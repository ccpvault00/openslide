/*
 *  OpenSlide, a library for reading whole slide image files
 *
 *  Copyright (c) 2022-2023 Alexandr Virodov
 *  Copyright (c) 2026 Chia-Ping Chang
 *  All rights reserved.
 *
 *  OpenSlide is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Lesser General Public License as
 *  published by the Free Software Foundation, version 2.1.
 *
 *  OpenSlide is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 *  GNU Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with OpenSlide. If not, see
 *  <http://www.gnu.org/licenses/>.
 *
 */

/*
 * Philips iSyntax support, via libisyntax
 *
 * quickhash comes from the XML header at the start of the file
 *
 * File layout (Philips "iSyntax image format" document, 2020):
 *   XML header | EOT marker "\r\n\x04" | optional seektable | codeblocks
 * The XML header is a DataObject tree of named attributes: scanner and
 * DICOM-style metadata, one DataObject per scanned image (WSI, LABELIMAGE,
 * MACROIMAGE) with the label/macro JPEGs and the ICC profiles as base64
 * text, and for the WSI the codeblock header table.  The pixel data is a
 * wavelet pyramid (one scale per level) of 256x256 tiles, each stored as
 * entropy-coded LL/LH/HL/HH coefficient blocks for three colour channels
 * (YCoCg); a tile of one level is reconstructed from its own coefficients
 * plus the LL band produced while decoding its parent, so decoding a tile
 * needs its ancestors up to the top level.  Levels are padded by a few
 * pixels per level for the wavelet transform, so the tile grid is larger
 * than the image and shifted by a per-level origin offset.
 *
 * Division of labour:
 * - libisyntax opens the file by path, parses the header into its own
 *   structures, reads codeblocks, decodes and caches coefficients, and
 *   returns reconstructed tiles (opaque BGRA), the base64-decoded JPEG of
 *   the label and macro images, and the ICC profiles.
 * - OpenSlide detects the file by its root tag, reads the XML header once
 *   more through its VFS to publish every attribute as a philips.*
 *   property (large base64 blobs excluded) and to hash it for quickhash1,
 *   maps level coordinates onto libisyntax's padded grid, paints tiles
 *   through the simple grid with its own pixel cache, clips the padding to
 *   transparent, decodes the associated JPEGs lazily, and sets
 *   openslide.mpp-x/y and openslide.barcode from libisyntax's parsed
 *   values.
 *
 * Properties: philips.<ATTRIBUTE> for every attribute of the root object
 * and of the WSI image object; attributes that are arrays of DataObjects
 * become philips.<ATTRIBUTE>[<i>].<SUBATTRIBUTE>.  openslide.mpp-x/y from
 * the WSI pixel spacing, openslide.barcode from PIM_DP_UFS_BARCODE (base64
 * decoded).  openslide.objective-power is not set (see below).
 *
 * Known limitations:
 * - libisyntax opens the file by path and does its own I/O, so the OpenSlide
 *   VFS (_openslide_file) is only used for the XML header and the hash.
 * - libisyntax serialises tile decoding of one slide behind a mutex, so
 *   concurrent openslide_read_region() calls on one handle do not scale.
 * - libisyntax distinguishes I/O errors (mapped to G_FILE_ERROR, like
 *   OpenSlide's own short reads) from undecodable data
 *   (OPENSLIDE_ERROR_FAILED) but does not say which codeblock failed; its
 *   error-level log message is appended to the GError instead.
 * - Each handle keeps a libisyntax coefficient cache of ISYNTAX_CACHE_TILES
 *   tiles (about 290 KB each once decoded) in addition to OpenSlide's own
 *   pixel cache; the two are not interchangeable, since neighbouring and
 *   child tiles are decoded from the cached coefficients.
 * - openslide.objective-power is not set: the derivation description of
 *   iSyntax files carries no magnification, and OpenSlide does not derive
 *   it from the pixel spacing in other formats either.
 * - Pixel byte order on big-endian hosts is left to libisyntax.
 */

#include "openslide-private.h"
#include "openslide-decode-jpeg.h"
#include "openslide-decode-xml.h"

#include <glib.h>
#include <math.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

#include <libisyntax.h>

static const char XML_ROOT[] = "DataObject";
static const char XML_ROOT_TYPE_ATTR[] = "ObjectType";
static const char XML_ROOT_TYPE_VALUE[] = "DPUfsImport";
static const char XML_NAME_ATTR[] = "Name";
static const char XML_SCANNED_IMAGES_NAME[] = "PIM_DP_SCANNED_IMAGES";
static const char XML_ELEMENT_END[] = "</Attribute>";

// the detect signature must appear within this many bytes of the file start
static const char DETECT_SIGNATURE[] = "<DataObject ObjectType=\"DPUfsImport\">";
#define DETECT_LENGTH 256

// end of the XML header
static const char EOT_MARKER[] = "\r\n\x04";
#define EOT_MARKER_LENGTH 3
#define HEADER_READ_CHUNK (1 << 20)
// refuse to look for the EOT marker beyond this offset
#define HEADER_MAX_LENGTH (1 << 30)

// Attributes whose text is a large base64 blob.  They are removed from the
// header before XML parsing (libxml2 limits text nodes to 10 MB) and never
// become properties.
static const char * const BLOB_ATTRIBUTES[] = {
  "PIM_DP_IMAGE_DATA",            // label/macro JPEG
  "DICOM_ICCPROFILE",             // ICC profile
  "UFS_IMAGE_BLOCK_HEADER_TABLE", // codeblock seektable
  NULL,
};

static const char MAIN_IMAGE_XPATH[] =
  "/DataObject/Attribute[@Name='PIM_DP_SCANNED_IMAGES']/Array"
  "/DataObject[Attribute/@Name='PIM_DP_IMAGE_TYPE' and "
  "Attribute/text()='WSI']";

// libisyntax keeps the wavelet coefficients of this many tiles per slide
// (about 290 KB each, allocated as tiles are decoded).  A single
// openslide_read_region() paint (at most 4096x4096 pixels, 289 tiles plus
// ancestors) needs about 500; a warm handle serving random windows of a
// mid level of a 150000x90000 slide needs the whole level plus ancestors
// (about 1000), and 2000 makes that case as fast as pyisyntax, which uses
// the same number.
#define ISYNTAX_CACHE_TILES 2000

// libisyntax pads every level of the wavelet pyramid by this many pixels;
// see libisyntax_read_region() for the same computation
#define PER_LEVEL_PADDING 3

struct philips_isyntax_ops_data {
  isyntax_t *isyntax;
  isyntax_cache_t *cache;
};

// buffers returned by libisyntax come from the C allocator, not GLib's
static void libisyntax_free(void *buf) {
  free(buf);  // ci-allow
}

static const char *libisyntax_strerror(isyntax_error_t ret) {
  switch (ret) {
  case LIBISYNTAX_OK:
    return "no error";
  case LIBISYNTAX_FATAL:
    return "fatal error";
  case LIBISYNTAX_INVALID_ARGUMENT:
    return "invalid argument";
  case LIBISYNTAX_IO_ERROR:
    return "I/O error";
  default:
    return "unknown error";
  }
}

// libisyntax decodes on the calling thread, so the last error-level
// message it logged on this thread belongs to the call that is failing.
static GPrivate last_error = G_PRIVATE_INIT(g_free);

static void libisyntax_log(enum libisyntax_log_level_t level,
                           const char *message,
                           void *userdata G_GNUC_UNUSED) {
  switch (level) {
  case LIBISYNTAX_LOG_ERROR:
    g_private_replace(&last_error, g_strchomp(g_strdup(message)));
    break;
  case LIBISYNTAX_LOG_WARNING:
    if (_openslide_debug(OPENSLIDE_DEBUG_DECODING)) {
      g_autofree char *msg = g_strchomp(g_strdup(message));
      g_warning("libisyntax warning: %s", msg);
    }
    break;
  default:
    if (_openslide_debug(OPENSLIDE_DEBUG_DECODING)) {
      g_autofree char *msg = g_strchomp(g_strdup(message));
      g_debug("libisyntax: %s", msg);
    }
    break;
  }
}

// Short reads of a truncated file get the same domain as OpenSlide's own
// file errors; everything else is a format or decode error.
static void set_libisyntax_error(GError **err, isyntax_error_t ret,
                                 const char *fmt, ...) G_GNUC_PRINTF(3, 4);
static void set_libisyntax_error(GError **err, isyntax_error_t ret,
                                 const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  g_autofree char *msg = g_strdup_vprintf(fmt, ap);
  va_end(ap);
  g_autofree char *detail = g_strdup(g_private_get(&last_error));
  g_private_replace(&last_error, NULL);
  GQuark domain = ret == LIBISYNTAX_IO_ERROR ? G_FILE_ERROR : OPENSLIDE_ERROR;
  int code = ret == LIBISYNTAX_IO_ERROR ?
    (int) G_FILE_ERROR_IO : (int) OPENSLIDE_ERROR_FAILED;
  g_set_error(err, domain, code, "%s: libisyntax %s (%d)%s%s",
              msg, libisyntax_strerror(ret), ret,
              detail ? ": " : "", detail ? detail : "");
}

// libisyntax_init() is idempotent; the log callback is process-wide.
static bool init_libisyntax(GError **err) {
  static gsize state = 0;
  if (g_once_init_enter(&state)) {
    isyntax_error_t ret = libisyntax_init();
    if (ret == LIBISYNTAX_OK) {
      libisyntax_set_log_callback(libisyntax_log, NULL);
    }
    g_once_init_leave(&state, ret == LIBISYNTAX_OK ? 1 : 2);
  }
  if (state != 1) {
    g_set_error(err, OPENSLIDE_ERROR, OPENSLIDE_ERROR_FAILED,
                "Couldn't initialize libisyntax");
    return false;
  }
  return true;
}

struct level {
  struct _openslide_level base;
  struct _openslide_grid *grid;
  int32_t scale;
  // offset of the level origin within libisyntax's padded tile grid,
  // in level pixels
  int64_t origin_offset;
};

enum associated_image_kind {
  IMAGE_LABEL,
  IMAGE_MACRO,
};

struct associated_image {
  struct _openslide_associated_image base;
  isyntax_t *isyntax;
  enum associated_image_kind kind;
};

static void destroy_level(struct level *l) {
  _openslide_grid_destroy(l->grid);
  g_free(l);
}
OPENSLIDE_DEFINE_G_DESTROY_NOTIFY_WRAPPER(destroy_level)

static void destroy_ops_data(struct philips_isyntax_ops_data *data) {
  // the cache owns the coefficient allocators the slide's tiles live in,
  // so close the slide first
  if (data->isyntax) {
    libisyntax_close(data->isyntax);
  }
  if (data->cache) {
    libisyntax_cache_destroy(data->cache);
  }
  g_free(data);
}
typedef struct philips_isyntax_ops_data philips_isyntax_ops_data;
G_DEFINE_AUTOPTR_CLEANUP_FUNC(philips_isyntax_ops_data, destroy_ops_data)

static void destroy(openslide_t *osr) {
  struct philips_isyntax_ops_data *data = osr->data;
  destroy_ops_data(data);

  for (int32_t i = 0; i < osr->level_count; i++) {
    destroy_level((struct level *) osr->levels[i]);
  }
  g_free(osr->levels);
}

static bool read_tile(openslide_t *osr,
                      cairo_t *cr,
                      struct _openslide_level *level,
                      int64_t tile_col, int64_t tile_row,
                      void *arg G_GNUC_UNUSED,
                      GError **err) {
  struct philips_isyntax_ops_data *data = osr->data;
  struct level *l = (struct level *) level;

  // tile size
  int64_t tw = l->base.tile_w;
  int64_t th = l->base.tile_h;

  // The grid covers libisyntax's padded tile grid; only the part inside
  // the image is painted, the rest stays transparent like in other
  // formats.  Bounds of the image within this tile, in tile pixels:
  int64_t x0 = MAX(0, l->origin_offset - tile_col * tw);
  int64_t y0 = MAX(0, l->origin_offset - tile_row * th);
  int64_t x1 = MIN(tw, l->origin_offset + l->base.w - tile_col * tw);
  int64_t y1 = MIN(th, l->origin_offset + l->base.h - tile_row * th);
  if (x0 >= x1 || y0 >= y1) {
    // entirely outside the image
    return true;
  }

  // cache
  g_autoptr(_openslide_cache_entry) cache_entry = NULL;
  uint32_t *tiledata = _openslide_cache_get(osr->cache,
                                            level, tile_col, tile_row,
                                            &cache_entry);
  if (!tiledata) {
    // libisyntax writes opaque BGRA, which is CAIRO_FORMAT_ARGB32 on
    // little-endian hosts.  Tiles without data are returned as white.
    g_autofree uint32_t *buf = g_new(uint32_t, tw * th);
    isyntax_error_t ret = libisyntax_tile_read(data->isyntax, data->cache,
                                               l->scale, tile_col, tile_row,
                                               buf,
                                               LIBISYNTAX_PIXEL_FORMAT_BGRA);
    if (ret != LIBISYNTAX_OK) {
      set_libisyntax_error(err, ret,
                           "Couldn't read tile (%"PRId64", %"PRId64
                           ") of scale %d",
                           tile_col, tile_row, l->scale);
      return false;
    }

    // clear the padding outside the image
    if (x0 > 0 || y0 > 0 || x1 < tw || y1 < th) {
      for (int64_t y = 0; y < th; y++) {
        uint32_t *row = buf + y * tw;
        if (y < y0 || y >= y1) {
          memset(row, 0, tw * sizeof(*row));
        } else {
          memset(row, 0, x0 * sizeof(*row));
          memset(row + x1, 0, (tw - x1) * sizeof(*row));
        }
      }
    }

    // put it in the cache
    tiledata = g_steal_pointer(&buf);
    _openslide_cache_put(osr->cache, level, tile_col, tile_row,
                         tiledata, tw * th * 4,
                         &cache_entry);
  }

  // draw it
  g_autoptr(cairo_surface_t) surface =
    cairo_image_surface_create_for_data((unsigned char *) tiledata,
                                        CAIRO_FORMAT_ARGB32,
                                        tw, th, tw * 4);
  cairo_set_source_surface(cr, surface, 0, 0);
  // Tiles are opaque, so when they land on integer pixel positions OVER
  // gives the same result as OpenSlide's default SATURATE, and pixman has
  // a fast path for it (SATURATE costs about 8 ns per pixel).  Fractional
  // positions need SATURATE to blend the tile seams.
  cairo_matrix_t m;
  cairo_get_matrix(cr, &m);
  bool integral = m.x0 == floor(m.x0) && m.y0 == floor(m.y0);
  if (integral) {
    cairo_save(cr);
    cairo_set_operator(cr, CAIRO_OPERATOR_OVER);
  }
  cairo_paint(cr);
  if (integral) {
    cairo_restore(cr);
  }

  return true;
}

static bool paint_region(openslide_t *osr G_GNUC_UNUSED, cairo_t *cr,
                         int64_t x, int64_t y,
                         struct _openslide_level *level,
                         int32_t w, int32_t h,
                         GError **err) {
  struct level *l = (struct level *) level;

  // Level coordinates are offset within the padded tile grid; use the same
  // convention as libisyntax_read_region() so that results match pyisyntax.
  return _openslide_grid_paint_region(l->grid, cr, NULL,
                                      x / l->base.downsample + l->origin_offset,
                                      y / l->base.downsample + l->origin_offset,
                                      level, w, h,
                                      err);
}

static bool read_icc_profile_common(isyntax_t *isyntax,
                                    const isyntax_image_t *image,
                                    int64_t expected_size,
                                    void *dest,
                                    GError **err) {
  uint8_t *profile = NULL;
  uint32_t size = 0;
  isyntax_error_t ret = libisyntax_read_icc_profile(isyntax,
                                                    (isyntax_image_t *) image,
                                                    &profile, &size);
  if (ret != LIBISYNTAX_OK) {
    set_libisyntax_error(err, ret, "No ICC profile");
    return false;
  }
  bool ok = true;
  if (size != expected_size) {
    g_set_error(err, OPENSLIDE_ERROR, OPENSLIDE_ERROR_FAILED,
                "ICC profile size changed");
    ok = false;
  } else {
    memcpy(dest, profile, size);
  }
  // allocated by libisyntax
  libisyntax_free(profile);
  return ok;
}

// returns 0 if the image has no ICC profile
static int64_t get_icc_profile_size(isyntax_t *isyntax,
                                    const isyntax_image_t *image) {
  uint8_t *profile = NULL;
  uint32_t size = 0;
  if (libisyntax_read_icc_profile(isyntax, (isyntax_image_t *) image,
                                  &profile, &size) != LIBISYNTAX_OK) {
    return 0;
  }
  libisyntax_free(profile);
  return size;
}

static bool read_icc_profile(openslide_t *osr, void *dest, GError **err) {
  struct philips_isyntax_ops_data *data = osr->data;
  return read_icc_profile_common(data->isyntax,
                                 libisyntax_get_wsi_image(data->isyntax),
                                 osr->icc_profile_size, dest, err);
}

static const struct _openslide_ops philips_isyntax_ops = {
  .paint_region = paint_region,
  .read_icc_profile = read_icc_profile,
  .destroy = destroy,
};

static bool philips_isyntax_detect(const char *filename,
                                   struct _openslide_tifflike *tl,
                                   GError **err) {
  // reject TIFFs
  if (tl) {
    g_set_error(err, OPENSLIDE_ERROR, OPENSLIDE_ERROR_FAILED,
                "Is a TIFF file");
    return false;
  }

  g_autoptr(_openslide_file) f = _openslide_fopen(filename, err);
  if (f == NULL) {
    return false;
  }

  // The header is an XML document whose root element is at the very
  // start of the file; we can't parse a partial document, so look for the
  // root tag literally.
  char buf[DETECT_LENGTH + 1];
  size_t len = _openslide_fread(f, buf, DETECT_LENGTH, err);
  if (len == 0) {
    g_prefix_error(err, "Couldn't read file header: ");
    return false;
  }
  buf[len] = 0;
  if (!g_strstr_len(buf, len, DETECT_SIGNATURE)) {
    g_set_error(err, OPENSLIDE_ERROR, OPENSLIDE_ERROR_FAILED,
                "Not a Philips iSyntax file");
    return false;
  }

  return true;
}

// Read the XML header: everything before the EOT marker.  Returns a
// NUL-terminated buffer and its length (excluding the marker).
static char *read_xml_header(const char *filename,
                             int64_t *header_len,
                             GError **err) {
  g_autoptr(_openslide_file) f = _openslide_fopen(filename, err);
  if (f == NULL) {
    return NULL;
  }

  g_autoptr(GByteArray) buf = g_byte_array_new();
  while (true) {
    size_t old_len = buf->len;
    g_byte_array_set_size(buf, old_len + HEADER_READ_CHUNK);
    GError *tmp_err = NULL;
    size_t count = _openslide_fread(f, buf->data + old_len,
                                    HEADER_READ_CHUNK, &tmp_err);
    if (count == 0) {
      if (tmp_err) {
        g_propagate_error(err, tmp_err);
      } else {
        g_set_error(err, OPENSLIDE_ERROR, OPENSLIDE_ERROR_FAILED,
                    "Couldn't find end of XML header");
      }
      return NULL;
    }
    g_byte_array_set_size(buf, old_len + count);

    // the marker may straddle the previous chunk boundary
    size_t search_from = old_len > EOT_MARKER_LENGTH - 1 ?
                         old_len - (EOT_MARKER_LENGTH - 1) : 0;
    const char *eot = g_strstr_len((const char *) buf->data + search_from,
                                   buf->len - search_from, EOT_MARKER);
    if (eot) {
      *header_len = eot - (const char *) buf->data;
      g_byte_array_set_size(buf, *header_len);
      g_byte_array_append(buf, (const guint8 *) "", 1);
      return (char *) g_byte_array_free(g_steal_pointer(&buf), false);
    }
    if (buf->len > HEADER_MAX_LENGTH) {
      g_set_error(err, OPENSLIDE_ERROR, OPENSLIDE_ERROR_FAILED,
                  "XML header larger than %d bytes", HEADER_MAX_LENGTH);
      return NULL;
    }
  }
}

// Drop the text content of attributes holding large base64 blobs, in place.
// One linear pass per attribute name: spans to keep are copied forward
// through a write pointer, so a crafted header with many blob attributes
// cannot make this quadratic.
static void strip_blob_attributes(char *xml) {
  for (const char * const *name = BLOB_ATTRIBUTES; *name; name++) {
    g_autofree char *pattern = g_strdup_printf("Name=\"%s\"", *name);
    char *read = xml;
    char *write = xml;
    char *cur;
    while ((cur = strstr(read, pattern))) {
      char *content = strchr(cur, '>');
      if (!content) {
        break;
      }
      content++;
      char *end = strstr(content, XML_ELEMENT_END);
      if (!end) {
        break;
      }
      size_t keep = content - read;
      memmove(write, read, keep);
      write += keep;
      read = end;
    }
    memmove(write, read, strlen(read) + 1);
  }
}

static bool verify_main_image_count(xmlDoc *doc, GError **err) {
  g_autoptr(xmlXPathContext) ctx = _openslide_xml_xpath_create(doc);
  g_autoptr(xmlXPathObject) result =
    _openslide_xml_xpath_eval(ctx, MAIN_IMAGE_XPATH);
  int count = result ? result->nodesetval->nodeNr : 0;
  if (count != 1) {
    g_set_error(err, OPENSLIDE_ERROR, OPENSLIDE_ERROR_FAILED,
                "Expected one WSI image, found %d", count);
    return false;
  }
  return true;
}

static xmlDoc *parse_header(const char *filename,
                            int64_t *header_len,
                            GError **err) {
  g_autofree char *xml = read_xml_header(filename, header_len, err);
  if (!xml) {
    return NULL;
  }
  strip_blob_attributes(xml);

  xmlDoc *doc = _openslide_xml_parse(xml, err);
  if (!doc) {
    return NULL;
  }

  // check root tag name and type
  xmlNode *root = xmlDocGetRootElement(doc);
  g_autoptr(xmlChar) type = root ?
    xmlGetProp(root, BAD_CAST XML_ROOT_TYPE_ATTR) : NULL;
  if (!root || xmlStrcmp(root->name, BAD_CAST XML_ROOT) ||
      !type || xmlStrcmp(type, BAD_CAST XML_ROOT_TYPE_VALUE)) {
    g_set_error(err, OPENSLIDE_ERROR, OPENSLIDE_ERROR_FAILED,
                "Root tag not <%s %s=\"%s\">",
                XML_ROOT, XML_ROOT_TYPE_ATTR, XML_ROOT_TYPE_VALUE);
    xmlFreeDoc(doc);
    return NULL;
  }

  return doc;
}

static bool is_blob_attribute(const xmlChar *name) {
  for (const char * const *blob = BLOB_ATTRIBUTES; *blob; blob++) {
    if (!xmlStrcmp(name, BAD_CAST *blob)) {
      return true;
    }
  }
  return false;
}

static void add_properties(openslide_t *osr,
                           xmlXPathContext *ctx,
                           const char *prefix,
                           const char *xpath);

static void add_properties_from_array(openslide_t *osr,
                                      xmlXPathContext *ctx,
                                      const char *prefix,
                                      xmlNode *node) {
  g_autoptr(xmlChar) name = xmlGetProp(node, BAD_CAST XML_NAME_ATTR);
  ctx->node = node;
  g_autoptr(xmlXPathObject) result =
    _openslide_xml_xpath_eval(ctx, "Array/DataObject");
  for (int i = 0; result && i < result->nodesetval->nodeNr; i++) {
    ctx->node = result->nodesetval->nodeTab[i];
    g_autofree char *sub_prefix = g_strdup_printf("%s.%s[%d]", prefix, name, i);
    add_properties(osr, ctx, sub_prefix, "Attribute");
  }
}

// Dump every attribute as a property, uninterpreted.  Arrays of DataObjects
// are recursed into with an index, except the scanned-image array, where
// only the WSI image is used (the label and macro images carry nothing but
// their pixel data).
static void add_properties(openslide_t *osr,
                           xmlXPathContext *ctx,
                           const char *prefix,
                           const char *xpath) {
  g_autoptr(xmlXPathObject) result = _openslide_xml_xpath_eval(ctx, xpath);
  for (int i = 0; result && i < result->nodesetval->nodeNr; i++) {
    xmlNode *node = result->nodesetval->nodeTab[i];
    g_autoptr(xmlChar) name = xmlGetProp(node, BAD_CAST XML_NAME_ATTR);
    if (!name || is_blob_attribute(name)) {
      continue;
    }

    if (!xmlStrcmp(name, BAD_CAST XML_SCANNED_IMAGES_NAME)) {
      ctx->node = node;
      add_properties(osr, ctx, prefix,
                     "Array/DataObject[Attribute/@Name='PIM_DP_IMAGE_TYPE' "
                     "and Attribute/text()='WSI'][1]/Attribute");
    } else if (xmlFirstElementChild(node)) {
      add_properties_from_array(osr, ctx, prefix, node);
    } else {
      g_autoptr(xmlChar) value = xmlNodeGetContent(node);
      if (value) {
        g_hash_table_insert(osr->properties,
                            g_strdup_printf("%s.%s", prefix, (char *) name),
                            g_strdup((char *) value));
      }
    }
  }
}

static uint32_t parse_objective_power(const char *derivation) {
  // e.g. "PHILIPS UFS V1.6.5641 | Quality=1 | DWT=1 | Compressor=16 |
  //       levels=20,2.0,1.0 | ..."; the first "levels" entry is the
  //       objective power.  Same heuristic as the Philips TIFF driver.
  g_auto(GStrv) items = g_strsplit(derivation, "|", 0);
  for (int i = 0; items[i]; i++) {
    g_auto(GStrv) kv = g_strsplit(g_strstrip(items[i]), "=", 2);
    if (g_str_equal(kv[0], "levels") && kv[1]) {
      g_auto(GStrv) levels = g_strsplit(kv[1], ",", 0);
      uint64_t first_level;
      if (levels[0] &&
          _openslide_parse_uint64(levels[0], &first_level, 10) &&
          first_level && first_level <= 200) {
        return first_level;
      }
      break;
    }
  }
  return 0;
}

static void add_openslide_properties(openslide_t *osr, isyntax_t *isyntax) {
  if (libisyntax_get_is_mpp_known(isyntax)) {
    g_hash_table_insert(osr->properties,
                        g_strdup(OPENSLIDE_PROPERTY_NAME_MPP_X),
                        _openslide_format_double(libisyntax_get_mpp_x(isyntax)));
    g_hash_table_insert(osr->properties,
                        g_strdup(OPENSLIDE_PROPERTY_NAME_MPP_Y),
                        _openslide_format_double(libisyntax_get_mpp_y(isyntax)));
  }

  const char *derivation =
    g_hash_table_lookup(osr->properties,
                        "philips.DICOM_DERIVATION_DESCRIPTION");
  if (derivation) {
    uint32_t objective_power = parse_objective_power(derivation);
    if (objective_power) {
      g_hash_table_insert(osr->properties,
                          g_strdup(OPENSLIDE_PROPERTY_NAME_OBJECTIVE_POWER),
                          g_strdup_printf("%u", objective_power));
    }
  }

  const char *barcode = libisyntax_get_barcode(isyntax);
  if (barcode && *barcode) {
    g_hash_table_insert(osr->properties,
                        g_strdup(OPENSLIDE_PROPERTY_NAME_BARCODE),
                        g_strdup(barcode));
  }
}

// Returns the base64-decoded JPEG of a label or macro image.  The buffer
// is allocated by libisyntax and must be released with libisyntax_free().
static bool read_associated_jpeg(isyntax_t *isyntax,
                                 enum associated_image_kind kind,
                                 uint8_t **jpeg, uint32_t *len,
                                 GError **err) {
  isyntax_error_t ret;
  switch (kind) {
  case IMAGE_LABEL:
    ret = libisyntax_read_label_image_jpeg(isyntax, jpeg, len);
    break;
  case IMAGE_MACRO:
    ret = libisyntax_read_macro_image_jpeg(isyntax, jpeg, len);
    break;
  default:
    g_assert_not_reached();
  }
  if (ret != LIBISYNTAX_OK) {
    set_libisyntax_error(err, ret, "Couldn't read associated image");
    return false;
  }
  return true;
}

static bool get_associated_image_data(struct _openslide_associated_image *_img,
                                      uint32_t *dest,
                                      GError **err) {
  struct associated_image *img = (struct associated_image *) _img;

  uint8_t *jpeg;
  uint32_t len;
  if (!read_associated_jpeg(img->isyntax, img->kind, &jpeg, &len, err)) {
    return false;
  }
  bool ok = _openslide_jpeg_decode_buffer(jpeg, len, dest,
                                          img->base.w, img->base.h, err);
  libisyntax_free(jpeg);
  return ok;
}

static bool associated_read_icc_profile(struct _openslide_associated_image *_img,
                                        void *dest, GError **err) {
  struct associated_image *img = (struct associated_image *) _img;
  const isyntax_image_t *image = img->kind == IMAGE_LABEL ?
    libisyntax_get_label_image(img->isyntax) :
    libisyntax_get_macro_image(img->isyntax);
  return read_icc_profile_common(img->isyntax, image,
                                 img->base.icc_profile_size, dest, err);
}

static void destroy_associated_image(struct _openslide_associated_image *_img) {
  struct associated_image *img = (struct associated_image *) _img;
  g_free(img);
}

static const struct _openslide_associated_image_ops philips_isyntax_associated_ops = {
  .get_argb_data = get_associated_image_data,
  .read_icc_profile = associated_read_icc_profile,
  .destroy = destroy_associated_image,
};

// Only the JPEG header is parsed here; the image is decoded on demand.
static bool add_associated_image(openslide_t *osr,
                                 isyntax_t *isyntax,
                                 const char *name,
                                 enum associated_image_kind kind,
                                 GError **err) {
  uint8_t *jpeg;
  uint32_t len;
  if (!read_associated_jpeg(isyntax, kind, &jpeg, &len, err)) {
    return false;
  }
  int32_t w, h;
  bool ok = _openslide_jpeg_decode_buffer_dimensions(jpeg, len, &w, &h, err);
  libisyntax_free(jpeg);
  if (!ok) {
    g_prefix_error(err, "Can't decode %s associated image: ", name);
    return false;
  }

  struct associated_image *img = g_new0(struct associated_image, 1);
  img->base.ops = &philips_isyntax_associated_ops;
  img->base.w = w;
  img->base.h = h;
  img->base.icc_profile_size =
    get_icc_profile_size(isyntax,
                         kind == IMAGE_LABEL ?
                         libisyntax_get_label_image(isyntax) :
                         libisyntax_get_macro_image(isyntax));
  img->isyntax = isyntax;
  img->kind = kind;

  g_hash_table_insert(osr->associated_images, g_strdup(name), img);
  return true;
}

static bool philips_isyntax_open(openslide_t *osr,
                                 const char *filename,
                                 struct _openslide_tifflike *tl G_GNUC_UNUSED,
                                 struct _openslide_hash *quickhash1,
                                 GError **err) {
  // parse the XML header
  int64_t header_len;
  g_autoptr(xmlDoc) doc = parse_header(filename, &header_len, err);
  if (!doc) {
    return false;
  }

  // libisyntax exposes exactly one pyramid, so refuse anything else
  if (!verify_main_image_count(doc, err)) {
    return false;
  }

  // open with libisyntax; init starts the library's worker thread pool on
  // first use
  g_autoptr(philips_isyntax_ops_data) data =
    g_new0(struct philips_isyntax_ops_data, 1);
  if (!init_libisyntax(err)) {
    return false;
  }
  isyntax_error_t ret = libisyntax_open(filename,
                                        (enum libisyntax_open_flags_t) 0,
                                        &data->isyntax);
  if (ret != LIBISYNTAX_OK) {
    set_libisyntax_error(err, ret, "libisyntax couldn't open the slide");
    return false;
  }

  // the coefficient cache is per slide; libisyntax serialises decoding
  // behind its mutex anyway
  ret = libisyntax_cache_create("openslide", ISYNTAX_CACHE_TILES,
                                &data->cache);
  if (ret != LIBISYNTAX_OK) {
    set_libisyntax_error(err, ret, "Couldn't create libisyntax cache");
    return false;
  }
  ret = libisyntax_cache_inject(data->cache, data->isyntax);
  if (ret != LIBISYNTAX_OK) {
    set_libisyntax_error(err, ret, "Couldn't attach libisyntax cache");
    return false;
  }

  // create levels
  const isyntax_image_t *wsi = libisyntax_get_wsi_image(data->isyntax);
  int32_t level_count = libisyntax_image_get_level_count(wsi);
  if (level_count < 1) {
    g_set_error(err, OPENSLIDE_ERROR, OPENSLIDE_ERROR_FAILED,
                "Slide has no pyramid levels");
    return false;
  }
  int32_t tile_w = libisyntax_get_tile_width(data->isyntax);
  int32_t tile_h = libisyntax_get_tile_height(data->isyntax);
  g_autoptr(GPtrArray) level_array =
    g_ptr_array_new_with_free_func(OPENSLIDE_G_DESTROY_NOTIFY_WRAPPER(destroy_level));
  for (int32_t i = 0; i < level_count; i++) {
    const isyntax_level_t *isyntax_level = libisyntax_image_get_level(wsi, i);
    struct level *l = g_new0(struct level, 1);
    g_ptr_array_add(level_array, l);

    l->scale = libisyntax_level_get_scale(isyntax_level);
    l->base.downsample =
      libisyntax_level_get_downsample_factor(isyntax_level);
    // dimensions without the wavelet padding
    l->base.w = libisyntax_level_get_width(isyntax_level);
    l->base.h = libisyntax_level_get_height(isyntax_level);
    l->base.tile_w = tile_w;
    l->base.tile_h = tile_h;
    l->origin_offset =
      ((PER_LEVEL_PADDING << level_count) - PER_LEVEL_PADDING) >> l->scale;
    // the grid covers the padded tile grid
    l->grid =
      _openslide_grid_create_simple(osr,
                                    libisyntax_level_get_width_in_tiles(isyntax_level),
                                    libisyntax_level_get_height_in_tiles(isyntax_level),
                                    tile_w, tile_h,
                                    read_tile);

    if (l->base.w <= 0 || l->base.h <= 0 || l->base.downsample <= 0) {
      g_set_error(err, OPENSLIDE_ERROR, OPENSLIDE_ERROR_FAILED,
                  "Invalid geometry for level %d", i);
      return false;
    }
  }

  // quickhash1: the XML header identifies the slide (UIDs, acquisition
  // time, barcode, embedded macro image) and is cheap to read
  if (!_openslide_hash_file_part(quickhash1, filename, 0, header_len, err)) {
    return false;
  }

  // properties
  g_autoptr(xmlXPathContext) ctx = _openslide_xml_xpath_create(doc);
  add_properties(osr, ctx, "philips", "/DataObject/Attribute");
  add_openslide_properties(osr, data->isyntax);

  // ICC profile of the main image
  osr->icc_profile_size = get_icc_profile_size(data->isyntax, wsi);

  // associated images; errors are non-fatal
  add_associated_image(osr, data->isyntax, "label", IMAGE_LABEL, NULL);
  add_associated_image(osr, data->isyntax, "macro", IMAGE_MACRO, NULL);

  // store osr data
  g_assert(osr->data == NULL);
  g_assert(osr->levels == NULL);
  osr->level_count = level_array->len;
  osr->levels = (struct _openslide_level **)
    g_ptr_array_free(g_steal_pointer(&level_array), false);
  osr->data = g_steal_pointer(&data);
  osr->ops = &philips_isyntax_ops;

  return true;
}

const struct _openslide_format _openslide_format_philips_isyntax = {
  .name = "philips-isyntax",
  .vendor = "philips",
  .detect = philips_isyntax_detect,
  .open = philips_isyntax_open,
};
