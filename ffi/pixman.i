# 1 "pixman.h"
# 1 "<built-in>"
# 1 "<command line>"
# 1 "pixman.h"
# 90 "pixman.h"
# 1 "/usr/include/stdint.h" 1 3 4
# 26 "/usr/include/stdint.h" 3 4
# 1 "/usr/include/features.h" 1 3 4
# 295 "/usr/include/features.h" 3 4
# 1 "/usr/include/sys/cdefs.h" 1 3 4
# 296 "/usr/include/features.h" 2 3 4
# 318 "/usr/include/features.h" 3 4
# 1 "/usr/include/gnu/stubs.h" 1 3 4
# 319 "/usr/include/features.h" 2 3 4
# 27 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/bits/wchar.h" 1 3 4
# 28 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/bits/wordsize.h" 1 3 4
# 29 "/usr/include/stdint.h" 2 3 4
# 37 "/usr/include/stdint.h" 3 4
typedef signed char int8_t;
typedef short int int16_t;
typedef int int32_t;



__extension__
typedef long long int int64_t;




typedef unsigned char uint8_t;
typedef unsigned short int uint16_t;

typedef unsigned int uint32_t;





__extension__
typedef unsigned long long int uint64_t;






typedef signed char int_least8_t;
typedef short int int_least16_t;
typedef int int_least32_t;



__extension__
typedef long long int int_least64_t;



typedef unsigned char uint_least8_t;
typedef unsigned short int uint_least16_t;
typedef unsigned int uint_least32_t;



__extension__
typedef unsigned long long int uint_least64_t;






typedef signed char int_fast8_t;





typedef int int_fast16_t;
typedef int int_fast32_t;
__extension__
typedef long long int int_fast64_t;



typedef unsigned char uint_fast8_t;





typedef unsigned int uint_fast16_t;
typedef unsigned int uint_fast32_t;
__extension__
typedef unsigned long long int uint_fast64_t;
# 126 "/usr/include/stdint.h" 3 4
typedef int intptr_t;


typedef unsigned int uintptr_t;
# 138 "/usr/include/stdint.h" 3 4
__extension__
typedef long long int intmax_t;
__extension__
typedef unsigned long long int uintmax_t;
# 91 "pixman.h" 2
# 101 "pixman.h"
typedef struct pixman_region16 pixman_region16_t;

typedef struct pixman_box16 {
    short x1, y1, x2, y2;
} pixman_box16_t;

typedef enum {
    PIXMAN_REGION_STATUS_FAILURE,
    PIXMAN_REGION_STATUS_SUCCESS
} pixman_region_status_t;



pixman_region16_t *
pixman_region_create (void);

pixman_region16_t *
pixman_region_create_simple (pixman_box16_t *extents);

void
pixman_region_destroy (pixman_region16_t *region);



void
pixman_region_translate (pixman_region16_t *region, int x, int y);

pixman_region_status_t
pixman_region_copy (pixman_region16_t *dest, pixman_region16_t *source);

pixman_region_status_t
pixman_region_intersect (pixman_region16_t *newReg, pixman_region16_t *reg1, pixman_region16_t *reg2);

pixman_region_status_t
pixman_region_union (pixman_region16_t *newReg, pixman_region16_t *reg1, pixman_region16_t *reg2);

pixman_region_status_t
pixman_region_union_rect(pixman_region16_t *dest, pixman_region16_t *source,
                         int x, int y, unsigned int width, unsigned int height);

pixman_region_status_t
pixman_region_subtract (pixman_region16_t *regD, pixman_region16_t *regM, pixman_region16_t *regS);

pixman_region_status_t
pixman_region_inverse (pixman_region16_t *newReg, pixman_region16_t *reg1, pixman_box16_t *invRect);
# 155 "pixman.h"
int
pixman_region_num_rects (pixman_region16_t *region);

pixman_box16_t *
pixman_region_rects (pixman_region16_t *region);






int
pixman_region_contains_point (pixman_region16_t *region, int x, int y, pixman_box16_t *box);

int
pixman_region_contains_rectangle (pixman_region16_t *region, pixman_box16_t *prect);

int
pixman_region_not_empty (pixman_region16_t *region);

pixman_box16_t *
pixman_region_extents (pixman_region16_t *region);





pixman_region_status_t
pixman_region_append (pixman_region16_t *dest, pixman_region16_t *region);

pixman_region_status_t
pixman_region_validate (pixman_region16_t *badreg, int *pOverlap);





void
pixman_region_reset (pixman_region16_t *region, pixman_box16_t *pBox);

void
pixman_region_empty (pixman_region16_t *region);






typedef enum pixman_operator {
    PIXMAN_OPERATOR_CLEAR,
    PIXMAN_OPERATOR_SRC,
    PIXMAN_OPERATOR_DST,
    PIXMAN_OPERATOR_OVER,
    PIXMAN_OPERATOR_OVER_REVERSE,
    PIXMAN_OPERATOR_IN,
    PIXMAN_OPERATOR_IN_REVERSE,
    PIXMAN_OPERATOR_OUT,
    PIXMAN_OPERATOR_OUT_REVERSE,
    PIXMAN_OPERATOR_ATOP,
    PIXMAN_OPERATOR_ATOP_REVERSE,
    PIXMAN_OPERATOR_XOR,
    PIXMAN_OPERATOR_ADD,
    PIXMAN_OPERATOR_SATURATE
} pixman_operator_t;

typedef enum pixman_format_name {
    PIXMAN_FORMAT_NAME_ARGB32,
    PIXMAN_FORMAT_NAME_RGB24,
    PIXMAN_FORMAT_NAME_A8,
    PIXMAN_FORMAT_NAME_A1
} pixman_format_name_t;

typedef struct pixman_format pixman_format_t;

pixman_format_t *
pixman_format_create (pixman_format_name_t name);

pixman_format_t *
pixman_format_create_masks (int bpp,
                            int alpha_mask,
                            int red_mask,
                            int green_mask,
                            int blue_mask);

void
pixman_format_destroy (pixman_format_t *format);



typedef struct pixman_image pixman_image_t;

pixman_image_t *
pixman_image_create (pixman_format_t *format,
                     int width,
                     int height);
# 266 "pixman.h"
typedef uint32_t pixman_bits_t;



pixman_image_t *
pixman_image_create_for_data (pixman_bits_t *data,
                              pixman_format_t *format,
                              int width, int height,
                              int bpp, int stride);

void
pixman_image_destroy (pixman_image_t *image);

int
pixman_image_set_clip_region (pixman_image_t *image,
                              pixman_region16_t *region);

typedef int pixman_fixed16_16_t;

typedef struct pixman_point_fixed {
    pixman_fixed16_16_t x, y;
} pixman_point_fixed_t;

typedef struct pixman_line_fixed {
    pixman_point_fixed_t p1, p2;
} pixman_line_fixed_t;




typedef struct pixman_rectangle {
    short x, y;
    unsigned short width, height;
} pixman_rectangle_t;

typedef struct pixman_triangle {
    pixman_point_fixed_t p1, p2, p3;
} pixman_triangle_t;

typedef struct pixman_trapezoid {
    pixman_fixed16_16_t top, bottom;
    pixman_line_fixed_t left, right;
} pixman_trapezoid_t;

typedef struct pixman_vector {
    pixman_fixed16_16_t vector[3];
} pixman_vector_t;

typedef struct pixman_transform {
    pixman_fixed16_16_t matrix[3][3];
} pixman_transform_t;

typedef enum {
    PIXMAN_FILTER_FAST,
    PIXMAN_FILTER_GOOD,
    PIXMAN_FILTER_BEST,
    PIXMAN_FILTER_NEAREST,
    PIXMAN_FILTER_BILINEAR
} pixman_filter_t;

int
pixman_image_set_transform (pixman_image_t *image,
                            pixman_transform_t *transform);

void
pixman_image_set_repeat (pixman_image_t *image,
                         int repeat);

void
pixman_image_set_filter (pixman_image_t *image,
                         pixman_filter_t filter);

int
pixman_image_get_width (pixman_image_t *image);

int
pixman_image_get_height (pixman_image_t *image);

int
pixman_image_get_stride (pixman_image_t *image);

int
pixman_image_get_depth (pixman_image_t *image);

pixman_format_t *
pixman_image_get_format (pixman_image_t *image);

pixman_bits_t *
pixman_image_get_data (pixman_image_t *image);




typedef struct pixman_color {
    unsigned short red;
    unsigned short green;
    unsigned short blue;
    unsigned short alpha;
} pixman_color_t;

void
pixman_color_to_pixel (const pixman_format_t *format,
                       const pixman_color_t *color,
                       pixman_bits_t *pixel);

void
pixman_pixel_to_color (const pixman_format_t *format,
                       pixman_bits_t pixel,
                       pixman_color_t *color);



void
pixman_fill_rectangle (pixman_operator_t op,
                       pixman_image_t *dst,
                       const pixman_color_t *color,
                       int x,
                       int y,
                       unsigned int width,
                       unsigned int height);

void
pixman_fill_rectangles (pixman_operator_t op,
                        pixman_image_t *dst,
                        const pixman_color_t *color,
                        const pixman_rectangle_t *rects,
                        int nRects);



void
pixman_composite_trapezoids (pixman_operator_t op,
                             pixman_image_t *src,
                             pixman_image_t *dst,
                             int xSrc,
                             int ySrc,
                             const pixman_trapezoid_t *traps,
                             int ntrap);



void
pixman_composite_triangles (pixman_operator_t op,
                            pixman_image_t *src,
                            pixman_image_t *dst,
                            int xSrc,
                            int ySrc,
                            const pixman_triangle_t *tris,
                            int ntris);

void
pixman_composite_tri_strip (pixman_operator_t op,
                            pixman_image_t *src,
                            pixman_image_t *dst,
                            int xSrc,
                            int ySrc,
                            const pixman_point_fixed_t *points,
                            int npoints);


void
pixman_composite_tri_fan (pixman_operator_t op,
                          pixman_image_t *src,
                          pixman_image_t *dst,
                          int xSrc,
                          int ySrc,
                          const pixman_point_fixed_t *points,
                          int npoints);



void
pixman_composite (pixman_operator_t op,
                  pixman_image_t *iSrc,
                  pixman_image_t *iMask,
                  pixman_image_t *iDst,
                  int xSrc,
                  int ySrc,
                  int xMask,
                  int yMask,
                  int xDst,
                  int yDst,
                  int width,
                  int height);
