# 1 "cairo.h"
# 1 "<built-in>"
# 1 "<command line>"
# 1 "cairo.h"
# 31 "cairo.h"
# 1 "/usr/include/cairo-features.h" 1 3 4
# 32 "cairo.h" 2

# 1 "/usr/include/pixman.h" 1 3 4
# 90 "/usr/include/pixman.h" 3 4
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




typedef long long int int64_t;




typedef unsigned char uint8_t;
typedef unsigned short int uint16_t;

typedef unsigned int uint32_t;






typedef unsigned long long int uint64_t;






typedef signed char int_least8_t;
typedef short int int_least16_t;
typedef int int_least32_t;




typedef long long int int_least64_t;



typedef unsigned char uint_least8_t;
typedef unsigned short int uint_least16_t;
typedef unsigned int uint_least32_t;




typedef unsigned long long int uint_least64_t;






typedef signed char int_fast8_t;





typedef int int_fast16_t;
typedef int int_fast32_t;

typedef long long int int_fast64_t;



typedef unsigned char uint_fast8_t;





typedef unsigned int uint_fast16_t;
typedef unsigned int uint_fast32_t;

typedef unsigned long long int uint_fast64_t;
# 126 "/usr/include/stdint.h" 3 4
typedef int intptr_t;


typedef unsigned int uintptr_t;
# 138 "/usr/include/stdint.h" 3 4

typedef long long int intmax_t;

typedef unsigned long long int uintmax_t;
# 91 "/usr/include/pixman.h" 2 3 4
# 101 "/usr/include/pixman.h" 3 4
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
# 155 "/usr/include/pixman.h" 3 4
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
# 266 "/usr/include/pixman.h" 3 4
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
# 34 "cairo.h" 2
# 1 "/usr/include/stdio.h" 1 3 4
# 30 "/usr/include/stdio.h" 3 4




# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 1 3 4
# 213 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 3 4
typedef unsigned int size_t;
# 35 "/usr/include/stdio.h" 2 3 4

# 1 "/usr/include/bits/types.h" 1 3 4
# 28 "/usr/include/bits/types.h" 3 4
# 1 "/usr/include/bits/wordsize.h" 1 3 4
# 29 "/usr/include/bits/types.h" 2 3 4


# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 1 3 4
# 32 "/usr/include/bits/types.h" 2 3 4


typedef unsigned char __u_char;
typedef unsigned short int __u_short;
typedef unsigned int __u_int;
typedef unsigned long int __u_long;


typedef signed char __int8_t;
typedef unsigned char __uint8_t;
typedef signed short int __int16_t;
typedef unsigned short int __uint16_t;
typedef signed int __int32_t;
typedef unsigned int __uint32_t;
# 62 "/usr/include/bits/types.h" 3 4
typedef struct
{
  long __val[2];
} __quad_t;
typedef struct
{
  __u_long __val[2];
} __u_quad_t;
# 129 "/usr/include/bits/types.h" 3 4
# 1 "/usr/include/bits/typesizes.h" 1 3 4
# 130 "/usr/include/bits/types.h" 2 3 4






 typedef unsigned long long int __dev_t;
 typedef unsigned int __uid_t;
 typedef unsigned int __gid_t;
 typedef unsigned long int __ino_t;
 typedef unsigned long long int __ino64_t;
 typedef unsigned int __mode_t;
 typedef unsigned int __nlink_t;
 typedef long int __off_t;
 typedef long long int __off64_t;
 typedef int __pid_t;
 typedef struct { int __val[2]; } __fsid_t;
 typedef long int __clock_t;
 typedef unsigned long int __rlim_t;
 typedef unsigned long long int __rlim64_t;
 typedef unsigned int __id_t;
 typedef long int __time_t;
 typedef unsigned int __useconds_t;
 typedef long int __suseconds_t;

 typedef int __daddr_t;
 typedef long int __swblk_t;
 typedef int __key_t;


 typedef int __clockid_t;


 typedef int __timer_t;


 typedef long int __blksize_t;




 typedef long int __blkcnt_t;
 typedef long long int __blkcnt64_t;


 typedef unsigned long int __fsblkcnt_t;
 typedef unsigned long long int __fsblkcnt64_t;


 typedef unsigned long int __fsfilcnt_t;
 typedef unsigned long long int __fsfilcnt64_t;

 typedef int __ssize_t;



typedef __off64_t __loff_t;
typedef __quad_t *__qaddr_t;
typedef char *__caddr_t;


 typedef int __intptr_t;


 typedef unsigned int __socklen_t;
# 37 "/usr/include/stdio.h" 2 3 4









typedef struct _IO_FILE FILE;





# 62 "/usr/include/stdio.h" 3 4
typedef struct _IO_FILE __FILE;
# 72 "/usr/include/stdio.h" 3 4
# 1 "/usr/include/libio.h" 1 3 4
# 32 "/usr/include/libio.h" 3 4
# 1 "/usr/include/_G_config.h" 1 3 4
# 14 "/usr/include/_G_config.h" 3 4
# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 1 3 4
# 325 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 3 4
typedef long int wchar_t;
# 354 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 3 4
typedef unsigned int wint_t;
# 15 "/usr/include/_G_config.h" 2 3 4
# 24 "/usr/include/_G_config.h" 3 4
# 1 "/usr/include/wchar.h" 1 3 4
# 48 "/usr/include/wchar.h" 3 4
# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 1 3 4
# 49 "/usr/include/wchar.h" 2 3 4
# 76 "/usr/include/wchar.h" 3 4
typedef struct
{
  int __count;
  union
  {
    wint_t __wch;
    char __wchb[4];
  } __value;
} __mbstate_t;
# 25 "/usr/include/_G_config.h" 2 3 4

typedef struct
{
  __off_t __pos;
  __mbstate_t __state;
} _G_fpos_t;
typedef struct
{
  __off64_t __pos;
  __mbstate_t __state;
} _G_fpos64_t;
# 44 "/usr/include/_G_config.h" 3 4
# 1 "/usr/include/gconv.h" 1 3 4
# 28 "/usr/include/gconv.h" 3 4
# 1 "/usr/include/wchar.h" 1 3 4
# 48 "/usr/include/wchar.h" 3 4
# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 1 3 4
# 49 "/usr/include/wchar.h" 2 3 4
# 29 "/usr/include/gconv.h" 2 3 4


# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 1 3 4
# 32 "/usr/include/gconv.h" 2 3 4





enum
{
  __GCONV_OK = 0,
  __GCONV_NOCONV,
  __GCONV_NODB,
  __GCONV_NOMEM,

  __GCONV_EMPTY_INPUT,
  __GCONV_FULL_OUTPUT,
  __GCONV_ILLEGAL_INPUT,
  __GCONV_INCOMPLETE_INPUT,

  __GCONV_ILLEGAL_DESCRIPTOR,
  __GCONV_INTERNAL_ERROR
};



enum
{
  __GCONV_IS_LAST = 0x0001,
  __GCONV_IGNORE_ERRORS = 0x0002
};



struct __gconv_step;
struct __gconv_step_data;
struct __gconv_loaded_object;
struct __gconv_trans_data;



typedef int (*__gconv_fct) (struct __gconv_step *, struct __gconv_step_data *,
                            const unsigned char **, const unsigned char *,
                            unsigned char **, size_t *, int, int);


typedef wint_t (*__gconv_btowc_fct) (struct __gconv_step *, unsigned char);


typedef int (*__gconv_init_fct) (struct __gconv_step *);
typedef void (*__gconv_end_fct) (struct __gconv_step *);



typedef int (*__gconv_trans_fct) (struct __gconv_step *,
                                  struct __gconv_step_data *, void *,
                                  const unsigned char *,
                                  const unsigned char **,
                                  const unsigned char *, unsigned char **,
                                  size_t *);


typedef int (*__gconv_trans_context_fct) (void *, const unsigned char *,
                                          const unsigned char *,
                                          unsigned char *, unsigned char *);


typedef int (*__gconv_trans_query_fct) (const char *, const char ***,
                                        size_t *);


typedef int (*__gconv_trans_init_fct) (void **, const char *);
typedef void (*__gconv_trans_end_fct) (void *);

struct __gconv_trans_data
{

  __gconv_trans_fct __trans_fct;
  __gconv_trans_context_fct __trans_context_fct;
  __gconv_trans_end_fct __trans_end_fct;
  void *__data;
  struct __gconv_trans_data *__next;
};



struct __gconv_step
{
  struct __gconv_loaded_object *__shlib_handle;
  const char *__modname;

  int __counter;

  char *__from_name;
  char *__to_name;

  __gconv_fct __fct;
  __gconv_btowc_fct __btowc_fct;
  __gconv_init_fct __init_fct;
  __gconv_end_fct __end_fct;



  int __min_needed_from;
  int __max_needed_from;
  int __min_needed_to;
  int __max_needed_to;


  int __stateful;

  void *__data;
};



struct __gconv_step_data
{
  unsigned char *__outbuf;
  unsigned char *__outbufend;



  int __flags;



  int __invocation_counter;



  int __internal_use;

  __mbstate_t *__statep;
  __mbstate_t __state;



  struct __gconv_trans_data *__trans;
};



typedef struct __gconv_info
{
  size_t __nsteps;
  struct __gconv_step *__steps;
  struct __gconv_step_data __data [1];
} *__gconv_t;
# 45 "/usr/include/_G_config.h" 2 3 4
typedef union
{
  struct __gconv_info __cd;
  struct
  {
    struct __gconv_info __cd;
    struct __gconv_step_data __data;
  } __combined;
} _G_iconv_t;

typedef int _G_int16_t ;
typedef int _G_int32_t ;
typedef unsigned int _G_uint16_t ;
typedef unsigned int _G_uint32_t ;
# 33 "/usr/include/libio.h" 2 3 4
# 53 "/usr/include/libio.h" 3 4
# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stdarg.h" 1 3 4
# 43 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stdarg.h" 3 4
typedef __builtin_va_list __gnuc_va_list;
# 54 "/usr/include/libio.h" 2 3 4
# 163 "/usr/include/libio.h" 3 4
struct _IO_jump_t; struct _IO_FILE;
# 173 "/usr/include/libio.h" 3 4
typedef void _IO_lock_t;





struct _IO_marker {
  struct _IO_marker *_next;
  struct _IO_FILE *_sbuf;



  int _pos;
# 196 "/usr/include/libio.h" 3 4
};


enum __codecvt_result
{
  __codecvt_ok,
  __codecvt_partial,
  __codecvt_error,
  __codecvt_noconv
};
# 264 "/usr/include/libio.h" 3 4
struct _IO_FILE {
  int _flags;




  char* _IO_read_ptr;
  char* _IO_read_end;
  char* _IO_read_base;
  char* _IO_write_base;
  char* _IO_write_ptr;
  char* _IO_write_end;
  char* _IO_buf_base;
  char* _IO_buf_end;

  char *_IO_save_base;
  char *_IO_backup_base;
  char *_IO_save_end;

  struct _IO_marker *_markers;

  struct _IO_FILE *_chain;

  int _fileno;



  int _flags2;

  __off_t _old_offset;



  unsigned short _cur_column;
  signed char _vtable_offset;
  char _shortbuf[1];



  _IO_lock_t *_lock;
# 312 "/usr/include/libio.h" 3 4
  __off64_t _offset;





  void *__pad1;
  void *__pad2;

  int _mode;

  char _unused2[15 * sizeof (int) - 2 * sizeof (void *)];

};


typedef struct _IO_FILE _IO_FILE;


struct _IO_FILE_plus;

extern struct _IO_FILE_plus _IO_2_1_stdin_;
extern struct _IO_FILE_plus _IO_2_1_stdout_;
extern struct _IO_FILE_plus _IO_2_1_stderr_;
# 351 "/usr/include/libio.h" 3 4
typedef __ssize_t __io_read_fn (void *__cookie, char *__buf, size_t __nbytes);







typedef __ssize_t __io_write_fn (void *__cookie, const char *__buf,
                                 size_t __n);







typedef int __io_seek_fn (void *__cookie, __off64_t *__pos, int __w);


typedef int __io_close_fn (void *__cookie);
# 403 "/usr/include/libio.h" 3 4
extern int __underflow (_IO_FILE *) ;
extern int __uflow (_IO_FILE *) ;
extern int __overflow (_IO_FILE *, int) ;
extern wint_t __wunderflow (_IO_FILE *) ;
extern wint_t __wuflow (_IO_FILE *) ;
extern wint_t __woverflow (_IO_FILE *, wint_t) ;
# 441 "/usr/include/libio.h" 3 4
extern int _IO_getc (_IO_FILE *__fp) ;
extern int _IO_putc (int __c, _IO_FILE *__fp) ;
extern int _IO_feof (_IO_FILE *__fp) ;
extern int _IO_ferror (_IO_FILE *__fp) ;

extern int _IO_peekc_locked (_IO_FILE *__fp) ;





extern void _IO_flockfile (_IO_FILE *) ;
extern void _IO_funlockfile (_IO_FILE *) ;
extern int _IO_ftrylockfile (_IO_FILE *) ;
# 471 "/usr/include/libio.h" 3 4
extern int _IO_vfscanf (_IO_FILE * , const char * ,
                        __gnuc_va_list, int *) ;
extern int _IO_vfprintf (_IO_FILE *, const char *,
                         __gnuc_va_list) ;
extern __ssize_t _IO_padn (_IO_FILE *, int, __ssize_t) ;
extern size_t _IO_sgetn (_IO_FILE *, void *, size_t) ;

extern __off64_t _IO_seekoff (_IO_FILE *, __off64_t, int, int) ;
extern __off64_t _IO_seekpos (_IO_FILE *, __off64_t, int) ;

extern void _IO_free_backup_area (_IO_FILE *) ;
# 73 "/usr/include/stdio.h" 2 3 4
# 86 "/usr/include/stdio.h" 3 4


typedef _G_fpos_t fpos_t;




# 138 "/usr/include/stdio.h" 3 4
# 1 "/usr/include/bits/stdio_lim.h" 1 3 4
# 139 "/usr/include/stdio.h" 2 3 4



extern struct _IO_FILE *stdin;
extern struct _IO_FILE *stdout;
extern struct _IO_FILE *stderr;









extern int remove (const char *__filename) ;

extern int rename (const char *__old, const char *__new) ;









extern FILE *tmpfile (void);
# 180 "/usr/include/stdio.h" 3 4
extern char *tmpnam (char *__s) ;





extern char *tmpnam_r (char *__s) ;
# 198 "/usr/include/stdio.h" 3 4
extern char *tempnam (const char *__dir, const char *__pfx)
     ;








extern int fclose (FILE *__stream);




extern int fflush (FILE *__stream);

# 223 "/usr/include/stdio.h" 3 4
extern int fflush_unlocked (FILE *__stream);
# 237 "/usr/include/stdio.h" 3 4






extern FILE *fopen (const char * __filename,
                    const char * __modes);




extern FILE *freopen (const char * __filename,
                      const char * __modes,
                      FILE * __stream);
# 264 "/usr/include/stdio.h" 3 4

# 275 "/usr/include/stdio.h" 3 4
extern FILE *fdopen (int __fd, const char *__modes) ;
# 296 "/usr/include/stdio.h" 3 4



extern void setbuf (FILE * __stream, char * __buf) ;



extern int setvbuf (FILE * __stream, char * __buf,
                    int __modes, size_t __n) ;





extern void setbuffer (FILE * __stream, char * __buf,
                       size_t __size) ;


extern void setlinebuf (FILE *__stream) ;








extern int fprintf (FILE * __stream,
                    const char * __format, ...);




extern int printf (const char * __format, ...);

extern int sprintf (char * __s,
                    const char * __format, ...) ;





extern int vfprintf (FILE * __s, const char * __format,
                     __gnuc_va_list __arg);




extern int vprintf (const char * __format, __gnuc_va_list __arg);

extern int vsprintf (char * __s, const char * __format,
                     __gnuc_va_list __arg) ;





extern int snprintf (char * __s, size_t __maxlen,
                     const char * __format, ...)
     ;

extern int vsnprintf (char * __s, size_t __maxlen,
                      const char * __format, __gnuc_va_list __arg)
     ;

# 390 "/usr/include/stdio.h" 3 4





extern int fscanf (FILE * __stream,
                   const char * __format, ...);




extern int scanf (const char * __format, ...);

extern int sscanf (const char * __s,
                   const char * __format, ...) ;

# 432 "/usr/include/stdio.h" 3 4





extern int fgetc (FILE *__stream);
extern int getc (FILE *__stream);





extern int getchar (void);

# 456 "/usr/include/stdio.h" 3 4
extern int getc_unlocked (FILE *__stream);
extern int getchar_unlocked (void);
# 467 "/usr/include/stdio.h" 3 4
extern int fgetc_unlocked (FILE *__stream);











extern int fputc (int __c, FILE *__stream);
extern int putc (int __c, FILE *__stream);





extern int putchar (int __c);

# 500 "/usr/include/stdio.h" 3 4
extern int fputc_unlocked (int __c, FILE *__stream);







extern int putc_unlocked (int __c, FILE *__stream);
extern int putchar_unlocked (int __c);






extern int getw (FILE *__stream);


extern int putw (int __w, FILE *__stream);








extern char *fgets (char * __s, int __n, FILE * __stream);






extern char *gets (char *__s);

# 580 "/usr/include/stdio.h" 3 4





extern int fputs (const char * __s, FILE * __stream);





extern int puts (const char *__s);






extern int ungetc (int __c, FILE *__stream);






extern size_t fread (void * __ptr, size_t __size,
                     size_t __n, FILE * __stream);




extern size_t fwrite (const void * __ptr, size_t __size,
                      size_t __n, FILE * __s);

# 633 "/usr/include/stdio.h" 3 4
extern size_t fread_unlocked (void * __ptr, size_t __size,
                              size_t __n, FILE * __stream);
extern size_t fwrite_unlocked (const void * __ptr, size_t __size,
                               size_t __n, FILE * __stream);








extern int fseek (FILE *__stream, long int __off, int __whence);




extern long int ftell (FILE *__stream);




extern void rewind (FILE *__stream);

# 688 "/usr/include/stdio.h" 3 4






extern int fgetpos (FILE * __stream, fpos_t * __pos);




extern int fsetpos (FILE *__stream, const fpos_t *__pos);
# 711 "/usr/include/stdio.h" 3 4

# 720 "/usr/include/stdio.h" 3 4


extern void clearerr (FILE *__stream) ;

extern int feof (FILE *__stream) ;

extern int ferror (FILE *__stream) ;




extern void clearerr_unlocked (FILE *__stream) ;
extern int feof_unlocked (FILE *__stream) ;
extern int ferror_unlocked (FILE *__stream) ;








extern void perror (const char *__s);






# 1 "/usr/include/bits/sys_errlist.h" 1 3 4
# 27 "/usr/include/bits/sys_errlist.h" 3 4
extern int sys_nerr;
extern const char *const sys_errlist[];
# 750 "/usr/include/stdio.h" 2 3 4




extern int fileno (FILE *__stream) ;




extern int fileno_unlocked (FILE *__stream) ;
# 769 "/usr/include/stdio.h" 3 4
extern FILE *popen (const char *__command, const char *__modes);





extern int pclose (FILE *__stream);





extern char *ctermid (char *__s) ;
# 809 "/usr/include/stdio.h" 3 4
extern void flockfile (FILE *__stream) ;



extern int ftrylockfile (FILE *__stream) ;


extern void funlockfile (FILE *__stream) ;
# 833 "/usr/include/stdio.h" 3 4

# 35 "cairo.h" 2

typedef struct cairo cairo_t;
typedef struct cairo_surface cairo_surface_t;
typedef struct cairo_matrix cairo_matrix_t;
typedef struct cairo_pattern cairo_pattern_t;






cairo_t *
cairo_create (void);

void
cairo_reference (cairo_t *cr);

void
cairo_destroy (cairo_t *cr);

void
cairo_save (cairo_t *cr);

void
cairo_restore (cairo_t *cr);


void
cairo_copy (cairo_t *dest, cairo_t *src);
# 74 "cairo.h"
void
cairo_set_target_surface (cairo_t *cr, cairo_surface_t *surface);

typedef enum cairo_format {
    CAIRO_FORMAT_ARGB32,
    CAIRO_FORMAT_RGB24,
    CAIRO_FORMAT_A8,
    CAIRO_FORMAT_A1
} cairo_format_t;

void
cairo_set_target_image (cairo_t *cr,
                        char *data,
                        cairo_format_t format,
                        int width,
                        int height,
                        int stride);





void
cairo_set_target_ps (cairo_t *cr,
                     FILE *file,
                     double width_inches,
                     double height_inches,
                     double x_pixels_per_inch,
                     double y_pixels_per_inch);







void
cairo_set_target_png (cairo_t *cr,
                      FILE *file,
                      cairo_format_t format,
                      int width,
                      int height);





# 1 "/usr/include/X11/extensions/Xrender.h" 1 3 4
# 29 "/usr/include/X11/extensions/Xrender.h" 3 4
# 1 "/usr/include/X11/extensions/render.h" 1 3 4
# 29 "/usr/include/X11/extensions/render.h" 3 4
typedef unsigned long Glyph;
typedef unsigned long GlyphSet;
typedef unsigned long Picture;
typedef unsigned long PictFormat;
# 30 "/usr/include/X11/extensions/Xrender.h" 2 3 4

# 1 "/usr/include/X11/Xlib.h" 1 3 4
# 52 "/usr/include/X11/Xlib.h" 3 4
# 1 "/usr/include/sys/types.h" 1 3 4
# 29 "/usr/include/sys/types.h" 3 4






typedef __u_char u_char;
typedef __u_short u_short;
typedef __u_int u_int;
typedef __u_long u_long;
typedef __quad_t quad_t;
typedef __u_quad_t u_quad_t;
typedef __fsid_t fsid_t;




typedef __loff_t loff_t;



typedef __ino_t ino_t;
# 62 "/usr/include/sys/types.h" 3 4
typedef __dev_t dev_t;




typedef __gid_t gid_t;




typedef __mode_t mode_t;




typedef __nlink_t nlink_t;




typedef __uid_t uid_t;





typedef __off_t off_t;
# 100 "/usr/include/sys/types.h" 3 4
typedef __pid_t pid_t;




typedef __id_t id_t;




typedef __ssize_t ssize_t;





typedef __daddr_t daddr_t;
typedef __caddr_t caddr_t;





typedef __key_t key_t;
# 133 "/usr/include/sys/types.h" 3 4
# 1 "/usr/include/time.h" 1 3 4
# 74 "/usr/include/time.h" 3 4


typedef __time_t time_t;



# 92 "/usr/include/time.h" 3 4
typedef __clockid_t clockid_t;
# 104 "/usr/include/time.h" 3 4
typedef __timer_t timer_t;
# 134 "/usr/include/sys/types.h" 2 3 4
# 147 "/usr/include/sys/types.h" 3 4
# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 1 3 4
# 148 "/usr/include/sys/types.h" 2 3 4



typedef unsigned long int ulong;
typedef unsigned short int ushort;
typedef unsigned int uint;
# 172 "/usr/include/sys/types.h" 3 4
typedef unsigned char u_int8_t;
typedef unsigned short int u_int16_t;
typedef unsigned int u_int32_t;




typedef int register_t;
# 213 "/usr/include/sys/types.h" 3 4
# 1 "/usr/include/endian.h" 1 3 4
# 37 "/usr/include/endian.h" 3 4
# 1 "/usr/include/bits/endian.h" 1 3 4
# 38 "/usr/include/endian.h" 2 3 4
# 214 "/usr/include/sys/types.h" 2 3 4


# 1 "/usr/include/sys/select.h" 1 3 4
# 31 "/usr/include/sys/select.h" 3 4
# 1 "/usr/include/bits/select.h" 1 3 4
# 32 "/usr/include/sys/select.h" 2 3 4


# 1 "/usr/include/bits/sigset.h" 1 3 4
# 23 "/usr/include/bits/sigset.h" 3 4
typedef int __sig_atomic_t;




typedef struct
  {
    unsigned long int __val[(1024 / (8 * sizeof (unsigned long int)))];
  } __sigset_t;
# 35 "/usr/include/sys/select.h" 2 3 4



typedef __sigset_t sigset_t;





# 1 "/usr/include/time.h" 1 3 4
# 118 "/usr/include/time.h" 3 4
struct timespec
  {
    __time_t tv_sec;
    long int tv_nsec;
  };
# 45 "/usr/include/sys/select.h" 2 3 4

# 1 "/usr/include/bits/time.h" 1 3 4
# 69 "/usr/include/bits/time.h" 3 4
struct timeval
  {
    __time_t tv_sec;
    __suseconds_t tv_usec;
  };
# 47 "/usr/include/sys/select.h" 2 3 4


typedef __suseconds_t suseconds_t;





typedef long int __fd_mask;
# 67 "/usr/include/sys/select.h" 3 4
typedef struct
  {






    __fd_mask __fds_bits[1024 / (8 * sizeof (__fd_mask))];


  } fd_set;






typedef __fd_mask fd_mask;
# 99 "/usr/include/sys/select.h" 3 4

# 109 "/usr/include/sys/select.h" 3 4
extern int select (int __nfds, fd_set * __readfds,
                   fd_set * __writefds,
                   fd_set * __exceptfds,
                   struct timeval * __timeout);
# 128 "/usr/include/sys/select.h" 3 4

# 217 "/usr/include/sys/types.h" 2 3 4


# 1 "/usr/include/sys/sysmacros.h" 1 3 4
# 220 "/usr/include/sys/types.h" 2 3 4
# 231 "/usr/include/sys/types.h" 3 4
typedef __blkcnt_t blkcnt_t;



typedef __fsblkcnt_t fsblkcnt_t;



typedef __fsfilcnt_t fsfilcnt_t;
# 266 "/usr/include/sys/types.h" 3 4
# 1 "/usr/include/bits/pthreadtypes.h" 1 3 4
# 23 "/usr/include/bits/pthreadtypes.h" 3 4
# 1 "/usr/include/bits/sched.h" 1 3 4
# 83 "/usr/include/bits/sched.h" 3 4
struct __sched_param
  {
    int __sched_priority;
  };
# 24 "/usr/include/bits/pthreadtypes.h" 2 3 4


struct _pthread_fastlock
{
  long int __status;
  int __spinlock;

};



typedef struct _pthread_descr_struct *_pthread_descr;





typedef struct __pthread_attr_s
{
  int __detachstate;
  int __schedpolicy;
  struct __sched_param __schedparam;
  int __inheritsched;
  int __scope;
  size_t __guardsize;
  int __stackaddr_set;
  void *__stackaddr;
  size_t __stacksize;
} pthread_attr_t;







typedef long __pthread_cond_align_t;


typedef struct
{
  struct _pthread_fastlock __c_lock;
  _pthread_descr __c_waiting;
  char __padding[48 - sizeof (struct _pthread_fastlock)
                 - sizeof (_pthread_descr) - sizeof (__pthread_cond_align_t)];
  __pthread_cond_align_t __align;
} pthread_cond_t;



typedef struct
{
  int __dummy;
} pthread_condattr_t;


typedef unsigned int pthread_key_t;





typedef struct
{
  int __m_reserved;
  int __m_count;
  _pthread_descr __m_owner;
  int __m_kind;
  struct _pthread_fastlock __m_lock;
} pthread_mutex_t;



typedef struct
{
  int __mutexkind;
} pthread_mutexattr_t;



typedef int pthread_once_t;
# 150 "/usr/include/bits/pthreadtypes.h" 3 4
typedef unsigned long int pthread_t;
# 267 "/usr/include/sys/types.h" 2 3 4



# 53 "/usr/include/X11/Xlib.h" 2 3 4







# 1 "/usr/include/X11/X.h" 1 3 4
# 71 "/usr/include/X11/X.h" 3 4
typedef unsigned long XID;



typedef unsigned long Mask;



typedef unsigned long Atom;

typedef unsigned long VisualID;
typedef unsigned long Time;
# 101 "/usr/include/X11/X.h" 3 4
typedef XID Window;
typedef XID Drawable;


typedef XID Font;

typedef XID Pixmap;
typedef XID Cursor;
typedef XID Colormap;
typedef XID GContext;
typedef XID KeySym;

typedef unsigned char KeyCode;
# 61 "/usr/include/X11/Xlib.h" 2 3 4


# 1 "/usr/include/X11/Xfuncproto.h" 1 3 4
# 64 "/usr/include/X11/Xlib.h" 2 3 4
# 1 "/usr/include/X11/Xosdefs.h" 1 3 4
# 65 "/usr/include/X11/Xlib.h" 2 3 4
# 77 "/usr/include/X11/Xlib.h" 3 4
# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 1 3 4
# 151 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 3 4
typedef int ptrdiff_t;
# 78 "/usr/include/X11/Xlib.h" 2 3 4
# 95 "/usr/include/X11/Xlib.h" 3 4
extern int
_Xmblen(




    char *str,
    int len

    );





typedef char *XPointer;
# 182 "/usr/include/X11/Xlib.h" 3 4
typedef struct _XExtData {
        int number;
        struct _XExtData *next;
        int (*free_private)(
        struct _XExtData *extension
        );
        XPointer private_data;
} XExtData;




typedef struct {
        int extension;
        int major_opcode;
        int first_event;
        int first_error;
} XExtCodes;





typedef struct {
    int depth;
    int bits_per_pixel;
    int scanline_pad;
} XPixmapFormatValues;





typedef struct {
        int function;
        unsigned long plane_mask;
        unsigned long foreground;
        unsigned long background;
        int line_width;
        int line_style;
        int cap_style;

        int join_style;
        int fill_style;

        int fill_rule;
        int arc_mode;
        Pixmap tile;
        Pixmap stipple;
        int ts_x_origin;
        int ts_y_origin;
        Font font;
        int subwindow_mode;
        int graphics_exposures;
        int clip_x_origin;
        int clip_y_origin;
        Pixmap clip_mask;
        int dash_offset;
        char dashes;
} XGCValues;






typedef struct _XGC







*GC;




typedef struct {
        XExtData *ext_data;
        VisualID visualid;



        int class;

        unsigned long red_mask, green_mask, blue_mask;
        int bits_per_rgb;
        int map_entries;
} Visual;




typedef struct {
        int depth;
        int nvisuals;
        Visual *visuals;
} Depth;







struct _XDisplay;

typedef struct {
        XExtData *ext_data;
        struct _XDisplay *display;
        Window root;
        int width, height;
        int mwidth, mheight;
        int ndepths;
        Depth *depths;
        int root_depth;
        Visual *root_visual;
        GC default_gc;
        Colormap cmap;
        unsigned long white_pixel;
        unsigned long black_pixel;
        int max_maps, min_maps;
        int backing_store;
        int save_unders;
        long root_input_mask;
} Screen;




typedef struct {
        XExtData *ext_data;
        int depth;
        int bits_per_pixel;
        int scanline_pad;
} ScreenFormat;




typedef struct {
    Pixmap background_pixmap;
    unsigned long background_pixel;
    Pixmap border_pixmap;
    unsigned long border_pixel;
    int bit_gravity;
    int win_gravity;
    int backing_store;
    unsigned long backing_planes;
    unsigned long backing_pixel;
    int save_under;
    long event_mask;
    long do_not_propagate_mask;
    int override_redirect;
    Colormap colormap;
    Cursor cursor;
} XSetWindowAttributes;

typedef struct {
    int x, y;
    int width, height;
    int border_width;
    int depth;
    Visual *visual;
    Window root;



    int class;

    int bit_gravity;
    int win_gravity;
    int backing_store;
    unsigned long backing_planes;
    unsigned long backing_pixel;
    int save_under;
    Colormap colormap;
    int map_installed;
    int map_state;
    long all_event_masks;
    long your_event_mask;
    long do_not_propagate_mask;
    int override_redirect;
    Screen *screen;
} XWindowAttributes;






typedef struct {
        int family;
        int length;
        char *address;
} XHostAddress;




typedef struct {
        int typelength;
        int valuelength;
        char *type;
        char *value;
} XServerInterpretedAddress;




typedef struct _XImage {
    int width, height;
    int xoffset;
    int format;
    char *data;
    int byte_order;
    int bitmap_unit;
    int bitmap_bit_order;
    int bitmap_pad;
    int depth;
    int bytes_per_line;
    int bits_per_pixel;
    unsigned long red_mask;
    unsigned long green_mask;
    unsigned long blue_mask;
    XPointer obdata;
    struct funcs {
        struct _XImage *(*create_image)(
                struct _XDisplay* ,
                Visual* ,
                unsigned int ,
                int ,
                int ,
                char* ,
                unsigned int ,
                unsigned int ,
                int ,
                int );
        int (*destroy_image) (struct _XImage *);
        unsigned long (*get_pixel) (struct _XImage *, int, int);
        int (*put_pixel) (struct _XImage *, int, int, unsigned long);
        struct _XImage *(*sub_image)(struct _XImage *, int, int, unsigned int, unsigned int);
        int (*add_pixel) (struct _XImage *, long);
        } f;
} XImage;




typedef struct {
    int x, y;
    int width, height;
    int border_width;
    Window sibling;
    int stack_mode;
} XWindowChanges;




typedef struct {
        unsigned long pixel;
        unsigned short red, green, blue;
        char flags;
        char pad;
} XColor;






typedef struct {
    short x1, y1, x2, y2;
} XSegment;

typedef struct {
    short x, y;
} XPoint;

typedef struct {
    short x, y;
    unsigned short width, height;
} XRectangle;

typedef struct {
    short x, y;
    unsigned short width, height;
    short angle1, angle2;
} XArc;




typedef struct {
        int key_click_percent;
        int bell_percent;
        int bell_pitch;
        int bell_duration;
        int led;
        int led_mode;
        int key;
        int auto_repeat_mode;
} XKeyboardControl;



typedef struct {
        int key_click_percent;
        int bell_percent;
        unsigned int bell_pitch, bell_duration;
        unsigned long led_mask;
        int global_auto_repeat;
        char auto_repeats[32];
} XKeyboardState;



typedef struct {
        Time time;
        short x, y;
} XTimeCoord;



typedef struct {
        int max_keypermod;
        KeyCode *modifiermap;
} XModifierKeymap;
# 521 "/usr/include/X11/Xlib.h" 3 4
typedef struct _XDisplay Display;


struct _XPrivate;
struct _XrmHashBucketRec;

typedef struct



{
        XExtData *ext_data;
        struct _XPrivate *private1;
        int fd;
        int private2;
        int proto_major_version;
        int proto_minor_version;
        char *vendor;
        XID private3;
        XID private4;
        XID private5;
        int private6;
        XID (*resource_alloc)(
                struct _XDisplay*
        );
        int byte_order;
        int bitmap_unit;
        int bitmap_pad;
        int bitmap_bit_order;
        int nformats;
        ScreenFormat *pixmap_format;
        int private8;
        int release;
        struct _XPrivate *private9, *private10;
        int qlen;
        unsigned long last_request_read;
        unsigned long request;
        XPointer private11;
        XPointer private12;
        XPointer private13;
        XPointer private14;
        unsigned max_request_size;
        struct _XrmHashBucketRec *db;
        int (*private15)(
                struct _XDisplay*
                );
        char *display_name;
        int default_screen;
        int nscreens;
        Screen *screens;
        unsigned long motion_buffer;
        unsigned long private16;
        int min_keycode;
        int max_keycode;
        XPointer private17;
        XPointer private18;
        int private19;
        char *xdefaults;

}



*_XPrivDisplay;






typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window window;
        Window root;
        Window subwindow;
        Time time;
        int x, y;
        int x_root, y_root;
        unsigned int state;
        unsigned int keycode;
        int same_screen;
} XKeyEvent;
typedef XKeyEvent XKeyPressedEvent;
typedef XKeyEvent XKeyReleasedEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window window;
        Window root;
        Window subwindow;
        Time time;
        int x, y;
        int x_root, y_root;
        unsigned int state;
        unsigned int button;
        int same_screen;
} XButtonEvent;
typedef XButtonEvent XButtonPressedEvent;
typedef XButtonEvent XButtonReleasedEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window window;
        Window root;
        Window subwindow;
        Time time;
        int x, y;
        int x_root, y_root;
        unsigned int state;
        char is_hint;
        int same_screen;
} XMotionEvent;
typedef XMotionEvent XPointerMovedEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window window;
        Window root;
        Window subwindow;
        Time time;
        int x, y;
        int x_root, y_root;
        int mode;
        int detail;




        int same_screen;
        int focus;
        unsigned int state;
} XCrossingEvent;
typedef XCrossingEvent XEnterWindowEvent;
typedef XCrossingEvent XLeaveWindowEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window window;
        int mode;
        int detail;





} XFocusChangeEvent;
typedef XFocusChangeEvent XFocusInEvent;
typedef XFocusChangeEvent XFocusOutEvent;


typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window window;
        char key_vector[32];
} XKeymapEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window window;
        int x, y;
        int width, height;
        int count;
} XExposeEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Drawable drawable;
        int x, y;
        int width, height;
        int count;
        int major_code;
        int minor_code;
} XGraphicsExposeEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Drawable drawable;
        int major_code;
        int minor_code;
} XNoExposeEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window window;
        int state;
} XVisibilityEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window parent;
        Window window;
        int x, y;
        int width, height;
        int border_width;
        int override_redirect;
} XCreateWindowEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window event;
        Window window;
} XDestroyWindowEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window event;
        Window window;
        int from_configure;
} XUnmapEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window event;
        Window window;
        int override_redirect;
} XMapEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window parent;
        Window window;
} XMapRequestEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window event;
        Window window;
        Window parent;
        int x, y;
        int override_redirect;
} XReparentEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window event;
        Window window;
        int x, y;
        int width, height;
        int border_width;
        Window above;
        int override_redirect;
} XConfigureEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window event;
        Window window;
        int x, y;
} XGravityEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window window;
        int width, height;
} XResizeRequestEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window parent;
        Window window;
        int x, y;
        int width, height;
        int border_width;
        Window above;
        int detail;
        unsigned long value_mask;
} XConfigureRequestEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window event;
        Window window;
        int place;
} XCirculateEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window parent;
        Window window;
        int place;
} XCirculateRequestEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window window;
        Atom atom;
        Time time;
        int state;
} XPropertyEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window window;
        Atom selection;
        Time time;
} XSelectionClearEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window owner;
        Window requestor;
        Atom selection;
        Atom target;
        Atom property;
        Time time;
} XSelectionRequestEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window requestor;
        Atom selection;
        Atom target;
        Atom property;
        Time time;
} XSelectionEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window window;
        Colormap colormap;



        int new;

        int state;
} XColormapEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window window;
        Atom message_type;
        int format;
        union {
                char b[20];
                short s[10];
                long l[5];
                } data;
} XClientMessageEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window window;
        int request;

        int first_keycode;
        int count;
} XMappingEvent;

typedef struct {
        int type;
        Display *display;
        XID resourceid;
        unsigned long serial;
        unsigned char error_code;
        unsigned char request_code;
        unsigned char minor_code;
} XErrorEvent;

typedef struct {
        int type;
        unsigned long serial;
        int send_event;
        Display *display;
        Window window;
} XAnyEvent;





typedef union _XEvent {
        int type;
        XAnyEvent xany;
        XKeyEvent xkey;
        XButtonEvent xbutton;
        XMotionEvent xmotion;
        XCrossingEvent xcrossing;
        XFocusChangeEvent xfocus;
        XExposeEvent xexpose;
        XGraphicsExposeEvent xgraphicsexpose;
        XNoExposeEvent xnoexpose;
        XVisibilityEvent xvisibility;
        XCreateWindowEvent xcreatewindow;
        XDestroyWindowEvent xdestroywindow;
        XUnmapEvent xunmap;
        XMapEvent xmap;
        XMapRequestEvent xmaprequest;
        XReparentEvent xreparent;
        XConfigureEvent xconfigure;
        XGravityEvent xgravity;
        XResizeRequestEvent xresizerequest;
        XConfigureRequestEvent xconfigurerequest;
        XCirculateEvent xcirculate;
        XCirculateRequestEvent xcirculaterequest;
        XPropertyEvent xproperty;
        XSelectionClearEvent xselectionclear;
        XSelectionRequestEvent xselectionrequest;
        XSelectionEvent xselection;
        XColormapEvent xcolormap;
        XClientMessageEvent xclient;
        XMappingEvent xmapping;
        XErrorEvent xerror;
        XKeymapEvent xkeymap;
        long pad[24];
} XEvent;







typedef struct {
    short lbearing;
    short rbearing;
    short width;
    short ascent;
    short descent;
    unsigned short attributes;
} XCharStruct;





typedef struct {
    Atom name;
    unsigned long card32;
} XFontProp;

typedef struct {
    XExtData *ext_data;
    Font fid;
    unsigned direction;
    unsigned min_char_or_byte2;
    unsigned max_char_or_byte2;
    unsigned min_byte1;
    unsigned max_byte1;
    int all_chars_exist;
    unsigned default_char;
    int n_properties;
    XFontProp *properties;
    XCharStruct min_bounds;
    XCharStruct max_bounds;
    XCharStruct *per_char;
    int ascent;
    int descent;
} XFontStruct;




typedef struct {
    char *chars;
    int nchars;
    int delta;
    Font font;
} XTextItem;

typedef struct {
    unsigned char byte1;
    unsigned char byte2;
} XChar2b;

typedef struct {
    XChar2b *chars;
    int nchars;
    int delta;
    Font font;
} XTextItem16;


typedef union { Display *display;
                GC gc;
                Visual *visual;
                Screen *screen;
                ScreenFormat *pixmap_format;
                XFontStruct *font; } XEDataObject;

typedef struct {
    XRectangle max_ink_extent;
    XRectangle max_logical_extent;
} XFontSetExtents;





typedef struct _XOM *XOM;
typedef struct _XOC *XOC, *XFontSet;

typedef struct {
    char *chars;
    int nchars;
    int delta;
    XFontSet font_set;
} XmbTextItem;

typedef struct {
    wchar_t *chars;
    int nchars;
    int delta;
    XFontSet font_set;
} XwcTextItem;
# 1125 "/usr/include/X11/Xlib.h" 3 4
typedef struct {
    int charset_count;
    char **charset_list;
} XOMCharSetList;

typedef enum {
    XOMOrientation_LTR_TTB,
    XOMOrientation_RTL_TTB,
    XOMOrientation_TTB_LTR,
    XOMOrientation_TTB_RTL,
    XOMOrientation_Context
} XOrientation;

typedef struct {
    int num_orientation;
    XOrientation *orientation;
} XOMOrientation;

typedef struct {
    int num_font;
    XFontStruct **font_struct_list;
    char **font_name_list;
} XOMFontInfo;

typedef struct _XIM *XIM;
typedef struct _XIC *XIC;

typedef void (*XIMProc)(
    XIM,
    XPointer,
    XPointer
);

typedef int (*XICProc)(
    XIC,
    XPointer,
    XPointer
);

typedef void (*XIDProc)(
    Display*,
    XPointer,
    XPointer
);

typedef unsigned long XIMStyle;

typedef struct {
    unsigned short count_styles;
    XIMStyle *supported_styles;
} XIMStyles;
# 1237 "/usr/include/X11/Xlib.h" 3 4
typedef void *XVaNestedList;

typedef struct {
    XPointer client_data;
    XIMProc callback;
} XIMCallback;

typedef struct {
    XPointer client_data;
    XICProc callback;
} XICCallback;

typedef unsigned long XIMFeedback;
# 1261 "/usr/include/X11/Xlib.h" 3 4
typedef struct _XIMText {
    unsigned short length;
    XIMFeedback *feedback;
    int encoding_is_wchar;
    union {
        char *multi_byte;
        wchar_t *wide_char;
    } string;
} XIMText;

typedef unsigned long XIMPreeditState;





typedef struct _XIMPreeditStateNotifyCallbackStruct {
    XIMPreeditState state;
} XIMPreeditStateNotifyCallbackStruct;

typedef unsigned long XIMResetState;




typedef unsigned long XIMStringConversionFeedback;
# 1295 "/usr/include/X11/Xlib.h" 3 4
typedef struct _XIMStringConversionText {
    unsigned short length;
    XIMStringConversionFeedback *feedback;
    int encoding_is_wchar;
    union {
        char *mbs;
        wchar_t *wcs;
    } string;
} XIMStringConversionText;

typedef unsigned short XIMStringConversionPosition;

typedef unsigned short XIMStringConversionType;






typedef unsigned short XIMStringConversionOperation;




typedef enum {
    XIMForwardChar, XIMBackwardChar,
    XIMForwardWord, XIMBackwardWord,
    XIMCaretUp, XIMCaretDown,
    XIMNextLine, XIMPreviousLine,
    XIMLineStart, XIMLineEnd,
    XIMAbsolutePosition,
    XIMDontChange
} XIMCaretDirection;

typedef struct _XIMStringConversionCallbackStruct {
    XIMStringConversionPosition position;
    XIMCaretDirection direction;
    XIMStringConversionOperation operation;
    unsigned short factor;
    XIMStringConversionText *text;
} XIMStringConversionCallbackStruct;

typedef struct _XIMPreeditDrawCallbackStruct {
    int caret;
    int chg_first;
    int chg_length;
    XIMText *text;
} XIMPreeditDrawCallbackStruct;

typedef enum {
    XIMIsInvisible,
    XIMIsPrimary,
    XIMIsSecondary
} XIMCaretStyle;

typedef struct _XIMPreeditCaretCallbackStruct {
    int position;
    XIMCaretDirection direction;
    XIMCaretStyle style;
} XIMPreeditCaretCallbackStruct;

typedef enum {
    XIMTextType,
    XIMBitmapType
} XIMStatusDataType;

typedef struct _XIMStatusDrawCallbackStruct {
    XIMStatusDataType type;
    union {
        XIMText *text;
        Pixmap bitmap;
    } data;
} XIMStatusDrawCallbackStruct;

typedef struct _XIMHotKeyTrigger {
    KeySym keysym;
    int modifier;
    int modifier_mask;
} XIMHotKeyTrigger;

typedef struct _XIMHotKeyTriggers {
    int num_hot_key;
    XIMHotKeyTrigger *key;
} XIMHotKeyTriggers;

typedef unsigned long XIMHotKeyState;




typedef struct {
    unsigned short count_values;
    char **supported_values;
} XIMValuesList;







extern int _Xdebug;

extern XFontStruct *XLoadQueryFont(
    Display* ,
    const char*
);

extern XFontStruct *XQueryFont(
    Display* ,
    XID
);


extern XTimeCoord *XGetMotionEvents(
    Display* ,
    Window ,
    Time ,
    Time ,
    int*
);

extern XModifierKeymap *XDeleteModifiermapEntry(
    XModifierKeymap* ,

    unsigned int ,



    int
);

extern XModifierKeymap *XGetModifierMapping(
    Display*
);

extern XModifierKeymap *XInsertModifiermapEntry(
    XModifierKeymap* ,

    unsigned int ,



    int
);

extern XModifierKeymap *XNewModifiermap(
    int
);

extern XImage *XCreateImage(
    Display* ,
    Visual* ,
    unsigned int ,
    int ,
    int ,
    char* ,
    unsigned int ,
    unsigned int ,
    int ,
    int
);
extern int XInitImage(
    XImage*
);
extern XImage *XGetImage(
    Display* ,
    Drawable ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    unsigned long ,
    int
);
extern XImage *XGetSubImage(
    Display* ,
    Drawable ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    unsigned long ,
    int ,
    XImage* ,
    int ,
    int
);




extern Display *XOpenDisplay(
    const char*
);

extern void XrmInitialize(
    void
);

extern char *XFetchBytes(
    Display* ,
    int*
);
extern char *XFetchBuffer(
    Display* ,
    int* ,
    int
);
extern char *XGetAtomName(
    Display* ,
    Atom
);
extern int XGetAtomNames(
    Display* ,
    Atom* ,
    int ,
    char**
);
extern char *XGetDefault(
    Display* ,
    const char* ,
    const char*
);
extern char *XDisplayName(
    const char*
);
extern char *XKeysymToString(
    KeySym
);

extern int (*XSynchronize(
    Display* ,
    int
))(
    Display*
);
extern int (*XSetAfterFunction(
    Display* ,
    int (*) (
             Display*
            )
))(
    Display*
);
extern Atom XInternAtom(
    Display* ,
    const char* ,
    int
);
extern int XInternAtoms(
    Display* ,
    char** ,
    int ,
    int ,
    Atom*
);
extern Colormap XCopyColormapAndFree(
    Display* ,
    Colormap
);
extern Colormap XCreateColormap(
    Display* ,
    Window ,
    Visual* ,
    int
);
extern Cursor XCreatePixmapCursor(
    Display* ,
    Pixmap ,
    Pixmap ,
    XColor* ,
    XColor* ,
    unsigned int ,
    unsigned int
);
extern Cursor XCreateGlyphCursor(
    Display* ,
    Font ,
    Font ,
    unsigned int ,
    unsigned int ,
    XColor const * ,
    XColor const *
);
extern Cursor XCreateFontCursor(
    Display* ,
    unsigned int
);
extern Font XLoadFont(
    Display* ,
    const char*
);
extern GC XCreateGC(
    Display* ,
    Drawable ,
    unsigned long ,
    XGCValues*
);
extern GContext XGContextFromGC(
    GC
);
extern void XFlushGC(
    Display* ,
    GC
);
extern Pixmap XCreatePixmap(
    Display* ,
    Drawable ,
    unsigned int ,
    unsigned int ,
    unsigned int
);
extern Pixmap XCreateBitmapFromData(
    Display* ,
    Drawable ,
    const char* ,
    unsigned int ,
    unsigned int
);
extern Pixmap XCreatePixmapFromBitmapData(
    Display* ,
    Drawable ,
    char* ,
    unsigned int ,
    unsigned int ,
    unsigned long ,
    unsigned long ,
    unsigned int
);
extern Window XCreateSimpleWindow(
    Display* ,
    Window ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    unsigned int ,
    unsigned long ,
    unsigned long
);
extern Window XGetSelectionOwner(
    Display* ,
    Atom
);
extern Window XCreateWindow(
    Display* ,
    Window ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    unsigned int ,
    int ,
    unsigned int ,
    Visual* ,
    unsigned long ,
    XSetWindowAttributes*
);
extern Colormap *XListInstalledColormaps(
    Display* ,
    Window ,
    int*
);
extern char **XListFonts(
    Display* ,
    const char* ,
    int ,
    int*
);
extern char **XListFontsWithInfo(
    Display* ,
    const char* ,
    int ,
    int* ,
    XFontStruct**
);
extern char **XGetFontPath(
    Display* ,
    int*
);
extern char **XListExtensions(
    Display* ,
    int*
);
extern Atom *XListProperties(
    Display* ,
    Window ,
    int*
);
extern XHostAddress *XListHosts(
    Display* ,
    int* ,
    int*
);
extern KeySym XKeycodeToKeysym(
    Display* ,

    unsigned int ,



    int
);
extern KeySym XLookupKeysym(
    XKeyEvent* ,
    int
);
extern KeySym *XGetKeyboardMapping(
    Display* ,

    unsigned int ,



    int ,
    int*
);
extern KeySym XStringToKeysym(
    const char*
);
extern long XMaxRequestSize(
    Display*
);
extern long XExtendedMaxRequestSize(
    Display*
);
extern char *XResourceManagerString(
    Display*
);
extern char *XScreenResourceString(
        Screen*
);
extern unsigned long XDisplayMotionBufferSize(
    Display*
);
extern VisualID XVisualIDFromVisual(
    Visual*
);



extern int XInitThreads(
    void
);

extern void XLockDisplay(
    Display*
);

extern void XUnlockDisplay(
    Display*
);



extern XExtCodes *XInitExtension(
    Display* ,
    const char*
);

extern XExtCodes *XAddExtension(
    Display*
);
extern XExtData *XFindOnExtensionList(
    XExtData** ,
    int
);
extern XExtData **XEHeadOfExtensionList(
    XEDataObject
);


extern Window XRootWindow(
    Display* ,
    int
);
extern Window XDefaultRootWindow(
    Display*
);
extern Window XRootWindowOfScreen(
    Screen*
);
extern Visual *XDefaultVisual(
    Display* ,
    int
);
extern Visual *XDefaultVisualOfScreen(
    Screen*
);
extern GC XDefaultGC(
    Display* ,
    int
);
extern GC XDefaultGCOfScreen(
    Screen*
);
extern unsigned long XBlackPixel(
    Display* ,
    int
);
extern unsigned long XWhitePixel(
    Display* ,
    int
);
extern unsigned long XAllPlanes(
    void
);
extern unsigned long XBlackPixelOfScreen(
    Screen*
);
extern unsigned long XWhitePixelOfScreen(
    Screen*
);
extern unsigned long XNextRequest(
    Display*
);
extern unsigned long XLastKnownRequestProcessed(
    Display*
);
extern char *XServerVendor(
    Display*
);
extern char *XDisplayString(
    Display*
);
extern Colormap XDefaultColormap(
    Display* ,
    int
);
extern Colormap XDefaultColormapOfScreen(
    Screen*
);
extern Display *XDisplayOfScreen(
    Screen*
);
extern Screen *XScreenOfDisplay(
    Display* ,
    int
);
extern Screen *XDefaultScreenOfDisplay(
    Display*
);
extern long XEventMaskOfScreen(
    Screen*
);

extern int XScreenNumberOfScreen(
    Screen*
);

typedef int (*XErrorHandler) (
    Display* ,
    XErrorEvent*
);

extern XErrorHandler XSetErrorHandler (
    XErrorHandler
);


typedef int (*XIOErrorHandler) (
    Display*
);

extern XIOErrorHandler XSetIOErrorHandler (
    XIOErrorHandler
);


extern XPixmapFormatValues *XListPixmapFormats(
    Display* ,
    int*
);
extern int *XListDepths(
    Display* ,
    int ,
    int*
);



extern int XReconfigureWMWindow(
    Display* ,
    Window ,
    int ,
    unsigned int ,
    XWindowChanges*
);

extern int XGetWMProtocols(
    Display* ,
    Window ,
    Atom** ,
    int*
);
extern int XSetWMProtocols(
    Display* ,
    Window ,
    Atom* ,
    int
);
extern int XIconifyWindow(
    Display* ,
    Window ,
    int
);
extern int XWithdrawWindow(
    Display* ,
    Window ,
    int
);
extern int XGetCommand(
    Display* ,
    Window ,
    char*** ,
    int*
);
extern int XGetWMColormapWindows(
    Display* ,
    Window ,
    Window** ,
    int*
);
extern int XSetWMColormapWindows(
    Display* ,
    Window ,
    Window* ,
    int
);
extern void XFreeStringList(
    char**
);
extern int XSetTransientForHint(
    Display* ,
    Window ,
    Window
);



extern int XActivateScreenSaver(
    Display*
);

extern int XAddHost(
    Display* ,
    XHostAddress*
);

extern int XAddHosts(
    Display* ,
    XHostAddress* ,
    int
);

extern int XAddToExtensionList(
    struct _XExtData** ,
    XExtData*
);

extern int XAddToSaveSet(
    Display* ,
    Window
);

extern int XAllocColor(
    Display* ,
    Colormap ,
    XColor*
);

extern int XAllocColorCells(
    Display* ,
    Colormap ,
    int ,
    unsigned long* ,
    unsigned int ,
    unsigned long* ,
    unsigned int
);

extern int XAllocColorPlanes(
    Display* ,
    Colormap ,
    int ,
    unsigned long* ,
    int ,
    int ,
    int ,
    int ,
    unsigned long* ,
    unsigned long* ,
    unsigned long*
);

extern int XAllocNamedColor(
    Display* ,
    Colormap ,
    const char* ,
    XColor* ,
    XColor*
);

extern int XAllowEvents(
    Display* ,
    int ,
    Time
);

extern int XAutoRepeatOff(
    Display*
);

extern int XAutoRepeatOn(
    Display*
);

extern int XBell(
    Display* ,
    int
);

extern int XBitmapBitOrder(
    Display*
);

extern int XBitmapPad(
    Display*
);

extern int XBitmapUnit(
    Display*
);

extern int XCellsOfScreen(
    Screen*
);

extern int XChangeActivePointerGrab(
    Display* ,
    unsigned int ,
    Cursor ,
    Time
);

extern int XChangeGC(
    Display* ,
    GC ,
    unsigned long ,
    XGCValues*
);

extern int XChangeKeyboardControl(
    Display* ,
    unsigned long ,
    XKeyboardControl*
);

extern int XChangeKeyboardMapping(
    Display* ,
    int ,
    int ,
    KeySym* ,
    int
);

extern int XChangePointerControl(
    Display* ,
    int ,
    int ,
    int ,
    int ,
    int
);

extern int XChangeProperty(
    Display* ,
    Window ,
    Atom ,
    Atom ,
    int ,
    int ,
    const unsigned char* ,
    int
);

extern int XChangeSaveSet(
    Display* ,
    Window ,
    int
);

extern int XChangeWindowAttributes(
    Display* ,
    Window ,
    unsigned long ,
    XSetWindowAttributes*
);

extern int XCheckIfEvent(
    Display* ,
    XEvent* ,
    int (*) (
               Display* ,
               XEvent* ,
               XPointer
             ) ,
    XPointer
);

extern int XCheckMaskEvent(
    Display* ,
    long ,
    XEvent*
);

extern int XCheckTypedEvent(
    Display* ,
    int ,
    XEvent*
);

extern int XCheckTypedWindowEvent(
    Display* ,
    Window ,
    int ,
    XEvent*
);

extern int XCheckWindowEvent(
    Display* ,
    Window ,
    long ,
    XEvent*
);

extern int XCirculateSubwindows(
    Display* ,
    Window ,
    int
);

extern int XCirculateSubwindowsDown(
    Display* ,
    Window
);

extern int XCirculateSubwindowsUp(
    Display* ,
    Window
);

extern int XClearArea(
    Display* ,
    Window ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    int
);

extern int XClearWindow(
    Display* ,
    Window
);

extern int XCloseDisplay(
    Display*
);

extern int XConfigureWindow(
    Display* ,
    Window ,
    unsigned int ,
    XWindowChanges*
);

extern int XConnectionNumber(
    Display*
);

extern int XConvertSelection(
    Display* ,
    Atom ,
    Atom ,
    Atom ,
    Window ,
    Time
);

extern int XCopyArea(
    Display* ,
    Drawable ,
    Drawable ,
    GC ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    int ,
    int
);

extern int XCopyGC(
    Display* ,
    GC ,
    unsigned long ,
    GC
);

extern int XCopyPlane(
    Display* ,
    Drawable ,
    Drawable ,
    GC ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    int ,
    int ,
    unsigned long
);

extern int XDefaultDepth(
    Display* ,
    int
);

extern int XDefaultDepthOfScreen(
    Screen*
);

extern int XDefaultScreen(
    Display*
);

extern int XDefineCursor(
    Display* ,
    Window ,
    Cursor
);

extern int XDeleteProperty(
    Display* ,
    Window ,
    Atom
);

extern int XDestroyWindow(
    Display* ,
    Window
);

extern int XDestroySubwindows(
    Display* ,
    Window
);

extern int XDoesBackingStore(
    Screen*
);

extern int XDoesSaveUnders(
    Screen*
);

extern int XDisableAccessControl(
    Display*
);


extern int XDisplayCells(
    Display* ,
    int
);

extern int XDisplayHeight(
    Display* ,
    int
);

extern int XDisplayHeightMM(
    Display* ,
    int
);

extern int XDisplayKeycodes(
    Display* ,
    int* ,
    int*
);

extern int XDisplayPlanes(
    Display* ,
    int
);

extern int XDisplayWidth(
    Display* ,
    int
);

extern int XDisplayWidthMM(
    Display* ,
    int
);

extern int XDrawArc(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    int ,
    int
);

extern int XDrawArcs(
    Display* ,
    Drawable ,
    GC ,
    XArc* ,
    int
);

extern int XDrawImageString(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    const char* ,
    int
);

extern int XDrawImageString16(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    const XChar2b* ,
    int
);

extern int XDrawLine(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    int ,
    int
);

extern int XDrawLines(
    Display* ,
    Drawable ,
    GC ,
    XPoint* ,
    int ,
    int
);

extern int XDrawPoint(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int
);

extern int XDrawPoints(
    Display* ,
    Drawable ,
    GC ,
    XPoint* ,
    int ,
    int
);

extern int XDrawRectangle(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    unsigned int ,
    unsigned int
);

extern int XDrawRectangles(
    Display* ,
    Drawable ,
    GC ,
    XRectangle* ,
    int
);

extern int XDrawSegments(
    Display* ,
    Drawable ,
    GC ,
    XSegment* ,
    int
);

extern int XDrawString(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    const char* ,
    int
);

extern int XDrawString16(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    const XChar2b* ,
    int
);

extern int XDrawText(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    XTextItem* ,
    int
);

extern int XDrawText16(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    XTextItem16* ,
    int
);

extern int XEnableAccessControl(
    Display*
);

extern int XEventsQueued(
    Display* ,
    int
);

extern int XFetchName(
    Display* ,
    Window ,
    char**
);

extern int XFillArc(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    int ,
    int
);

extern int XFillArcs(
    Display* ,
    Drawable ,
    GC ,
    XArc* ,
    int
);

extern int XFillPolygon(
    Display* ,
    Drawable ,
    GC ,
    XPoint* ,
    int ,
    int ,
    int
);

extern int XFillRectangle(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    unsigned int ,
    unsigned int
);

extern int XFillRectangles(
    Display* ,
    Drawable ,
    GC ,
    XRectangle* ,
    int
);

extern int XFlush(
    Display*
);

extern int XForceScreenSaver(
    Display* ,
    int
);

extern int XFree(
    void*
);

extern int XFreeColormap(
    Display* ,
    Colormap
);

extern int XFreeColors(
    Display* ,
    Colormap ,
    unsigned long* ,
    int ,
    unsigned long
);

extern int XFreeCursor(
    Display* ,
    Cursor
);

extern int XFreeExtensionList(
    char**
);

extern int XFreeFont(
    Display* ,
    XFontStruct*
);

extern int XFreeFontInfo(
    char** ,
    XFontStruct* ,
    int
);

extern int XFreeFontNames(
    char**
);

extern int XFreeFontPath(
    char**
);

extern int XFreeGC(
    Display* ,
    GC
);

extern int XFreeModifiermap(
    XModifierKeymap*
);

extern int XFreePixmap(
    Display* ,
    Pixmap
);

extern int XGeometry(
    Display* ,
    int ,
    const char* ,
    const char* ,
    unsigned int ,
    unsigned int ,
    unsigned int ,
    int ,
    int ,
    int* ,
    int* ,
    int* ,
    int*
);

extern int XGetErrorDatabaseText(
    Display* ,
    const char* ,
    const char* ,
    const char* ,
    char* ,
    int
);

extern int XGetErrorText(
    Display* ,
    int ,
    char* ,
    int
);

extern int XGetFontProperty(
    XFontStruct* ,
    Atom ,
    unsigned long*
);

extern int XGetGCValues(
    Display* ,
    GC ,
    unsigned long ,
    XGCValues*
);

extern int XGetGeometry(
    Display* ,
    Drawable ,
    Window* ,
    int* ,
    int* ,
    unsigned int* ,
    unsigned int* ,
    unsigned int* ,
    unsigned int*
);

extern int XGetIconName(
    Display* ,
    Window ,
    char**
);

extern int XGetInputFocus(
    Display* ,
    Window* ,
    int*
);

extern int XGetKeyboardControl(
    Display* ,
    XKeyboardState*
);

extern int XGetPointerControl(
    Display* ,
    int* ,
    int* ,
    int*
);

extern int XGetPointerMapping(
    Display* ,
    unsigned char* ,
    int
);

extern int XGetScreenSaver(
    Display* ,
    int* ,
    int* ,
    int* ,
    int*
);

extern int XGetTransientForHint(
    Display* ,
    Window ,
    Window*
);

extern int XGetWindowProperty(
    Display* ,
    Window ,
    Atom ,
    long ,
    long ,
    int ,
    Atom ,
    Atom* ,
    int* ,
    unsigned long* ,
    unsigned long* ,
    unsigned char**
);

extern int XGetWindowAttributes(
    Display* ,
    Window ,
    XWindowAttributes*
);

extern int XGrabButton(
    Display* ,
    unsigned int ,
    unsigned int ,
    Window ,
    int ,
    unsigned int ,
    int ,
    int ,
    Window ,
    Cursor
);

extern int XGrabKey(
    Display* ,
    int ,
    unsigned int ,
    Window ,
    int ,
    int ,
    int
);

extern int XGrabKeyboard(
    Display* ,
    Window ,
    int ,
    int ,
    int ,
    Time
);

extern int XGrabPointer(
    Display* ,
    Window ,
    int ,
    unsigned int ,
    int ,
    int ,
    Window ,
    Cursor ,
    Time
);

extern int XGrabServer(
    Display*
);

extern int XHeightMMOfScreen(
    Screen*
);

extern int XHeightOfScreen(
    Screen*
);

extern int XIfEvent(
    Display* ,
    XEvent* ,
    int (*) (
               Display* ,
               XEvent* ,
               XPointer
             ) ,
    XPointer
);

extern int XImageByteOrder(
    Display*
);

extern int XInstallColormap(
    Display* ,
    Colormap
);

extern KeyCode XKeysymToKeycode(
    Display* ,
    KeySym
);

extern int XKillClient(
    Display* ,
    XID
);

extern int XLookupColor(
    Display* ,
    Colormap ,
    const char* ,
    XColor* ,
    XColor*
);

extern int XLowerWindow(
    Display* ,
    Window
);

extern int XMapRaised(
    Display* ,
    Window
);

extern int XMapSubwindows(
    Display* ,
    Window
);

extern int XMapWindow(
    Display* ,
    Window
);

extern int XMaskEvent(
    Display* ,
    long ,
    XEvent*
);

extern int XMaxCmapsOfScreen(
    Screen*
);

extern int XMinCmapsOfScreen(
    Screen*
);

extern int XMoveResizeWindow(
    Display* ,
    Window ,
    int ,
    int ,
    unsigned int ,
    unsigned int
);

extern int XMoveWindow(
    Display* ,
    Window ,
    int ,
    int
);

extern int XNextEvent(
    Display* ,
    XEvent*
);

extern int XNoOp(
    Display*
);

extern int XParseColor(
    Display* ,
    Colormap ,
    const char* ,
    XColor*
);

extern int XParseGeometry(
    const char* ,
    int* ,
    int* ,
    unsigned int* ,
    unsigned int*
);

extern int XPeekEvent(
    Display* ,
    XEvent*
);

extern int XPeekIfEvent(
    Display* ,
    XEvent* ,
    int (*) (
               Display* ,
               XEvent* ,
               XPointer
             ) ,
    XPointer
);

extern int XPending(
    Display*
);

extern int XPlanesOfScreen(
    Screen*
);

extern int XProtocolRevision(
    Display*
);

extern int XProtocolVersion(
    Display*
);


extern int XPutBackEvent(
    Display* ,
    XEvent*
);

extern int XPutImage(
    Display* ,
    Drawable ,
    GC ,
    XImage* ,
    int ,
    int ,
    int ,
    int ,
    unsigned int ,
    unsigned int
);

extern int XQLength(
    Display*
);

extern int XQueryBestCursor(
    Display* ,
    Drawable ,
    unsigned int ,
    unsigned int ,
    unsigned int* ,
    unsigned int*
);

extern int XQueryBestSize(
    Display* ,
    int ,
    Drawable ,
    unsigned int ,
    unsigned int ,
    unsigned int* ,
    unsigned int*
);

extern int XQueryBestStipple(
    Display* ,
    Drawable ,
    unsigned int ,
    unsigned int ,
    unsigned int* ,
    unsigned int*
);

extern int XQueryBestTile(
    Display* ,
    Drawable ,
    unsigned int ,
    unsigned int ,
    unsigned int* ,
    unsigned int*
);

extern int XQueryColor(
    Display* ,
    Colormap ,
    XColor*
);

extern int XQueryColors(
    Display* ,
    Colormap ,
    XColor* ,
    int
);

extern int XQueryExtension(
    Display* ,
    const char* ,
    int* ,
    int* ,
    int*
);

extern int XQueryKeymap(
    Display* ,
    char [32]
);

extern int XQueryPointer(
    Display* ,
    Window ,
    Window* ,
    Window* ,
    int* ,
    int* ,
    int* ,
    int* ,
    unsigned int*
);

extern int XQueryTextExtents(
    Display* ,
    XID ,
    const char* ,
    int ,
    int* ,
    int* ,
    int* ,
    XCharStruct*
);

extern int XQueryTextExtents16(
    Display* ,
    XID ,
    const XChar2b* ,
    int ,
    int* ,
    int* ,
    int* ,
    XCharStruct*
);

extern int XQueryTree(
    Display* ,
    Window ,
    Window* ,
    Window* ,
    Window** ,
    unsigned int*
);

extern int XRaiseWindow(
    Display* ,
    Window
);

extern int XReadBitmapFile(
    Display* ,
    Drawable ,
    const char* ,
    unsigned int* ,
    unsigned int* ,
    Pixmap* ,
    int* ,
    int*
);

extern int XReadBitmapFileData(
    const char* ,
    unsigned int* ,
    unsigned int* ,
    unsigned char** ,
    int* ,
    int*
);

extern int XRebindKeysym(
    Display* ,
    KeySym ,
    KeySym* ,
    int ,
    const unsigned char* ,
    int
);

extern int XRecolorCursor(
    Display* ,
    Cursor ,
    XColor* ,
    XColor*
);

extern int XRefreshKeyboardMapping(
    XMappingEvent*
);

extern int XRemoveFromSaveSet(
    Display* ,
    Window
);

extern int XRemoveHost(
    Display* ,
    XHostAddress*
);

extern int XRemoveHosts(
    Display* ,
    XHostAddress* ,
    int
);

extern int XReparentWindow(
    Display* ,
    Window ,
    Window ,
    int ,
    int
);

extern int XResetScreenSaver(
    Display*
);

extern int XResizeWindow(
    Display* ,
    Window ,
    unsigned int ,
    unsigned int
);

extern int XRestackWindows(
    Display* ,
    Window* ,
    int
);

extern int XRotateBuffers(
    Display* ,
    int
);

extern int XRotateWindowProperties(
    Display* ,
    Window ,
    Atom* ,
    int ,
    int
);

extern int XScreenCount(
    Display*
);

extern int XSelectInput(
    Display* ,
    Window ,
    long
);

extern int XSendEvent(
    Display* ,
    Window ,
    int ,
    long ,
    XEvent*
);

extern int XSetAccessControl(
    Display* ,
    int
);

extern int XSetArcMode(
    Display* ,
    GC ,
    int
);

extern int XSetBackground(
    Display* ,
    GC ,
    unsigned long
);

extern int XSetClipMask(
    Display* ,
    GC ,
    Pixmap
);

extern int XSetClipOrigin(
    Display* ,
    GC ,
    int ,
    int
);

extern int XSetClipRectangles(
    Display* ,
    GC ,
    int ,
    int ,
    XRectangle* ,
    int ,
    int
);

extern int XSetCloseDownMode(
    Display* ,
    int
);

extern int XSetCommand(
    Display* ,
    Window ,
    char** ,
    int
);

extern int XSetDashes(
    Display* ,
    GC ,
    int ,
    const char* ,
    int
);

extern int XSetFillRule(
    Display* ,
    GC ,
    int
);

extern int XSetFillStyle(
    Display* ,
    GC ,
    int
);

extern int XSetFont(
    Display* ,
    GC ,
    Font
);

extern int XSetFontPath(
    Display* ,
    char** ,
    int
);

extern int XSetForeground(
    Display* ,
    GC ,
    unsigned long
);

extern int XSetFunction(
    Display* ,
    GC ,
    int
);

extern int XSetGraphicsExposures(
    Display* ,
    GC ,
    int
);

extern int XSetIconName(
    Display* ,
    Window ,
    const char*
);

extern int XSetInputFocus(
    Display* ,
    Window ,
    int ,
    Time
);

extern int XSetLineAttributes(
    Display* ,
    GC ,
    unsigned int ,
    int ,
    int ,
    int
);

extern int XSetModifierMapping(
    Display* ,
    XModifierKeymap*
);

extern int XSetPlaneMask(
    Display* ,
    GC ,
    unsigned long
);

extern int XSetPointerMapping(
    Display* ,
    const unsigned char* ,
    int
);

extern int XSetScreenSaver(
    Display* ,
    int ,
    int ,
    int ,
    int
);

extern int XSetSelectionOwner(
    Display* ,
    Atom ,
    Window ,
    Time
);

extern int XSetState(
    Display* ,
    GC ,
    unsigned long ,
    unsigned long ,
    int ,
    unsigned long
);

extern int XSetStipple(
    Display* ,
    GC ,
    Pixmap
);

extern int XSetSubwindowMode(
    Display* ,
    GC ,
    int
);

extern int XSetTSOrigin(
    Display* ,
    GC ,
    int ,
    int
);

extern int XSetTile(
    Display* ,
    GC ,
    Pixmap
);

extern int XSetWindowBackground(
    Display* ,
    Window ,
    unsigned long
);

extern int XSetWindowBackgroundPixmap(
    Display* ,
    Window ,
    Pixmap
);

extern int XSetWindowBorder(
    Display* ,
    Window ,
    unsigned long
);

extern int XSetWindowBorderPixmap(
    Display* ,
    Window ,
    Pixmap
);

extern int XSetWindowBorderWidth(
    Display* ,
    Window ,
    unsigned int
);

extern int XSetWindowColormap(
    Display* ,
    Window ,
    Colormap
);

extern int XStoreBuffer(
    Display* ,
    const char* ,
    int ,
    int
);

extern int XStoreBytes(
    Display* ,
    const char* ,
    int
);

extern int XStoreColor(
    Display* ,
    Colormap ,
    XColor*
);

extern int XStoreColors(
    Display* ,
    Colormap ,
    XColor* ,
    int
);

extern int XStoreName(
    Display* ,
    Window ,
    const char*
);

extern int XStoreNamedColor(
    Display* ,
    Colormap ,
    const char* ,
    unsigned long ,
    int
);

extern int XSync(
    Display* ,
    int
);

extern int XTextExtents(
    XFontStruct* ,
    const char* ,
    int ,
    int* ,
    int* ,
    int* ,
    XCharStruct*
);

extern int XTextExtents16(
    XFontStruct* ,
    const XChar2b* ,
    int ,
    int* ,
    int* ,
    int* ,
    XCharStruct*
);

extern int XTextWidth(
    XFontStruct* ,
    const char* ,
    int
);

extern int XTextWidth16(
    XFontStruct* ,
    const XChar2b* ,
    int
);

extern int XTranslateCoordinates(
    Display* ,
    Window ,
    Window ,
    int ,
    int ,
    int* ,
    int* ,
    Window*
);

extern int XUndefineCursor(
    Display* ,
    Window
);

extern int XUngrabButton(
    Display* ,
    unsigned int ,
    unsigned int ,
    Window
);

extern int XUngrabKey(
    Display* ,
    int ,
    unsigned int ,
    Window
);

extern int XUngrabKeyboard(
    Display* ,
    Time
);

extern int XUngrabPointer(
    Display* ,
    Time
);

extern int XUngrabServer(
    Display*
);

extern int XUninstallColormap(
    Display* ,
    Colormap
);

extern int XUnloadFont(
    Display* ,
    Font
);

extern int XUnmapSubwindows(
    Display* ,
    Window
);

extern int XUnmapWindow(
    Display* ,
    Window
);

extern int XVendorRelease(
    Display*
);

extern int XWarpPointer(
    Display* ,
    Window ,
    Window ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    int ,
    int
);

extern int XWidthMMOfScreen(
    Screen*
);

extern int XWidthOfScreen(
    Screen*
);

extern int XWindowEvent(
    Display* ,
    Window ,
    long ,
    XEvent*
);

extern int XWriteBitmapFile(
    Display* ,
    const char* ,
    Pixmap ,
    unsigned int ,
    unsigned int ,
    int ,
    int
);

extern int XSupportsLocale (void);

extern char *XSetLocaleModifiers(
    const char*
);

extern XOM XOpenOM(
    Display* ,
    struct _XrmHashBucketRec* ,
    const char* ,
    const char*
);

extern int XCloseOM(
    XOM
);

extern char *XSetOMValues(
    XOM ,
    ...
);

extern char *XGetOMValues(
    XOM ,
    ...
);

extern Display *XDisplayOfOM(
    XOM
);

extern char *XLocaleOfOM(
    XOM
);

extern XOC XCreateOC(
    XOM ,
    ...
);

extern void XDestroyOC(
    XOC
);

extern XOM XOMOfOC(
    XOC
);

extern char *XSetOCValues(
    XOC ,
    ...
);

extern char *XGetOCValues(
    XOC ,
    ...
);

extern XFontSet XCreateFontSet(
    Display* ,
    const char* ,
    char*** ,
    int* ,
    char**
);

extern void XFreeFontSet(
    Display* ,
    XFontSet
);

extern int XFontsOfFontSet(
    XFontSet ,
    XFontStruct*** ,
    char***
);

extern char *XBaseFontNameListOfFontSet(
    XFontSet
);

extern char *XLocaleOfFontSet(
    XFontSet
);

extern int XContextDependentDrawing(
    XFontSet
);

extern int XDirectionalDependentDrawing(
    XFontSet
);

extern int XContextualDrawing(
    XFontSet
);

extern XFontSetExtents *XExtentsOfFontSet(
    XFontSet
);

extern int XmbTextEscapement(
    XFontSet ,
    const char* ,
    int
);

extern int XwcTextEscapement(
    XFontSet ,
    const wchar_t* ,
    int
);

extern int Xutf8TextEscapement(
    XFontSet ,
    const char* ,
    int
);

extern int XmbTextExtents(
    XFontSet ,
    const char* ,
    int ,
    XRectangle* ,
    XRectangle*
);

extern int XwcTextExtents(
    XFontSet ,
    const wchar_t* ,
    int ,
    XRectangle* ,
    XRectangle*
);

extern int Xutf8TextExtents(
    XFontSet ,
    const char* ,
    int ,
    XRectangle* ,
    XRectangle*
);

extern int XmbTextPerCharExtents(
    XFontSet ,
    const char* ,
    int ,
    XRectangle* ,
    XRectangle* ,
    int ,
    int* ,
    XRectangle* ,
    XRectangle*
);

extern int XwcTextPerCharExtents(
    XFontSet ,
    const wchar_t* ,
    int ,
    XRectangle* ,
    XRectangle* ,
    int ,
    int* ,
    XRectangle* ,
    XRectangle*
);

extern int Xutf8TextPerCharExtents(
    XFontSet ,
    const char* ,
    int ,
    XRectangle* ,
    XRectangle* ,
    int ,
    int* ,
    XRectangle* ,
    XRectangle*
);

extern void XmbDrawText(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    XmbTextItem* ,
    int
);

extern void XwcDrawText(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    XwcTextItem* ,
    int
);

extern void Xutf8DrawText(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    XmbTextItem* ,
    int
);

extern void XmbDrawString(
    Display* ,
    Drawable ,
    XFontSet ,
    GC ,
    int ,
    int ,
    const char* ,
    int
);

extern void XwcDrawString(
    Display* ,
    Drawable ,
    XFontSet ,
    GC ,
    int ,
    int ,
    const wchar_t* ,
    int
);

extern void Xutf8DrawString(
    Display* ,
    Drawable ,
    XFontSet ,
    GC ,
    int ,
    int ,
    const char* ,
    int
);

extern void XmbDrawImageString(
    Display* ,
    Drawable ,
    XFontSet ,
    GC ,
    int ,
    int ,
    const char* ,
    int
);

extern void XwcDrawImageString(
    Display* ,
    Drawable ,
    XFontSet ,
    GC ,
    int ,
    int ,
    const wchar_t* ,
    int
);

extern void Xutf8DrawImageString(
    Display* ,
    Drawable ,
    XFontSet ,
    GC ,
    int ,
    int ,
    const char* ,
    int
);

extern XIM XOpenIM(
    Display* ,
    struct _XrmHashBucketRec* ,
    char* ,
    char*
);

extern int XCloseIM(
    XIM
);

extern char *XGetIMValues(
    XIM , ...
);

extern char *XSetIMValues(
    XIM , ...
);

extern Display *XDisplayOfIM(
    XIM
);

extern char *XLocaleOfIM(
    XIM
);

extern XIC XCreateIC(
    XIM , ...
);

extern void XDestroyIC(
    XIC
);

extern void XSetICFocus(
    XIC
);

extern void XUnsetICFocus(
    XIC
);

extern wchar_t *XwcResetIC(
    XIC
);

extern char *XmbResetIC(
    XIC
);

extern char *Xutf8ResetIC(
    XIC
);

extern char *XSetICValues(
    XIC , ...
);

extern char *XGetICValues(
    XIC , ...
);

extern XIM XIMOfIC(
    XIC
);

extern int XFilterEvent(
    XEvent* ,
    Window
);

extern int XmbLookupString(
    XIC ,
    XKeyPressedEvent* ,
    char* ,
    int ,
    KeySym* ,
    int*
);

extern int XwcLookupString(
    XIC ,
    XKeyPressedEvent* ,
    wchar_t* ,
    int ,
    KeySym* ,
    int*
);

extern int Xutf8LookupString(
    XIC ,
    XKeyPressedEvent* ,
    char* ,
    int ,
    KeySym* ,
    int*
);

extern XVaNestedList XVaCreateNestedList(
    int , ...
);



extern int XRegisterIMInstantiateCallback(
    Display* ,
    struct _XrmHashBucketRec* ,
    char* ,
    char* ,
    XIDProc ,
    XPointer
);

extern int XUnregisterIMInstantiateCallback(
    Display* ,
    struct _XrmHashBucketRec* ,
    char* ,
    char* ,
    XIDProc ,
    XPointer
);

typedef void (*XConnectionWatchProc)(
    Display* ,
    XPointer ,
    int ,
    int ,
    XPointer*
);


extern int XInternalConnectionNumbers(
    Display* ,
    int** ,
    int*
);

extern void XProcessInternalConnection(
    Display* ,
    int
);

extern int XAddConnectionWatch(
    Display* ,
    XConnectionWatchProc ,
    XPointer
);

extern void XRemoveConnectionWatch(
    Display* ,
    XConnectionWatchProc ,
    XPointer
);

extern void XSetAuthorization(
    char * ,
    int ,
    char * ,
    int
);

extern int _Xmbtowc(
    wchar_t * ,




    char * ,
    int

);

extern int _Xwctomb(
    char * ,
    wchar_t
);


# 32 "/usr/include/X11/extensions/Xrender.h" 2 3 4


# 1 "/usr/include/X11/Xutil.h" 1 3 4
# 74 "/usr/include/X11/Xutil.h" 3 4
typedef struct {
        long flags;
        int x, y;
        int width, height;
        int min_width, min_height;
        int max_width, max_height;
        int width_inc, height_inc;
        struct {
                int x;
                int y;
        } min_aspect, max_aspect;
        int base_width, base_height;
        int win_gravity;
} XSizeHints;
# 112 "/usr/include/X11/Xutil.h" 3 4
typedef struct {
        long flags;
        int input;

        int initial_state;
        Pixmap icon_pixmap;
        Window icon_window;
        int icon_x, icon_y;
        Pixmap icon_mask;
        XID window_group;

} XWMHints;
# 156 "/usr/include/X11/Xutil.h" 3 4
typedef struct {
    unsigned char *value;
    Atom encoding;
    int format;
    unsigned long nitems;
} XTextProperty;





typedef enum {
    XStringStyle,
    XCompoundTextStyle,
    XTextStyle,
    XStdICCTextStyle,

    XUTF8StringStyle
} XICCEncodingStyle;

typedef struct {
        int min_width, min_height;
        int max_width, max_height;
        int width_inc, height_inc;
} XIconSize;

typedef struct {
        char *res_name;
        char *res_class;
} XClassHint;
# 224 "/usr/include/X11/Xutil.h" 3 4
typedef struct _XComposeStatus {
    XPointer compose_ptr;
    int chars_matched;
} XComposeStatus;
# 259 "/usr/include/X11/Xutil.h" 3 4
typedef struct _XRegion *Region;
# 273 "/usr/include/X11/Xutil.h" 3 4
typedef struct {
  Visual *visual;
  VisualID visualid;
  int screen;
  int depth;



  int class;

  unsigned long red_mask;
  unsigned long green_mask;
  unsigned long blue_mask;
  int colormap_size;
  int bits_per_rgb;
} XVisualInfo;
# 306 "/usr/include/X11/Xutil.h" 3 4
typedef struct {
        Colormap colormap;
        unsigned long red_max;
        unsigned long red_mult;
        unsigned long green_max;
        unsigned long green_mult;
        unsigned long blue_max;
        unsigned long blue_mult;
        unsigned long base_pixel;
        VisualID visualid;
        XID killid;
} XStandardColormap;
# 343 "/usr/include/X11/Xutil.h" 3 4
typedef int XContext;








extern XClassHint *XAllocClassHint (
    void
);

extern XIconSize *XAllocIconSize (
    void
);

extern XSizeHints *XAllocSizeHints (
    void
);

extern XStandardColormap *XAllocStandardColormap (
    void
);

extern XWMHints *XAllocWMHints (
    void
);

extern int XClipBox(
    Region ,
    XRectangle*
);

extern Region XCreateRegion(
    void
);

extern const char *XDefaultString (void);

extern int XDeleteContext(
    Display* ,
    XID ,
    XContext
);

extern int XDestroyRegion(
    Region
);

extern int XEmptyRegion(
    Region
);

extern int XEqualRegion(
    Region ,
    Region
);

extern int XFindContext(
    Display* ,
    XID ,
    XContext ,
    XPointer*
);

extern int XGetClassHint(
    Display* ,
    Window ,
    XClassHint*
);

extern int XGetIconSizes(
    Display* ,
    Window ,
    XIconSize** ,
    int*
);

extern int XGetNormalHints(
    Display* ,
    Window ,
    XSizeHints*
);

extern int XGetRGBColormaps(
    Display* ,
    Window ,
    XStandardColormap** ,
    int* ,
    Atom
);

extern int XGetSizeHints(
    Display* ,
    Window ,
    XSizeHints* ,
    Atom
);

extern int XGetStandardColormap(
    Display* ,
    Window ,
    XStandardColormap* ,
    Atom
);

extern int XGetTextProperty(
    Display* ,
    Window ,
    XTextProperty* ,
    Atom
);

extern XVisualInfo *XGetVisualInfo(
    Display* ,
    long ,
    XVisualInfo* ,
    int*
);

extern int XGetWMClientMachine(
    Display* ,
    Window ,
    XTextProperty*
);

extern XWMHints *XGetWMHints(
    Display* ,
    Window
);

extern int XGetWMIconName(
    Display* ,
    Window ,
    XTextProperty*
);

extern int XGetWMName(
    Display* ,
    Window ,
    XTextProperty*
);

extern int XGetWMNormalHints(
    Display* ,
    Window ,
    XSizeHints* ,
    long*
);

extern int XGetWMSizeHints(
    Display* ,
    Window ,
    XSizeHints* ,
    long* ,
    Atom
);

extern int XGetZoomHints(
    Display* ,
    Window ,
    XSizeHints*
);

extern int XIntersectRegion(
    Region ,
    Region ,
    Region
);

extern void XConvertCase(
    KeySym ,
    KeySym* ,
    KeySym*
);

extern int XLookupString(
    XKeyEvent* ,
    char* ,
    int ,
    KeySym* ,
    XComposeStatus*
);

extern int XMatchVisualInfo(
    Display* ,
    int ,
    int ,
    int ,
    XVisualInfo*
);

extern int XOffsetRegion(
    Region ,
    int ,
    int
);

extern int XPointInRegion(
    Region ,
    int ,
    int
);

extern Region XPolygonRegion(
    XPoint* ,
    int ,
    int
);

extern int XRectInRegion(
    Region ,
    int ,
    int ,
    unsigned int ,
    unsigned int
);

extern int XSaveContext(
    Display* ,
    XID ,
    XContext ,
    const char*
);

extern int XSetClassHint(
    Display* ,
    Window ,
    XClassHint*
);

extern int XSetIconSizes(
    Display* ,
    Window ,
    XIconSize* ,
    int
);

extern int XSetNormalHints(
    Display* ,
    Window ,
    XSizeHints*
);

extern void XSetRGBColormaps(
    Display* ,
    Window ,
    XStandardColormap* ,
    int ,
    Atom
);

extern int XSetSizeHints(
    Display* ,
    Window ,
    XSizeHints* ,
    Atom
);

extern int XSetStandardProperties(
    Display* ,
    Window ,
    const char* ,
    const char* ,
    Pixmap ,
    char** ,
    int ,
    XSizeHints*
);

extern void XSetTextProperty(
    Display* ,
    Window ,
    XTextProperty* ,
    Atom
);

extern void XSetWMClientMachine(
    Display* ,
    Window ,
    XTextProperty*
);

extern int XSetWMHints(
    Display* ,
    Window ,
    XWMHints*
);

extern void XSetWMIconName(
    Display* ,
    Window ,
    XTextProperty*
);

extern void XSetWMName(
    Display* ,
    Window ,
    XTextProperty*
);

extern void XSetWMNormalHints(
    Display* ,
    Window ,
    XSizeHints*
);

extern void XSetWMProperties(
    Display* ,
    Window ,
    XTextProperty* ,
    XTextProperty* ,
    char** ,
    int ,
    XSizeHints* ,
    XWMHints* ,
    XClassHint*
);

extern void XmbSetWMProperties(
    Display* ,
    Window ,
    const char* ,
    const char* ,
    char** ,
    int ,
    XSizeHints* ,
    XWMHints* ,
    XClassHint*
);

extern void Xutf8SetWMProperties(
    Display* ,
    Window ,
    const char* ,
    const char* ,
    char** ,
    int ,
    XSizeHints* ,
    XWMHints* ,
    XClassHint*
);

extern void XSetWMSizeHints(
    Display* ,
    Window ,
    XSizeHints* ,
    Atom
);

extern int XSetRegion(
    Display* ,
    GC ,
    Region
);

extern void XSetStandardColormap(
    Display* ,
    Window ,
    XStandardColormap* ,
    Atom
);

extern int XSetZoomHints(
    Display* ,
    Window ,
    XSizeHints*
);

extern int XShrinkRegion(
    Region ,
    int ,
    int
);

extern int XStringListToTextProperty(
    char** ,
    int ,
    XTextProperty*
);

extern int XSubtractRegion(
    Region ,
    Region ,
    Region
);

extern int XmbTextListToTextProperty(
    Display* display,
    char** list,
    int count,
    XICCEncodingStyle style,
    XTextProperty* text_prop_return
);

extern int XwcTextListToTextProperty(
    Display* display,
    wchar_t** list,
    int count,
    XICCEncodingStyle style,
    XTextProperty* text_prop_return
);

extern int Xutf8TextListToTextProperty(
    Display* display,
    char** list,
    int count,
    XICCEncodingStyle style,
    XTextProperty* text_prop_return
);

extern void XwcFreeStringList(
    wchar_t** list
);

extern int XTextPropertyToStringList(
    XTextProperty* ,
    char*** ,
    int*
);

extern int XmbTextPropertyToTextList(
    Display* display,
    const XTextProperty* text_prop,
    char*** list_return,
    int* count_return
);

extern int XwcTextPropertyToTextList(
    Display* display,
    const XTextProperty* text_prop,
    wchar_t*** list_return,
    int* count_return
);

extern int Xutf8TextPropertyToTextList(
    Display* display,
    const XTextProperty* text_prop,
    char*** list_return,
    int* count_return
);

extern int XUnionRectWithRegion(
    XRectangle* ,
    Region ,
    Region
);

extern int XUnionRegion(
    Region ,
    Region ,
    Region
);

extern int XWMGeometry(
    Display* ,
    int ,
    const char* ,
    const char* ,
    unsigned int ,
    XSizeHints* ,
    int* ,
    int* ,
    int* ,
    int* ,
    int*
);

extern int XXorRegion(
    Region ,
    Region ,
    Region
);


# 35 "/usr/include/X11/extensions/Xrender.h" 2 3 4

typedef struct {
    short red;
    short redMask;
    short green;
    short greenMask;
    short blue;
    short blueMask;
    short alpha;
    short alphaMask;
} XRenderDirectFormat;

typedef struct {
    PictFormat id;
    int type;
    int depth;
    XRenderDirectFormat direct;
    Colormap colormap;
} XRenderPictFormat;
# 68 "/usr/include/X11/extensions/Xrender.h" 3 4
typedef struct _XRenderPictureAttributes {
    int repeat;
    Picture alpha_map;
    int alpha_x_origin;
    int alpha_y_origin;
    int clip_x_origin;
    int clip_y_origin;
    Pixmap clip_mask;
    int graphics_exposures;
    int subwindow_mode;
    int poly_edge;
    int poly_mode;
    Atom dither;
    int component_alpha;
} XRenderPictureAttributes;

typedef struct {
    unsigned short red;
    unsigned short green;
    unsigned short blue;
    unsigned short alpha;
} XRenderColor;

typedef struct _XGlyphInfo {
    unsigned short width;
    unsigned short height;
    short x;
    short y;
    short xOff;
    short yOff;
} XGlyphInfo;

typedef struct _XGlyphElt8 {
    GlyphSet glyphset;
    const char *chars;
    int nchars;
    int xOff;
    int yOff;
} XGlyphElt8;

typedef struct _XGlyphElt16 {
    GlyphSet glyphset;
    const unsigned short *chars;
    int nchars;
    int xOff;
    int yOff;
} XGlyphElt16;

typedef struct _XGlyphElt32 {
    GlyphSet glyphset;
    const unsigned int *chars;
    int nchars;
    int xOff;
    int yOff;
} XGlyphElt32;

typedef double XDouble;

typedef struct _XPointDouble {
    XDouble x, y;
} XPointDouble;




typedef int XFixed;

typedef struct _XPointFixed {
    XFixed x, y;
} XPointFixed;

typedef struct _XLineFixed {
    XPointFixed p1, p2;
} XLineFixed;

typedef struct _XTriangle {
    XPointFixed p1, p2, p3;
} XTriangle;

typedef struct _XTrapezoid {
    XFixed top, bottom;
    XLineFixed left, right;
} XTrapezoid;

typedef struct _XTransform {
    XFixed matrix[3][3];
} XTransform;

typedef struct _XFilters {
    int nfilter;
    char **filter;
    int nalias;
    short *alias;
} XFilters;

typedef struct _XIndexValue {
    unsigned long pixel;
    unsigned short red, green, blue, alpha;
} XIndexValue;

typedef struct _XAnimCursor {
    Cursor cursor;
    unsigned long delay;
} XAnimCursor;



int XRenderQueryExtension (Display *dpy, int *event_basep, int *error_basep);

int XRenderQueryVersion (Display *dpy,
                            int *major_versionp,
                            int *minor_versionp);

int XRenderQueryFormats (Display *dpy);

int XRenderQuerySubpixelOrder (Display *dpy, int screen);

int XRenderSetSubpixelOrder (Display *dpy, int screen, int subpixel);

XRenderPictFormat *
XRenderFindVisualFormat (Display *dpy, const Visual *visual);

XRenderPictFormat *
XRenderFindFormat (Display *dpy,
                   unsigned long mask,
                   const XRenderPictFormat *templ,
                   int count);
# 203 "/usr/include/X11/extensions/Xrender.h" 3 4
XRenderPictFormat *
XRenderFindStandardFormat (Display *dpy,
                           int format);

XIndexValue *
XRenderQueryPictIndexValues(Display *dpy,
                            const XRenderPictFormat *format,
                            int *num);

Picture
XRenderCreatePicture (Display *dpy,
                      Drawable drawable,
                      const XRenderPictFormat *format,
                      unsigned long valuemask,
                      const XRenderPictureAttributes *attributes);

void
XRenderChangePicture (Display *dpy,
                      Picture picture,
                      unsigned long valuemask,
                      const XRenderPictureAttributes *attributes);

void
XRenderSetPictureClipRectangles (Display *dpy,
                                 Picture picture,
                                 int xOrigin,
                                 int yOrigin,
                                 const XRectangle *rects,
                                 int n);

void
XRenderSetPictureClipRegion (Display *dpy,
                             Picture picture,
                             Region r);

void
XRenderSetPictureTransform (Display *dpy,
                            Picture picture,
                            XTransform *transform);

void
XRenderFreePicture (Display *dpy,
                    Picture picture);

void
XRenderComposite (Display *dpy,
                  int op,
                  Picture src,
                  Picture mask,
                  Picture dst,
                  int src_x,
                  int src_y,
                  int mask_x,
                  int mask_y,
                  int dst_x,
                  int dst_y,
                  unsigned int width,
                  unsigned int height);

GlyphSet
XRenderCreateGlyphSet (Display *dpy, const XRenderPictFormat *format);

GlyphSet
XRenderReferenceGlyphSet (Display *dpy, GlyphSet existing);

void
XRenderFreeGlyphSet (Display *dpy, GlyphSet glyphset);

void
XRenderAddGlyphs (Display *dpy,
                  GlyphSet glyphset,
                  const Glyph *gids,
                  const XGlyphInfo *glyphs,
                  int nglyphs,
                  const char *images,
                  int nbyte_images);

void
XRenderFreeGlyphs (Display *dpy,
                   GlyphSet glyphset,
                   const Glyph *gids,
                   int nglyphs);

void
XRenderCompositeString8 (Display *dpy,
                         int op,
                         Picture src,
                         Picture dst,
                         const XRenderPictFormat *maskFormat,
                         GlyphSet glyphset,
                         int xSrc,
                         int ySrc,
                         int xDst,
                         int yDst,
                         const char *string,
                         int nchar);

void
XRenderCompositeString16 (Display *dpy,
                          int op,
                          Picture src,
                          Picture dst,
                          const XRenderPictFormat *maskFormat,
                          GlyphSet glyphset,
                          int xSrc,
                          int ySrc,
                          int xDst,
                          int yDst,
                          const unsigned short *string,
                          int nchar);

void
XRenderCompositeString32 (Display *dpy,
                          int op,
                          Picture src,
                          Picture dst,
                          const XRenderPictFormat *maskFormat,
                          GlyphSet glyphset,
                          int xSrc,
                          int ySrc,
                          int xDst,
                          int yDst,
                          const unsigned int *string,
                          int nchar);

void
XRenderCompositeText8 (Display *dpy,
                       int op,
                       Picture src,
                       Picture dst,
                       const XRenderPictFormat *maskFormat,
                       int xSrc,
                       int ySrc,
                       int xDst,
                       int yDst,
                       const XGlyphElt8 *elts,
                       int nelt);

void
XRenderCompositeText16 (Display *dpy,
                        int op,
                        Picture src,
                        Picture dst,
                        const XRenderPictFormat *maskFormat,
                        int xSrc,
                        int ySrc,
                        int xDst,
                        int yDst,
                        const XGlyphElt16 *elts,
                        int nelt);

void
XRenderCompositeText32 (Display *dpy,
                        int op,
                        Picture src,
                        Picture dst,
                        const XRenderPictFormat *maskFormat,
                        int xSrc,
                        int ySrc,
                        int xDst,
                        int yDst,
                        const XGlyphElt32 *elts,
                        int nelt);

void
XRenderFillRectangle (Display *dpy,
                      int op,
                      Picture dst,
                      const XRenderColor *color,
                      int x,
                      int y,
                      unsigned int width,
                      unsigned int height);

void
XRenderFillRectangles (Display *dpy,
                       int op,
                       Picture dst,
                       const XRenderColor *color,
                       const XRectangle *rectangles,
                       int n_rects);

void
XRenderCompositeTrapezoids (Display *dpy,
                            int op,
                            Picture src,
                            Picture dst,
                            const XRenderPictFormat *maskFormat,
                            int xSrc,
                            int ySrc,
                            const XTrapezoid *traps,
                            int ntrap);

void
XRenderCompositeTriangles (Display *dpy,
                           int op,
                           Picture src,
                           Picture dst,
                            const XRenderPictFormat *maskFormat,
                           int xSrc,
                           int ySrc,
                           const XTriangle *triangles,
                           int ntriangle);

void
XRenderCompositeTriStrip (Display *dpy,
                          int op,
                          Picture src,
                          Picture dst,
                            const XRenderPictFormat *maskFormat,
                          int xSrc,
                          int ySrc,
                          const XPointFixed *points,
                          int npoint);

void
XRenderCompositeTriFan (Display *dpy,
                        int op,
                        Picture src,
                        Picture dst,
                        const XRenderPictFormat *maskFormat,
                        int xSrc,
                        int ySrc,
                        const XPointFixed *points,
                        int npoint);

void
XRenderCompositeDoublePoly (Display *dpy,
                            int op,
                            Picture src,
                            Picture dst,
                            const XRenderPictFormat *maskFormat,
                            int xSrc,
                            int ySrc,
                            int xDst,
                            int yDst,
                            const XPointDouble *fpoints,
                            int npoints,
                            int winding);
int
XRenderParseColor(Display *dpy,
                  char *spec,
                  XRenderColor *def);

Cursor
XRenderCreateCursor (Display *dpy,
                     Picture source,
                     unsigned int x,
                     unsigned int y);

XFilters *
XRenderQueryFilters (Display *dpy, Drawable drawable);

void
XRenderSetPictureFilter (Display *dpy,
                         Picture picture,
                         char *filter,
                         XFixed *params,
                         int nparams);

Cursor
XRenderCreateAnimCursor (Display *dpy,
                         int ncursor,
                         XAnimCursor *cursors);


# 122 "cairo.h" 2



void
cairo_set_target_drawable (cairo_t *cr,
                           Display *dpy,
                           Drawable drawable);
# 153 "cairo.h"
typedef enum cairo_operator {
    CAIRO_OPERATOR_CLEAR,
    CAIRO_OPERATOR_SRC,
    CAIRO_OPERATOR_DST,
    CAIRO_OPERATOR_OVER,
    CAIRO_OPERATOR_OVER_REVERSE,
    CAIRO_OPERATOR_IN,
    CAIRO_OPERATOR_IN_REVERSE,
    CAIRO_OPERATOR_OUT,
    CAIRO_OPERATOR_OUT_REVERSE,
    CAIRO_OPERATOR_ATOP,
    CAIRO_OPERATOR_ATOP_REVERSE,
    CAIRO_OPERATOR_XOR,
    CAIRO_OPERATOR_ADD,
    CAIRO_OPERATOR_SATURATE
} cairo_operator_t;

void
cairo_set_operator (cairo_t *cr, cairo_operator_t op);
# 190 "cairo.h"
void
cairo_set_rgb_color (cairo_t *cr, double red, double green, double blue);

void
cairo_set_pattern (cairo_t *cr, cairo_pattern_t *pattern);

void
cairo_set_alpha (cairo_t *cr, double alpha);





void
cairo_set_tolerance (cairo_t *cr, double tolerance);

typedef enum cairo_fill_rule {
    CAIRO_FILL_RULE_WINDING,
    CAIRO_FILL_RULE_EVEN_ODD
} cairo_fill_rule_t;

void
cairo_set_fill_rule (cairo_t *cr, cairo_fill_rule_t fill_rule);

void
cairo_set_line_width (cairo_t *cr, double width);

typedef enum cairo_line_cap {
    CAIRO_LINE_CAP_BUTT,
    CAIRO_LINE_CAP_ROUND,
    CAIRO_LINE_CAP_SQUARE
} cairo_line_cap_t;

void
cairo_set_line_cap (cairo_t *cr, cairo_line_cap_t line_cap);

typedef enum cairo_line_join {
    CAIRO_LINE_JOIN_MITER,
    CAIRO_LINE_JOIN_ROUND,
    CAIRO_LINE_JOIN_BEVEL
} cairo_line_join_t;

void
cairo_set_line_join (cairo_t *cr, cairo_line_join_t line_join);

void
cairo_set_dash (cairo_t *cr, double *dashes, int ndash, double offset);

void
cairo_set_miter_limit (cairo_t *cr, double limit);

void
cairo_translate (cairo_t *cr, double tx, double ty);

void
cairo_scale (cairo_t *cr, double sx, double sy);

void
cairo_rotate (cairo_t *cr, double angle);

void
cairo_concat_matrix (cairo_t *cr,
                     cairo_matrix_t *matrix);

void
cairo_set_matrix (cairo_t *cr,
                  cairo_matrix_t *matrix);

void
cairo_default_matrix (cairo_t *cr);



void
cairo_identity_matrix (cairo_t *cr);

void
cairo_transform_point (cairo_t *cr, double *x, double *y);

void
cairo_transform_distance (cairo_t *cr, double *dx, double *dy);

void
cairo_inverse_transform_point (cairo_t *cr, double *x, double *y);

void
cairo_inverse_transform_distance (cairo_t *cr, double *dx, double *dy);


void
cairo_new_path (cairo_t *cr);

void
cairo_move_to (cairo_t *cr, double x, double y);

void
cairo_line_to (cairo_t *cr, double x, double y);

void
cairo_curve_to (cairo_t *cr,
                double x1, double y1,
                double x2, double y2,
                double x3, double y3);

void
cairo_arc (cairo_t *cr,
           double xc, double yc,
           double radius,
           double angle1, double angle2);

void
cairo_arc_negative (cairo_t *cr,
                    double xc, double yc,
                    double radius,
                    double angle1, double angle2);
# 314 "cairo.h"
void
cairo_rel_move_to (cairo_t *cr, double dx, double dy);

void
cairo_rel_line_to (cairo_t *cr, double dx, double dy);

void
cairo_rel_curve_to (cairo_t *cr,
                    double dx1, double dy1,
                    double dx2, double dy2,
                    double dx3, double dy3);

void
cairo_rectangle (cairo_t *cr,
                 double x, double y,
                 double width, double height);
# 343 "cairo.h"
void
cairo_close_path (cairo_t *cr);


void
cairo_stroke (cairo_t *cr);

void
cairo_fill (cairo_t *cr);

void
cairo_copy_page (cairo_t *cr);

void
cairo_show_page (cairo_t *cr);


int
cairo_in_stroke (cairo_t *cr, double x, double y);

int
cairo_in_fill (cairo_t *cr, double x, double y);


void
cairo_stroke_extents (cairo_t *cr,
                      double *x1, double *y1,
                      double *x2, double *y2);

void
cairo_fill_extents (cairo_t *cr,
                    double *x1, double *y1,
                    double *x2, double *y2);


void
cairo_init_clip (cairo_t *cr);


void
cairo_clip (cairo_t *cr);



typedef struct cairo_font cairo_font_t;

typedef struct {
  unsigned long index;
  double x;
  double y;
} cairo_glyph_t;

typedef struct {
    double x_bearing;
    double y_bearing;
    double width;
    double height;
    double x_advance;
    double y_advance;
} cairo_text_extents_t;

typedef struct {
    double ascent;
    double descent;
    double height;
    double max_x_advance;
    double max_y_advance;
} cairo_font_extents_t;

typedef enum cairo_font_slant {
  CAIRO_FONT_SLANT_NORMAL,
  CAIRO_FONT_SLANT_ITALIC,
  CAIRO_FONT_SLANT_OBLIQUE
} cairo_font_slant_t;

typedef enum cairo_font_weight {
  CAIRO_FONT_WEIGHT_NORMAL,
  CAIRO_FONT_WEIGHT_BOLD
} cairo_font_weight_t;




void
cairo_select_font (cairo_t *ct,
                   const char *family,
                   cairo_font_slant_t slant,
                   cairo_font_weight_t weight);

void
cairo_scale_font (cairo_t *cr, double scale);

void
cairo_transform_font (cairo_t *cr, cairo_matrix_t *matrix);

void
cairo_show_text (cairo_t *ct, const unsigned char *utf8);

void
cairo_show_glyphs (cairo_t *ct, cairo_glyph_t *glyphs, int num_glyphs);

cairo_font_t *
cairo_current_font (cairo_t *ct);

void
cairo_current_font_extents (cairo_t *ct,
                            cairo_font_extents_t *extents);

void
cairo_set_font (cairo_t *ct, cairo_font_t *font);

void
cairo_text_extents (cairo_t *ct,
                    const unsigned char *utf8,
                    cairo_text_extents_t *extents);

void
cairo_glyph_extents (cairo_t *ct,
                     cairo_glyph_t *glyphs,
                     int num_glyphs,
                     cairo_text_extents_t *extents);

void
cairo_text_path (cairo_t *ct, const unsigned char *utf8);

void
cairo_glyph_path (cairo_t *ct, cairo_glyph_t *glyphs, int num_glyphs);



void
cairo_font_reference (cairo_font_t *font);

void
cairo_font_destroy (cairo_font_t *font);

void
cairo_font_set_transform (cairo_font_t *font,
                          cairo_matrix_t *matrix);

void
cairo_font_current_transform (cairo_font_t *font,
                              cairo_matrix_t *matrix);



# 1 "/usr/include/fontconfig/fontconfig.h" 1 3 4
# 28 "/usr/include/fontconfig/fontconfig.h" 3 4
# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stdarg.h" 1 3 4
# 105 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stdarg.h" 3 4
typedef __gnuc_va_list va_list;
# 29 "/usr/include/fontconfig/fontconfig.h" 2 3 4

typedef unsigned char FcChar8;
typedef unsigned short FcChar16;
typedef unsigned int FcChar32;
typedef int FcBool;
# 148 "/usr/include/fontconfig/fontconfig.h" 3 4
typedef enum _FcType {
    FcTypeVoid,
    FcTypeInteger,
    FcTypeDouble,
    FcTypeString,
    FcTypeBool,
    FcTypeMatrix,
    FcTypeCharSet,
    FcTypeFTFace,
    FcTypeLangSet
} FcType;

typedef struct _FcMatrix {
    double xx, xy, yx, yy;
} FcMatrix;
# 172 "/usr/include/fontconfig/fontconfig.h" 3 4
typedef struct _FcCharSet FcCharSet;

typedef struct _FcObjectType {
    const char *object;
    FcType type;
} FcObjectType;

typedef struct _FcConstant {
    const FcChar8 *name;
    const char *object;
    int value;
} FcConstant;

typedef enum _FcResult {
    FcResultMatch, FcResultNoMatch, FcResultTypeMismatch, FcResultNoId
} FcResult;

typedef struct _FcPattern FcPattern;

typedef struct _FcLangSet FcLangSet;

typedef struct _FcValue {
    FcType type;
    union {
        const FcChar8 *s;
        int i;
        FcBool b;
        double d;
        const FcMatrix *m;
        const FcCharSet *c;
        void *f;
        const FcPattern *p;
        const FcLangSet *l;
    } u;
} FcValue;

typedef struct _FcFontSet {
    int nfont;
    int sfont;
    FcPattern **fonts;
} FcFontSet;

typedef struct _FcObjectSet {
    int nobject;
    int sobject;
    const char **objects;
} FcObjectSet;

typedef enum _FcMatchKind {
    FcMatchPattern, FcMatchFont
} FcMatchKind;

typedef enum _FcLangResult {
    FcLangEqual, FcLangDifferentCountry, FcLangDifferentLang
} FcLangResult;

typedef enum _FcSetName {
    FcSetSystem = 0,
    FcSetApplication = 1
} FcSetName;

typedef struct _FcAtomic FcAtomic;
# 243 "/usr/include/fontconfig/fontconfig.h" 3 4
typedef enum { FcEndianBig, FcEndianLittle } FcEndian;

typedef struct _FcConfig FcConfig;

typedef struct _FcGlobalCache FcFileCache;

typedef struct _FcBlanks FcBlanks;

typedef struct _FcStrList FcStrList;

typedef struct _FcStrSet FcStrSet;



FcBool
FcDirCacheValid (const FcChar8 *cache_file);


FcBlanks *
FcBlanksCreate (void);

void
FcBlanksDestroy (FcBlanks *b);

FcBool
FcBlanksAdd (FcBlanks *b, FcChar32 ucs4);

FcBool
FcBlanksIsMember (FcBlanks *b, FcChar32 ucs4);


FcChar8 *
FcConfigHome (void);

FcBool
FcConfigEnableHome (FcBool enable);

FcChar8 *
FcConfigFilename (const FcChar8 *url);

FcConfig *
FcConfigCreate (void);

void
FcConfigDestroy (FcConfig *config);

FcBool
FcConfigSetCurrent (FcConfig *config);

FcConfig *
FcConfigGetCurrent (void);

FcBool
FcConfigUptoDate (FcConfig *config);

FcBool
FcConfigBuildFonts (FcConfig *config);

FcStrList *
FcConfigGetFontDirs (FcConfig *config);

FcStrList *
FcConfigGetConfigDirs (FcConfig *config);

FcStrList *
FcConfigGetConfigFiles (FcConfig *config);

FcChar8 *
FcConfigGetCache (FcConfig *config);

FcBlanks *
FcConfigGetBlanks (FcConfig *config);

int
FcConfigGetRescanInverval (FcConfig *config);

FcBool
FcConfigSetRescanInverval (FcConfig *config, int rescanInterval);

FcFontSet *
FcConfigGetFonts (FcConfig *config,
                  FcSetName set);

FcBool
FcConfigAppFontAddFile (FcConfig *config,
                        const FcChar8 *file);

FcBool
FcConfigAppFontAddDir (FcConfig *config,
                       const FcChar8 *dir);

void
FcConfigAppFontClear (FcConfig *config);

FcBool
FcConfigSubstituteWithPat (FcConfig *config,
                           FcPattern *p,
                           FcPattern *p_pat,
                           FcMatchKind kind);

FcBool
FcConfigSubstitute (FcConfig *config,
                    FcPattern *p,
                    FcMatchKind kind);


FcCharSet *
FcCharSetCreate (void);

void
FcCharSetDestroy (FcCharSet *fcs);

FcBool
FcCharSetAddChar (FcCharSet *fcs, FcChar32 ucs4);

FcCharSet *
FcCharSetCopy (FcCharSet *src);

FcBool
FcCharSetEqual (const FcCharSet *a, const FcCharSet *b);

FcCharSet *
FcCharSetIntersect (const FcCharSet *a, const FcCharSet *b);

FcCharSet *
FcCharSetUnion (const FcCharSet *a, const FcCharSet *b);

FcCharSet *
FcCharSetSubtract (const FcCharSet *a, const FcCharSet *b);

FcBool
FcCharSetHasChar (const FcCharSet *fcs, FcChar32 ucs4);

FcChar32
FcCharSetCount (const FcCharSet *a);

FcChar32
FcCharSetIntersectCount (const FcCharSet *a, const FcCharSet *b);

FcChar32
FcCharSetSubtractCount (const FcCharSet *a, const FcCharSet *b);

FcBool
FcCharSetIsSubset (const FcCharSet *a, const FcCharSet *b);




FcChar32
FcCharSetFirstPage (const FcCharSet *a,
                    FcChar32 map[(256/32)],
                    FcChar32 *next);

FcChar32
FcCharSetNextPage (const FcCharSet *a,
                   FcChar32 map[(256/32)],
                   FcChar32 *next);



void
FcValuePrint (const FcValue v);

void
FcPatternPrint (const FcPattern *p);

void
FcFontSetPrint (const FcFontSet *s);


void
FcDefaultSubstitute (FcPattern *pattern);


FcBool
FcFileScan (FcFontSet *set,
            FcStrSet *dirs,
            FcFileCache *cache,
            FcBlanks *blanks,
            const FcChar8 *file,
            FcBool force);

FcBool
FcDirScan (FcFontSet *set,
           FcStrSet *dirs,
           FcFileCache *cache,
           FcBlanks *blanks,
           const FcChar8 *dir,
           FcBool force);

FcBool
FcDirSave (FcFontSet *set, FcStrSet *dirs, const FcChar8 *dir);


FcPattern *
FcFreeTypeQuery (const FcChar8 *file, int id, FcBlanks *blanks, int *count);



FcFontSet *
FcFontSetCreate (void);

void
FcFontSetDestroy (FcFontSet *s);

FcBool
FcFontSetAdd (FcFontSet *s, FcPattern *font);


FcConfig *
FcInitLoadConfig (void);

FcConfig *
FcInitLoadConfigAndFonts (void);

FcBool
FcInit (void);

int
FcGetVersion (void);

FcBool
FcInitReinitialize (void);

FcBool
FcInitBringUptoDate (void);


FcLangSet *
FcLangSetCreate (void);

void
FcLangSetDestroy (FcLangSet *ls);

FcLangSet *
FcLangSetCopy (const FcLangSet *ls);

FcBool
FcLangSetAdd (FcLangSet *ls, const FcChar8 *lang);

FcLangResult
FcLangSetHasLang (const FcLangSet *ls, const FcChar8 *lang);

FcLangResult
FcLangSetCompare (const FcLangSet *lsa, const FcLangSet *lsb);

FcBool
FcLangSetContains (const FcLangSet *lsa, const FcLangSet *lsb);

FcBool
FcLangSetEqual (const FcLangSet *lsa, const FcLangSet *lsb);

FcChar32
FcLangSetHash (const FcLangSet *ls);


FcObjectSet *
FcObjectSetCreate (void);

FcBool
FcObjectSetAdd (FcObjectSet *os, const char *object);

void
FcObjectSetDestroy (FcObjectSet *os);

FcObjectSet *
FcObjectSetVaBuild (const char *first, va_list va);

FcObjectSet *
FcObjectSetBuild (const char *first, ...);

FcFontSet *
FcFontSetList (FcConfig *config,
               FcFontSet **sets,
               int nsets,
               FcPattern *p,
               FcObjectSet *os);

FcFontSet *
FcFontList (FcConfig *config,
            FcPattern *p,
            FcObjectSet *os);



FcAtomic *
FcAtomicCreate (const FcChar8 *file);

FcBool
FcAtomicLock (FcAtomic *atomic);

FcChar8 *
FcAtomicNewFile (FcAtomic *atomic);

FcChar8 *
FcAtomicOrigFile (FcAtomic *atomic);

FcBool
FcAtomicReplaceOrig (FcAtomic *atomic);

void
FcAtomicDeleteNew (FcAtomic *atomic);

void
FcAtomicUnlock (FcAtomic *atomic);

void
FcAtomicDestroy (FcAtomic *atomic);


FcPattern *
FcFontSetMatch (FcConfig *config,
                FcFontSet **sets,
                int nsets,
                FcPattern *p,
                FcResult *result);

FcPattern *
FcFontMatch (FcConfig *config,
             FcPattern *p,
             FcResult *result);

FcPattern *
FcFontRenderPrepare (FcConfig *config,
                     FcPattern *pat,
                     FcPattern *font);

FcFontSet *
FcFontSetSort (FcConfig *config,
               FcFontSet **sets,
               int nsets,
               FcPattern *p,
               FcBool trim,
               FcCharSet **csp,
               FcResult *result);

FcFontSet *
FcFontSort (FcConfig *config,
            FcPattern *p,
            FcBool trim,
            FcCharSet **csp,
            FcResult *result);

void
FcFontSetSortDestroy (FcFontSet *fs);


FcMatrix *
FcMatrixCopy (const FcMatrix *mat);

FcBool
FcMatrixEqual (const FcMatrix *mat1, const FcMatrix *mat2);

void
FcMatrixMultiply (FcMatrix *result, const FcMatrix *a, const FcMatrix *b);

void
FcMatrixRotate (FcMatrix *m, double c, double s);

void
FcMatrixScale (FcMatrix *m, double sx, double sy);

void
FcMatrixShear (FcMatrix *m, double sh, double sv);



FcBool
FcNameRegisterObjectTypes (const FcObjectType *types, int ntype);

FcBool
FcNameUnregisterObjectTypes (const FcObjectType *types, int ntype);

const FcObjectType *
FcNameGetObjectType (const char *object);

FcBool
FcNameRegisterConstants (const FcConstant *consts, int nconsts);

FcBool
FcNameUnregisterConstants (const FcConstant *consts, int nconsts);

const FcConstant *
FcNameGetConstant (FcChar8 *string);

FcBool
FcNameConstant (FcChar8 *string, int *result);

FcPattern *
FcNameParse (const FcChar8 *name);

FcChar8 *
FcNameUnparse (FcPattern *pat);


FcPattern *
FcPatternCreate (void);

FcPattern *
FcPatternDuplicate (const FcPattern *p);

void
FcPatternReference (FcPattern *p);

void
FcValueDestroy (FcValue v);

FcBool
FcValueEqual (FcValue va, FcValue vb);

FcValue
FcValueSave (FcValue v);

void
FcPatternDestroy (FcPattern *p);

FcBool
FcPatternEqual (const FcPattern *pa, const FcPattern *pb);

FcBool
FcPatternEqualSubset (const FcPattern *pa, const FcPattern *pb, const FcObjectSet *os);

FcChar32
FcPatternHash (const FcPattern *p);

FcBool
FcPatternAdd (FcPattern *p, const char *object, FcValue value, FcBool append);

FcBool
FcPatternAddWeak (FcPattern *p, const char *object, FcValue value, FcBool append);

FcResult
FcPatternGet (const FcPattern *p, const char *object, int id, FcValue *v);

FcBool
FcPatternDel (FcPattern *p, const char *object);

FcBool
FcPatternAddInteger (FcPattern *p, const char *object, int i);

FcBool
FcPatternAddDouble (FcPattern *p, const char *object, double d);

FcBool
FcPatternAddString (FcPattern *p, const char *object, const FcChar8 *s);

FcBool
FcPatternAddMatrix (FcPattern *p, const char *object, const FcMatrix *s);

FcBool
FcPatternAddCharSet (FcPattern *p, const char *object, const FcCharSet *c);

FcBool
FcPatternAddBool (FcPattern *p, const char *object, FcBool b);

FcBool
FcPatternAddLangSet (FcPattern *p, const char *object, const FcLangSet *ls);

FcResult
FcPatternGetInteger (const FcPattern *p, const char *object, int n, int *i);

FcResult
FcPatternGetDouble (const FcPattern *p, const char *object, int n, double *d);

FcResult
FcPatternGetString (const FcPattern *p, const char *object, int n, FcChar8 ** s);

FcResult
FcPatternGetMatrix (const FcPattern *p, const char *object, int n, FcMatrix **s);

FcResult
FcPatternGetCharSet (const FcPattern *p, const char *object, int n, FcCharSet **c);

FcResult
FcPatternGetBool (const FcPattern *p, const char *object, int n, FcBool *b);

FcResult
FcPatternGetLangSet (const FcPattern *p, const char *object, int n, FcLangSet **ls);

FcPattern *
FcPatternVaBuild (FcPattern *orig, va_list va);

FcPattern *
FcPatternBuild (FcPattern *orig, ...);



FcChar8 *
FcStrCopy (const FcChar8 *s);

FcChar8 *
FcStrCopyFilename (const FcChar8 *s);





int
FcStrCmpIgnoreCase (const FcChar8 *s1, const FcChar8 *s2);

int
FcStrCmp (const FcChar8 *s1, const FcChar8 *s2);

int
FcUtf8ToUcs4 (const FcChar8 *src_orig,
              FcChar32 *dst,
              int len);

FcBool
FcUtf8Len (const FcChar8 *string,
           int len,
           int *nchar,
           int *wchar);



int
FcUcs4ToUtf8 (FcChar32 ucs4,
              FcChar8 dest[6]);

int
FcUtf16ToUcs4 (const FcChar8 *src_orig,
               FcEndian endian,
               FcChar32 *dst,
               int len);

FcBool
FcUtf16Len (const FcChar8 *string,
            FcEndian endian,
            int len,
            int *nchar,
            int *wchar);

FcChar8 *
FcStrDirname (const FcChar8 *file);

FcChar8 *
FcStrBasename (const FcChar8 *file);

FcStrSet *
FcStrSetCreate (void);

FcBool
FcStrSetMember (FcStrSet *set, const FcChar8 *s);

FcBool
FcStrSetEqual (FcStrSet *sa, FcStrSet *sb);

FcBool
FcStrSetAdd (FcStrSet *set, const FcChar8 *s);

FcBool
FcStrSetAddFilename (FcStrSet *set, const FcChar8 *s);

FcBool
FcStrSetDel (FcStrSet *set, const FcChar8 *s);

void
FcStrSetDestroy (FcStrSet *set);

FcStrList *
FcStrListCreate (FcStrSet *set);

FcChar8 *
FcStrListNext (FcStrList *list);

void
FcStrListDone (FcStrList *list);


FcBool
FcConfigParseAndLoad (FcConfig *config, const FcChar8 *file, FcBool complain);


# 490 "cairo.h" 2
# 1 "/usr/include/ft2build.h" 1 3 4
# 56 "/usr/include/ft2build.h" 3 4
# 1 "/usr/include/freetype2/freetype/config/ftheader.h" 1 3 4
# 531 "/usr/include/freetype2/freetype/config/ftheader.h" 3 4
# 1 "/usr/include/freetype2/freetype/internal/internal.h" 1 3 4
# 532 "/usr/include/freetype2/freetype/config/ftheader.h" 2 3 4
# 57 "/usr/include/ft2build.h" 2 3 4
# 491 "cairo.h" 2
# 1 "/usr/include/freetype2/freetype/freetype.h" 1
# 51 "/usr/include/freetype2/freetype/freetype.h"
# 1 "/usr/include/freetype2/freetype/config/ftconfig.h" 1
# 42 "/usr/include/freetype2/freetype/config/ftconfig.h"
# 1 "/usr/include/freetype2/freetype/config/ftoption.h" 1
# 26 "/usr/include/freetype2/freetype/config/ftoption.h"

# 524 "/usr/include/freetype2/freetype/config/ftoption.h"

# 43 "/usr/include/freetype2/freetype/config/ftconfig.h" 2
# 1 "/usr/include/freetype2/freetype/config/ftstdlib.h" 1
# 61 "/usr/include/freetype2/freetype/config/ftstdlib.h"
# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/limits.h" 1 3 4
# 11 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/limits.h" 3 4
# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/syslimits.h" 1 3 4






# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/limits.h" 1 3 4
# 122 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/limits.h" 3 4
# 1 "/usr/include/limits.h" 1 3 4
# 45 "/usr/include/limits.h" 3 4
# 1 "/usr/include/bits/wordsize.h" 1 3 4
# 46 "/usr/include/limits.h" 2 3 4
# 144 "/usr/include/limits.h" 3 4
# 1 "/usr/include/bits/posix1_lim.h" 1 3 4
# 130 "/usr/include/bits/posix1_lim.h" 3 4
# 1 "/usr/include/bits/local_lim.h" 1 3 4
# 36 "/usr/include/bits/local_lim.h" 3 4
# 1 "/usr/include/linux/limits.h" 1 3 4
# 37 "/usr/include/bits/local_lim.h" 2 3 4
# 131 "/usr/include/bits/posix1_lim.h" 2 3 4
# 145 "/usr/include/limits.h" 2 3 4



# 1 "/usr/include/bits/posix2_lim.h" 1 3 4
# 149 "/usr/include/limits.h" 2 3 4
# 123 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/limits.h" 2 3 4
# 8 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/syslimits.h" 2 3 4
# 12 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/limits.h" 2 3 4
# 62 "/usr/include/freetype2/freetype/config/ftstdlib.h" 2
# 74 "/usr/include/freetype2/freetype/config/ftstdlib.h"
# 1 "/usr/include/ctype.h" 1 3 4
# 30 "/usr/include/ctype.h" 3 4

# 48 "/usr/include/ctype.h" 3 4
enum
{
  _ISupper = ((0) < 8 ? ((1 << (0)) << 8) : ((1 << (0)) >> 8)),
  _ISlower = ((1) < 8 ? ((1 << (1)) << 8) : ((1 << (1)) >> 8)),
  _ISalpha = ((2) < 8 ? ((1 << (2)) << 8) : ((1 << (2)) >> 8)),
  _ISdigit = ((3) < 8 ? ((1 << (3)) << 8) : ((1 << (3)) >> 8)),
  _ISxdigit = ((4) < 8 ? ((1 << (4)) << 8) : ((1 << (4)) >> 8)),
  _ISspace = ((5) < 8 ? ((1 << (5)) << 8) : ((1 << (5)) >> 8)),
  _ISprint = ((6) < 8 ? ((1 << (6)) << 8) : ((1 << (6)) >> 8)),
  _ISgraph = ((7) < 8 ? ((1 << (7)) << 8) : ((1 << (7)) >> 8)),
  _ISblank = ((8) < 8 ? ((1 << (8)) << 8) : ((1 << (8)) >> 8)),
  _IScntrl = ((9) < 8 ? ((1 << (9)) << 8) : ((1 << (9)) >> 8)),
  _ISpunct = ((10) < 8 ? ((1 << (10)) << 8) : ((1 << (10)) >> 8)),
  _ISalnum = ((11) < 8 ? ((1 << (11)) << 8) : ((1 << (11)) >> 8))
};
# 81 "/usr/include/ctype.h" 3 4
extern const unsigned short int **__ctype_b_loc (void)
     ;
extern const __int32_t **__ctype_tolower_loc (void)
     ;
extern const __int32_t **__ctype_toupper_loc (void)
     ;
# 96 "/usr/include/ctype.h" 3 4






extern int isalnum (int) ;
extern int isalpha (int) ;
extern int iscntrl (int) ;
extern int isdigit (int) ;
extern int islower (int) ;
extern int isgraph (int) ;
extern int isprint (int) ;
extern int ispunct (int) ;
extern int isspace (int) ;
extern int isupper (int) ;
extern int isxdigit (int) ;



extern int tolower (int __c) ;


extern int toupper (int __c) ;


# 142 "/usr/include/ctype.h" 3 4
extern int isascii (int __c) ;



extern int toascii (int __c) ;



extern int _toupper (int) ;
extern int _tolower (int) ;
# 323 "/usr/include/ctype.h" 3 4

# 75 "/usr/include/freetype2/freetype/config/ftstdlib.h" 2
# 83 "/usr/include/freetype2/freetype/config/ftstdlib.h"
# 1 "/usr/include/string.h" 1 3 4
# 28 "/usr/include/string.h" 3 4





# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 1 3 4
# 34 "/usr/include/string.h" 2 3 4




extern void *memcpy (void * __dest,
                     const void * __src, size_t __n) ;


extern void *memmove (void *__dest, const void *__src, size_t __n)
     ;






extern void *memccpy (void * __dest, const void * __src,
                      int __c, size_t __n)
     ;





extern void *memset (void *__s, int __c, size_t __n) ;


extern int memcmp (const void *__s1, const void *__s2, size_t __n)
     ;


extern void *memchr (const void *__s, int __c, size_t __n)
      ;

# 80 "/usr/include/string.h" 3 4


extern char *strcpy (char * __dest, const char * __src)
     ;

extern char *strncpy (char * __dest,
                      const char * __src, size_t __n) ;


extern char *strcat (char * __dest, const char * __src)
     ;

extern char *strncat (char * __dest, const char * __src,
                      size_t __n) ;


extern int strcmp (const char *__s1, const char *__s2)
     ;

extern int strncmp (const char *__s1, const char *__s2, size_t __n)
     ;


extern int strcoll (const char *__s1, const char *__s2)
     ;

extern size_t strxfrm (char * __dest,
                       const char * __src, size_t __n) ;

# 126 "/usr/include/string.h" 3 4
extern char *strdup (const char *__s) ;
# 160 "/usr/include/string.h" 3 4


extern char *strchr (const char *__s, int __c) ;

extern char *strrchr (const char *__s, int __c) ;











extern size_t strcspn (const char *__s, const char *__reject)
     ;


extern size_t strspn (const char *__s, const char *__accept)
     ;

extern char *strpbrk (const char *__s, const char *__accept)
     ;

extern char *strstr (const char *__haystack, const char *__needle)
     ;



extern char *strtok (char * __s, const char * __delim)
     ;




extern char *__strtok_r (char * __s,
                         const char * __delim,
                         char ** __save_ptr) ;

extern char *strtok_r (char * __s, const char * __delim,
                       char ** __save_ptr) ;
# 228 "/usr/include/string.h" 3 4


extern size_t strlen (const char *__s) ;

# 241 "/usr/include/string.h" 3 4


extern char *strerror (int __errnum) ;

# 268 "/usr/include/string.h" 3 4
extern char *strerror_r (int __errnum, char *__buf, size_t __buflen) ;





extern void __bzero (void *__s, size_t __n) ;



extern void bcopy (const void *__src, void *__dest, size_t __n) ;


extern void bzero (void *__s, size_t __n) ;


extern int bcmp (const void *__s1, const void *__s2, size_t __n)
     ;


extern char *index (const char *__s, int __c) ;


extern char *rindex (const char *__s, int __c) ;



extern int ffs (int __i) ;
# 308 "/usr/include/string.h" 3 4
extern int strcasecmp (const char *__s1, const char *__s2)
     ;


extern int strncasecmp (const char *__s1, const char *__s2, size_t __n)
     ;
# 330 "/usr/include/string.h" 3 4
extern char *strsep (char ** __stringp,
                     const char * __delim) ;
# 400 "/usr/include/string.h" 3 4

# 84 "/usr/include/freetype2/freetype/config/ftstdlib.h" 2
# 108 "/usr/include/freetype2/freetype/config/ftstdlib.h"
# 1 "/usr/include/stdlib.h" 1 3 4
# 33 "/usr/include/stdlib.h" 3 4
# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 1 3 4
# 34 "/usr/include/stdlib.h" 2 3 4


# 93 "/usr/include/stdlib.h" 3 4


typedef struct
  {
    int quot;
    int rem;
  } div_t;



typedef struct
  {
    long int quot;
    long int rem;
  } ldiv_t;



# 137 "/usr/include/stdlib.h" 3 4
extern size_t __ctype_get_mb_cur_max (void) ;




extern double atof (const char *__nptr) ;

extern int atoi (const char *__nptr) ;

extern long int atol (const char *__nptr) ;

# 157 "/usr/include/stdlib.h" 3 4


extern double strtod (const char * __nptr,
                      char ** __endptr) ;

# 174 "/usr/include/stdlib.h" 3 4


extern long int strtol (const char * __nptr,
                        char ** __endptr, int __base) ;

extern unsigned long int strtoul (const char * __nptr,
                                  char ** __endptr, int __base)
     ;

# 264 "/usr/include/stdlib.h" 3 4
extern double __strtod_internal (const char * __nptr,
                                 char ** __endptr, int __group)
     ;
extern float __strtof_internal (const char * __nptr,
                                char ** __endptr, int __group)
     ;
extern long double __strtold_internal (const char * __nptr,
                                       char ** __endptr,
                                       int __group) ;

extern long int __strtol_internal (const char * __nptr,
                                   char ** __endptr,
                                   int __base, int __group) ;



extern unsigned long int __strtoul_internal (const char * __nptr,
                                             char ** __endptr,
                                             int __base, int __group) ;
# 408 "/usr/include/stdlib.h" 3 4
extern char *l64a (long int __n) ;


extern long int a64l (const char *__s) ;
# 423 "/usr/include/stdlib.h" 3 4
extern long int random (void) ;


extern void srandom (unsigned int __seed) ;





extern char *initstate (unsigned int __seed, char *__statebuf,
                        size_t __statelen) ;



extern char *setstate (char *__statebuf) ;







struct random_data
  {
    int32_t *fptr;
    int32_t *rptr;
    int32_t *state;
    int rand_type;
    int rand_deg;
    int rand_sep;
    int32_t *end_ptr;
  };

extern int random_r (struct random_data * __buf,
                     int32_t * __result) ;

extern int srandom_r (unsigned int __seed, struct random_data *__buf) ;

extern int initstate_r (unsigned int __seed, char * __statebuf,
                        size_t __statelen,
                        struct random_data * __buf) ;

extern int setstate_r (char * __statebuf,
                       struct random_data * __buf) ;






extern int rand (void) ;

extern void srand (unsigned int __seed) ;




extern int rand_r (unsigned int *__seed) ;







extern double drand48 (void) ;
extern double erand48 (unsigned short int __xsubi[3]) ;


extern long int lrand48 (void) ;
extern long int nrand48 (unsigned short int __xsubi[3]) ;


extern long int mrand48 (void) ;
extern long int jrand48 (unsigned short int __xsubi[3]) ;


extern void srand48 (long int __seedval) ;
extern unsigned short int *seed48 (unsigned short int __seed16v[3]) ;
extern void lcong48 (unsigned short int __param[7]) ;





struct drand48_data
  {
    unsigned short int __x[3];
    unsigned short int __old_x[3];
    unsigned short int __c;
    unsigned short int __init;
    unsigned long long int __a;
  };


extern int drand48_r (struct drand48_data * __buffer,
                      double * __result) ;
extern int erand48_r (unsigned short int __xsubi[3],
                      struct drand48_data * __buffer,
                      double * __result) ;


extern int lrand48_r (struct drand48_data * __buffer,
                      long int * __result) ;
extern int nrand48_r (unsigned short int __xsubi[3],
                      struct drand48_data * __buffer,
                      long int * __result) ;


extern int mrand48_r (struct drand48_data * __buffer,
                      long int * __result) ;
extern int jrand48_r (unsigned short int __xsubi[3],
                      struct drand48_data * __buffer,
                      long int * __result) ;


extern int srand48_r (long int __seedval, struct drand48_data *__buffer)
     ;

extern int seed48_r (unsigned short int __seed16v[3],
                     struct drand48_data *__buffer) ;

extern int lcong48_r (unsigned short int __param[7],
                      struct drand48_data *__buffer) ;









extern void *malloc (size_t __size) ;

extern void *calloc (size_t __nmemb, size_t __size)
     ;







extern void *realloc (void *__ptr, size_t __size) ;

extern void free (void *__ptr) ;




extern void cfree (void *__ptr) ;



# 1 "/usr/include/alloca.h" 1 3 4
# 25 "/usr/include/alloca.h" 3 4
# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 1 3 4
# 26 "/usr/include/alloca.h" 2 3 4







extern void *alloca (size_t __size) ;






# 579 "/usr/include/stdlib.h" 2 3 4




extern void *valloc (size_t __size) ;
# 592 "/usr/include/stdlib.h" 3 4


extern void abort (void) ;



extern int atexit (void (*__func) (void)) ;





extern int on_exit (void (*__func) (int __status, void *__arg), void *__arg)
     ;






extern void exit (int __status) ;

# 624 "/usr/include/stdlib.h" 3 4


extern char *getenv (const char *__name) ;




extern char *__secure_getenv (const char *__name) ;





extern int putenv (char *__string) ;





extern int setenv (const char *__name, const char *__value, int __replace)
     ;


extern int unsetenv (const char *__name) ;






extern int clearenv (void) ;
# 663 "/usr/include/stdlib.h" 3 4
extern char *mktemp (char *__template) ;
# 674 "/usr/include/stdlib.h" 3 4
extern int mkstemp (char *__template);
# 693 "/usr/include/stdlib.h" 3 4
extern char *mkdtemp (char *__template) ;








extern int system (const char *__command);

# 720 "/usr/include/stdlib.h" 3 4
extern char *realpath (const char * __name,
                       char * __resolved) ;






typedef int (*__compar_fn_t) (const void *, const void *);









extern void *bsearch (const void *__key, const void *__base,
                      size_t __nmemb, size_t __size, __compar_fn_t __compar);



extern void qsort (void *__base, size_t __nmemb, size_t __size,
                   __compar_fn_t __compar);



extern int abs (int __x) ;
extern long int labs (long int __x) ;












extern div_t div (int __numer, int __denom)
     ;
extern ldiv_t ldiv (long int __numer, long int __denom)
     ;

# 784 "/usr/include/stdlib.h" 3 4
extern char *ecvt (double __value, int __ndigit, int * __decpt,
                   int * __sign) ;




extern char *fcvt (double __value, int __ndigit, int * __decpt,
                   int * __sign) ;




extern char *gcvt (double __value, int __ndigit, char *__buf) ;




extern char *qecvt (long double __value, int __ndigit,
                    int * __decpt, int * __sign) ;
extern char *qfcvt (long double __value, int __ndigit,
                    int * __decpt, int * __sign) ;
extern char *qgcvt (long double __value, int __ndigit, char *__buf) ;




extern int ecvt_r (double __value, int __ndigit, int * __decpt,
                   int * __sign, char * __buf,
                   size_t __len) ;
extern int fcvt_r (double __value, int __ndigit, int * __decpt,
                   int * __sign, char * __buf,
                   size_t __len) ;

extern int qecvt_r (long double __value, int __ndigit,
                    int * __decpt, int * __sign,
                    char * __buf, size_t __len) ;
extern int qfcvt_r (long double __value, int __ndigit,
                    int * __decpt, int * __sign,
                    char * __buf, size_t __len) ;







extern int mblen (const char *__s, size_t __n) ;


extern int mbtowc (wchar_t * __pwc,
                   const char * __s, size_t __n) ;


extern int wctomb (char *__s, wchar_t __wchar) ;



extern size_t mbstowcs (wchar_t * __pwcs,
                        const char * __s, size_t __n) ;

extern size_t wcstombs (char * __s,
                        const wchar_t * __pwcs, size_t __n)
     ;








extern int rpmatch (const char *__response) ;
# 916 "/usr/include/stdlib.h" 3 4
extern int getloadavg (double __loadavg[], int __nelem) ;






# 109 "/usr/include/freetype2/freetype/config/ftstdlib.h" 2
# 123 "/usr/include/freetype2/freetype/config/ftstdlib.h"
# 1 "/usr/include/setjmp.h" 1 3 4
# 28 "/usr/include/setjmp.h" 3 4


# 1 "/usr/include/bits/setjmp.h" 1 3 4
# 38 "/usr/include/bits/setjmp.h" 3 4
typedef int __jmp_buf[6];
# 31 "/usr/include/setjmp.h" 2 3 4
# 1 "/usr/include/bits/sigset.h" 1 3 4
# 32 "/usr/include/setjmp.h" 2 3 4




typedef struct __jmp_buf_tag
  {




    __jmp_buf __jmpbuf;
    int __mask_was_saved;
    __sigset_t __saved_mask;
  } jmp_buf[1];




extern int setjmp (jmp_buf __env) ;







extern int __sigsetjmp (struct __jmp_buf_tag __env[1], int __savemask) ;




extern int _setjmp (struct __jmp_buf_tag __env[1]) ;
# 76 "/usr/include/setjmp.h" 3 4




extern void longjmp (struct __jmp_buf_tag __env[1], int __val)
     ;







extern void _longjmp (struct __jmp_buf_tag __env[1], int __val)
     ;







typedef struct __jmp_buf_tag sigjmp_buf[1];
# 108 "/usr/include/setjmp.h" 3 4
extern void siglongjmp (sigjmp_buf __env, int __val)
     ;



# 124 "/usr/include/freetype2/freetype/config/ftstdlib.h" 2
# 44 "/usr/include/freetype2/freetype/config/ftconfig.h" 2



# 113 "/usr/include/freetype2/freetype/config/ftconfig.h"
  typedef signed short FT_Int16;
  typedef unsigned short FT_UInt16;



  typedef signed int FT_Int32;
  typedef unsigned int FT_UInt32;
# 134 "/usr/include/freetype2/freetype/config/ftconfig.h"
  typedef int FT_Fast;
  typedef unsigned int FT_UFast;
# 328 "/usr/include/freetype2/freetype/config/ftconfig.h"

# 52 "/usr/include/freetype2/freetype/freetype.h" 2
# 1 "/usr/include/freetype2/freetype/fterrors.h" 1
# 95 "/usr/include/freetype2/freetype/fterrors.h"
# 1 "/usr/include/freetype2/freetype/ftmoderr.h" 1
# 101 "/usr/include/freetype2/freetype/ftmoderr.h"
  enum {



  FT_Mod_Err_Base = 0,
  FT_Mod_Err_Autohint = 0,
  FT_Mod_Err_BDF = 0,
  FT_Mod_Err_Cache = 0,
  FT_Mod_Err_CFF = 0,
  FT_Mod_Err_CID = 0,
  FT_Mod_Err_Gzip = 0,
  FT_Mod_Err_PCF = 0,
  FT_Mod_Err_PFR = 0,
  FT_Mod_Err_PSaux = 0,
  FT_Mod_Err_PShinter = 0,
  FT_Mod_Err_PSnames = 0,
  FT_Mod_Err_Raster = 0,
  FT_Mod_Err_SFNT = 0,
  FT_Mod_Err_Smooth = 0,
  FT_Mod_Err_TrueType = 0,
  FT_Mod_Err_Type1 = 0,
  FT_Mod_Err_Type42 = 0,
  FT_Mod_Err_Winfonts = 0,



  FT_Mod_Err_Max };
# 96 "/usr/include/freetype2/freetype/fterrors.h" 2
# 167 "/usr/include/freetype2/freetype/fterrors.h"
  enum {




# 1 "/usr/include/freetype2/freetype/fterrdef.h" 1
# 34 "/usr/include/freetype2/freetype/fterrdef.h"
  FT_Err_Ok = 0x00,


  FT_Err_Cannot_Open_Resource = 0x01 + 0,

  FT_Err_Unknown_File_Format = 0x02 + 0,

  FT_Err_Invalid_File_Format = 0x03 + 0,

  FT_Err_Invalid_Version = 0x04 + 0,

  FT_Err_Lower_Module_Version = 0x05 + 0,

  FT_Err_Invalid_Argument = 0x06 + 0,

  FT_Err_Unimplemented_Feature = 0x07 + 0,

  FT_Err_Invalid_Table = 0x08 + 0,

  FT_Err_Invalid_Offset = 0x09 + 0,




  FT_Err_Invalid_Glyph_Index = 0x10 + 0,

  FT_Err_Invalid_Character_Code = 0x11 + 0,

  FT_Err_Invalid_Glyph_Format = 0x12 + 0,

  FT_Err_Cannot_Render_Glyph = 0x13 + 0,

  FT_Err_Invalid_Outline = 0x14 + 0,

  FT_Err_Invalid_Composite = 0x15 + 0,

  FT_Err_Too_Many_Hints = 0x16 + 0,

  FT_Err_Invalid_Pixel_Size = 0x17 + 0,




  FT_Err_Invalid_Handle = 0x20 + 0,

  FT_Err_Invalid_Library_Handle = 0x21 + 0,

  FT_Err_Invalid_Driver_Handle = 0x22 + 0,

  FT_Err_Invalid_Face_Handle = 0x23 + 0,

  FT_Err_Invalid_Size_Handle = 0x24 + 0,

  FT_Err_Invalid_Slot_Handle = 0x25 + 0,

  FT_Err_Invalid_CharMap_Handle = 0x26 + 0,

  FT_Err_Invalid_Cache_Handle = 0x27 + 0,

  FT_Err_Invalid_Stream_Handle = 0x28 + 0,




  FT_Err_Too_Many_Drivers = 0x30 + 0,

  FT_Err_Too_Many_Extensions = 0x31 + 0,




  FT_Err_Out_Of_Memory = 0x40 + 0,

  FT_Err_Unlisted_Object = 0x41 + 0,




  FT_Err_Cannot_Open_Stream = 0x51 + 0,

  FT_Err_Invalid_Stream_Seek = 0x52 + 0,

  FT_Err_Invalid_Stream_Skip = 0x53 + 0,

  FT_Err_Invalid_Stream_Read = 0x54 + 0,

  FT_Err_Invalid_Stream_Operation = 0x55 + 0,

  FT_Err_Invalid_Frame_Operation = 0x56 + 0,

  FT_Err_Nested_Frame_Access = 0x57 + 0,

  FT_Err_Invalid_Frame_Read = 0x58 + 0,




  FT_Err_Raster_Uninitialized = 0x60 + 0,

  FT_Err_Raster_Corrupted = 0x61 + 0,

  FT_Err_Raster_Overflow = 0x62 + 0,

  FT_Err_Raster_Negative_Height = 0x63 + 0,




  FT_Err_Too_Many_Caches = 0x70 + 0,




  FT_Err_Invalid_Opcode = 0x80 + 0,

  FT_Err_Too_Few_Arguments = 0x81 + 0,

  FT_Err_Stack_Overflow = 0x82 + 0,

  FT_Err_Code_Overflow = 0x83 + 0,

  FT_Err_Bad_Argument = 0x84 + 0,

  FT_Err_Divide_By_Zero = 0x85 + 0,

  FT_Err_Invalid_Reference = 0x86 + 0,

  FT_Err_Debug_OpCode = 0x87 + 0,

  FT_Err_ENDF_In_Exec_Stream = 0x88 + 0,

  FT_Err_Nested_DEFS = 0x89 + 0,

  FT_Err_Invalid_CodeRange = 0x8A + 0,

  FT_Err_Execution_Too_Long = 0x8B + 0,

  FT_Err_Too_Many_Function_Defs = 0x8C + 0,

  FT_Err_Too_Many_Instruction_Defs = 0x8D + 0,

  FT_Err_Table_Missing = 0x8E + 0,

  FT_Err_Horiz_Header_Missing = 0x8F + 0,

  FT_Err_Locations_Missing = 0x90 + 0,

  FT_Err_Name_Table_Missing = 0x91 + 0,

  FT_Err_CMap_Table_Missing = 0x92 + 0,

  FT_Err_Hmtx_Table_Missing = 0x93 + 0,

  FT_Err_Post_Table_Missing = 0x94 + 0,

  FT_Err_Invalid_Horiz_Metrics = 0x95 + 0,

  FT_Err_Invalid_CharMap_Format = 0x96 + 0,

  FT_Err_Invalid_PPem = 0x97 + 0,

  FT_Err_Invalid_Vert_Metrics = 0x98 + 0,

  FT_Err_Could_Not_Find_Context = 0x99 + 0,

  FT_Err_Invalid_Post_Table_Format = 0x9A + 0,

  FT_Err_Invalid_Post_Table = 0x9B + 0,




  FT_Err_Syntax_Error = 0xA0 + 0,

  FT_Err_Stack_Underflow = 0xA1 + 0,




  FT_Err_Missing_Startfont_Field = 0xB0 + 0,

  FT_Err_Missing_Font_Field = 0xB1 + 0,

  FT_Err_Missing_Size_Field = 0xB2 + 0,

  FT_Err_Missing_Chars_Field = 0xB3 + 0,

  FT_Err_Missing_Startchar_Field = 0xB4 + 0,

  FT_Err_Missing_Encoding_Field = 0xB5 + 0,

  FT_Err_Missing_Bbx_Field = 0xB6 + 0,
# 173 "/usr/include/freetype2/freetype/fterrors.h" 2



  FT_Err_Max };
# 53 "/usr/include/freetype2/freetype/freetype.h" 2
# 1 "/usr/include/freetype2/freetype/fttypes.h" 1
# 25 "/usr/include/freetype2/freetype/fttypes.h"
# 1 "/usr/include/freetype2/freetype/ftsystem.h" 1
# 26 "/usr/include/freetype2/freetype/ftsystem.h"

# 65 "/usr/include/freetype2/freetype/ftsystem.h"
  typedef struct FT_MemoryRec_* FT_Memory;
# 84 "/usr/include/freetype2/freetype/ftsystem.h"
  typedef void*
  (*FT_Alloc_Func)( FT_Memory memory,
                    long size );
# 102 "/usr/include/freetype2/freetype/ftsystem.h"
  typedef void
  (*FT_Free_Func)( FT_Memory memory,
                   void* block );
# 130 "/usr/include/freetype2/freetype/ftsystem.h"
  typedef void*
  (*FT_Realloc_Func)( FT_Memory memory,
                      long cur_size,
                      long new_size,
                      void* block );
# 154 "/usr/include/freetype2/freetype/ftsystem.h"
  struct FT_MemoryRec_
  {
    void* user;
    FT_Alloc_Func alloc;
    FT_Free_Func free;
    FT_Realloc_Func realloc;
  };
# 178 "/usr/include/freetype2/freetype/ftsystem.h"
  typedef struct FT_StreamRec_* FT_Stream;
# 190 "/usr/include/freetype2/freetype/ftsystem.h"
  typedef union FT_StreamDesc_
  {
    long value;
    void* pointer;

  } FT_StreamDesc;
# 222 "/usr/include/freetype2/freetype/ftsystem.h"
  typedef unsigned long
  (*FT_Stream_IoFunc)( FT_Stream stream,
                       unsigned long offset,
                       unsigned char* buffer,
                       unsigned long count );
# 240 "/usr/include/freetype2/freetype/ftsystem.h"
  typedef void
  (*FT_Stream_CloseFunc)( FT_Stream stream );
# 283 "/usr/include/freetype2/freetype/ftsystem.h"
  typedef struct FT_StreamRec_
  {
    unsigned char* base;
    unsigned long size;
    unsigned long pos;

    FT_StreamDesc descriptor;
    FT_StreamDesc pathname;
    FT_Stream_IoFunc read;
    FT_Stream_CloseFunc close;

    FT_Memory memory;
    unsigned char* cursor;
    unsigned char* limit;

  } FT_StreamRec;






# 26 "/usr/include/freetype2/freetype/fttypes.h" 2
# 1 "/usr/include/freetype2/freetype/ftimage.h" 1
# 37 "/usr/include/freetype2/freetype/ftimage.h"

# 59 "/usr/include/freetype2/freetype/ftimage.h"
  typedef signed long FT_Pos;
# 75 "/usr/include/freetype2/freetype/ftimage.h"
  typedef struct FT_Vector_
  {
    FT_Pos x;
    FT_Pos y;

  } FT_Vector;
# 102 "/usr/include/freetype2/freetype/ftimage.h"
  typedef struct FT_BBox_
  {
    FT_Pos xMin, yMin;
    FT_Pos xMax, yMax;

  } FT_BBox;
# 157 "/usr/include/freetype2/freetype/ftimage.h"
  typedef enum FT_Pixel_Mode_
  {
    FT_PIXEL_MODE_NONE = 0,
    FT_PIXEL_MODE_MONO,
    FT_PIXEL_MODE_GRAY,
    FT_PIXEL_MODE_GRAY2,
    FT_PIXEL_MODE_GRAY4,
    FT_PIXEL_MODE_LCD,
    FT_PIXEL_MODE_LCD_V,

    FT_PIXEL_MODE_MAX

  } FT_Pixel_Mode;
# 286 "/usr/include/freetype2/freetype/ftimage.h"
  typedef struct FT_Bitmap_
  {
    int rows;
    int width;
    int pitch;
    unsigned char* buffer;
    short num_grays;
    char pixel_mode;
    char palette_mode;
    void* palette;

  } FT_Bitmap;
# 344 "/usr/include/freetype2/freetype/ftimage.h"
  typedef struct FT_Outline_
  {
    short n_contours;
    short n_points;

    FT_Vector* points;
    char* tags;
    short* contours;

    int flags;

  } FT_Outline;
# 494 "/usr/include/freetype2/freetype/ftimage.h"
  typedef int
  (*FT_Outline_MoveToFunc)( FT_Vector* to,
                            void* user );
# 520 "/usr/include/freetype2/freetype/ftimage.h"
  typedef int
  (*FT_Outline_LineToFunc)( FT_Vector* to,
                            void* user );
# 550 "/usr/include/freetype2/freetype/ftimage.h"
  typedef int
  (*FT_Outline_ConicToFunc)( FT_Vector* control,
                             FT_Vector* to,
                             void* user );
# 581 "/usr/include/freetype2/freetype/ftimage.h"
  typedef int
  (*FT_Outline_CubicToFunc)( FT_Vector* control1,
                             FT_Vector* control2,
                             FT_Vector* to,
                             void* user );
# 626 "/usr/include/freetype2/freetype/ftimage.h"
  typedef struct FT_Outline_Funcs_
  {
    FT_Outline_MoveToFunc move_to;
    FT_Outline_LineToFunc line_to;
    FT_Outline_ConicToFunc conic_to;
    FT_Outline_CubicToFunc cubic_to;

    int shift;
    FT_Pos delta;

  } FT_Outline_Funcs;
# 711 "/usr/include/freetype2/freetype/ftimage.h"
  typedef enum FT_Glyph_Format_
  {
    FT_GLYPH_FORMAT_NONE = ( ( (unsigned long)0 << 24 ) | ( (unsigned long)0 << 16 ) | ( (unsigned long)0 << 8 ) | (unsigned long)0 ),

    FT_GLYPH_FORMAT_COMPOSITE = ( ( (unsigned long)'c' << 24 ) | ( (unsigned long)'o' << 16 ) | ( (unsigned long)'m' << 8 ) | (unsigned long)'p' ),
    FT_GLYPH_FORMAT_BITMAP = ( ( (unsigned long)'b' << 24 ) | ( (unsigned long)'i' << 16 ) | ( (unsigned long)'t' << 8 ) | (unsigned long)'s' ),
    FT_GLYPH_FORMAT_OUTLINE = ( ( (unsigned long)'o' << 24 ) | ( (unsigned long)'u' << 16 ) | ( (unsigned long)'t' << 8 ) | (unsigned long)'l' ),
    FT_GLYPH_FORMAT_PLOTTER = ( ( (unsigned long)'p' << 24 ) | ( (unsigned long)'l' << 16 ) | ( (unsigned long)'o' << 8 ) | (unsigned long)'t' )

  } FT_Glyph_Format;
# 795 "/usr/include/freetype2/freetype/ftimage.h"
  typedef struct FT_RasterRec_* FT_Raster;
# 824 "/usr/include/freetype2/freetype/ftimage.h"
  typedef struct FT_Span_
  {
    short x;
    unsigned short len;
    unsigned char coverage;

  } FT_Span;
# 869 "/usr/include/freetype2/freetype/ftimage.h"
  typedef void
  (*FT_SpanFunc)( int y,
                  int count,
                  FT_Span* spans,
                  void* user );
# 901 "/usr/include/freetype2/freetype/ftimage.h"
  typedef int
  (*FT_Raster_BitTest_Func)( int y,
                             int x,
                             void* user );
# 929 "/usr/include/freetype2/freetype/ftimage.h"
  typedef void
  (*FT_Raster_BitSet_Func)( int y,
                            int x,
                            void* user );
# 1037 "/usr/include/freetype2/freetype/ftimage.h"
  typedef struct FT_Raster_Params_
  {
    FT_Bitmap* target;
    void* source;
    int flags;
    FT_SpanFunc gray_spans;
    FT_SpanFunc black_spans;
    FT_Raster_BitTest_Func bit_test;
    FT_Raster_BitSet_Func bit_set;
    void* user;
    FT_BBox clip_box;

  } FT_Raster_Params;
# 1076 "/usr/include/freetype2/freetype/ftimage.h"
  typedef int
  (*FT_Raster_NewFunc)( void* memory,
                        FT_Raster* raster );
# 1093 "/usr/include/freetype2/freetype/ftimage.h"
  typedef void
  (*FT_Raster_DoneFunc)( FT_Raster raster );
# 1125 "/usr/include/freetype2/freetype/ftimage.h"
  typedef void
  (*FT_Raster_ResetFunc)( FT_Raster raster,
                          unsigned char* pool_base,
                          unsigned long pool_size );
# 1150 "/usr/include/freetype2/freetype/ftimage.h"
  typedef int
  (*FT_Raster_SetModeFunc)( FT_Raster raster,
                            unsigned long mode,
                            void* args );
# 1191 "/usr/include/freetype2/freetype/ftimage.h"
  typedef int
  (*FT_Raster_RenderFunc)( FT_Raster raster,
                           FT_Raster_Params* params );
# 1216 "/usr/include/freetype2/freetype/ftimage.h"
  typedef struct FT_Raster_Funcs_
  {
    FT_Glyph_Format glyph_format;
    FT_Raster_NewFunc raster_new;
    FT_Raster_ResetFunc raster_reset;
    FT_Raster_SetModeFunc raster_set_mode;
    FT_Raster_RenderFunc raster_render;
    FT_Raster_DoneFunc raster_done;

  } FT_Raster_Funcs;






# 27 "/usr/include/freetype2/freetype/fttypes.h" 2

# 1 "/usr/lib/gcc-lib/i386-redhat-linux/3.3.3/include/stddef.h" 1 3 4
# 29 "/usr/include/freetype2/freetype/fttypes.h" 2



# 97 "/usr/include/freetype2/freetype/fttypes.h"
  typedef unsigned char FT_Bool;
# 109 "/usr/include/freetype2/freetype/fttypes.h"
  typedef signed short FT_FWord;
# 121 "/usr/include/freetype2/freetype/fttypes.h"
  typedef unsigned short FT_UFWord;
# 132 "/usr/include/freetype2/freetype/fttypes.h"
  typedef signed char FT_Char;
# 143 "/usr/include/freetype2/freetype/fttypes.h"
  typedef unsigned char FT_Byte;
# 154 "/usr/include/freetype2/freetype/fttypes.h"
  typedef char FT_String;
# 165 "/usr/include/freetype2/freetype/fttypes.h"
  typedef signed short FT_Short;
# 176 "/usr/include/freetype2/freetype/fttypes.h"
  typedef unsigned short FT_UShort;
# 187 "/usr/include/freetype2/freetype/fttypes.h"
  typedef int FT_Int;
# 198 "/usr/include/freetype2/freetype/fttypes.h"
  typedef unsigned int FT_UInt;
# 209 "/usr/include/freetype2/freetype/fttypes.h"
  typedef signed long FT_Long;
# 220 "/usr/include/freetype2/freetype/fttypes.h"
  typedef unsigned long FT_ULong;
# 231 "/usr/include/freetype2/freetype/fttypes.h"
  typedef signed short FT_F2Dot14;
# 243 "/usr/include/freetype2/freetype/fttypes.h"
  typedef signed long FT_F26Dot6;
# 255 "/usr/include/freetype2/freetype/fttypes.h"
  typedef signed long FT_Fixed;
# 267 "/usr/include/freetype2/freetype/fttypes.h"
  typedef int FT_Error;
# 278 "/usr/include/freetype2/freetype/fttypes.h"
  typedef void* FT_Pointer;
# 291 "/usr/include/freetype2/freetype/fttypes.h"
  typedef size_t FT_Offset;
# 304 "/usr/include/freetype2/freetype/fttypes.h"
  typedef size_t FT_PtrDist;
# 321 "/usr/include/freetype2/freetype/fttypes.h"
  typedef struct FT_UnitVector_
  {
    FT_F2Dot14 x;
    FT_F2Dot14 y;

  } FT_UnitVector;
# 352 "/usr/include/freetype2/freetype/fttypes.h"
  typedef struct FT_Matrix_
  {
    FT_Fixed xx, xy;
    FT_Fixed yx, yy;

  } FT_Matrix;
# 373 "/usr/include/freetype2/freetype/fttypes.h"
  typedef struct FT_Data_
  {
    const FT_Byte* pointer;
    FT_Int length;

  } FT_Data;
# 395 "/usr/include/freetype2/freetype/fttypes.h"
  typedef void (*FT_Generic_Finalizer)(void* object);
# 426 "/usr/include/freetype2/freetype/fttypes.h"
  typedef struct FT_Generic_
  {
    void* data;
    FT_Generic_Finalizer finalizer;

  } FT_Generic;
# 481 "/usr/include/freetype2/freetype/fttypes.h"
  typedef struct FT_ListNodeRec_* FT_ListNode;
# 492 "/usr/include/freetype2/freetype/fttypes.h"
  typedef struct FT_ListRec_* FT_List;
# 510 "/usr/include/freetype2/freetype/fttypes.h"
  typedef struct FT_ListNodeRec_
  {
    FT_ListNode prev;
    FT_ListNode next;
    void* data;

  } FT_ListNodeRec;
# 533 "/usr/include/freetype2/freetype/fttypes.h"
  typedef struct FT_ListRec_
  {
    FT_ListNode head;
    FT_ListNode tail;

  } FT_ListRec;
# 553 "/usr/include/freetype2/freetype/fttypes.h"

# 54 "/usr/include/freetype2/freetype/freetype.h" 2



# 207 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_Glyph_Metrics_
  {
    FT_Pos width;
    FT_Pos height;

    FT_Pos horiBearingX;
    FT_Pos horiBearingY;
    FT_Pos horiAdvance;

    FT_Pos vertBearingX;
    FT_Pos vertBearingY;
    FT_Pos vertAdvance;

  } FT_Glyph_Metrics;
# 275 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_Bitmap_Size_
  {
    FT_Short height;
    FT_Short width;

    FT_Pos size;

    FT_Pos x_ppem;
    FT_Pos y_ppem;

  } FT_Bitmap_Size;
# 313 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_LibraryRec_ *FT_Library;
# 326 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_ModuleRec_* FT_Module;
# 338 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_DriverRec_* FT_Driver;
# 352 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_RendererRec_* FT_Renderer;
# 377 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_FaceRec_* FT_Face;
# 402 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_SizeRec_* FT_Size;
# 423 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_GlyphSlotRec_* FT_GlyphSlot;
# 455 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_CharMapRec_* FT_CharMap;
# 593 "/usr/include/freetype2/freetype/freetype.h"
  typedef enum FT_Encoding_
  {
    FT_ENCODING_NONE = ( ( (FT_UInt32)(0) << 24 ) | ( (FT_UInt32)(0) << 16 ) | ( (FT_UInt32)(0) << 8 ) | (FT_UInt32)(0) ),

    FT_ENCODING_MS_SYMBOL = ( ( (FT_UInt32)('s') << 24 ) | ( (FT_UInt32)('y') << 16 ) | ( (FT_UInt32)('m') << 8 ) | (FT_UInt32)('b') ),
    FT_ENCODING_UNICODE = ( ( (FT_UInt32)('u') << 24 ) | ( (FT_UInt32)('n') << 16 ) | ( (FT_UInt32)('i') << 8 ) | (FT_UInt32)('c') ),

    FT_ENCODING_SJIS = ( ( (FT_UInt32)('s') << 24 ) | ( (FT_UInt32)('j') << 16 ) | ( (FT_UInt32)('i') << 8 ) | (FT_UInt32)('s') ),
    FT_ENCODING_GB2312 = ( ( (FT_UInt32)('g') << 24 ) | ( (FT_UInt32)('b') << 16 ) | ( (FT_UInt32)(' ') << 8 ) | (FT_UInt32)(' ') ),
    FT_ENCODING_BIG5 = ( ( (FT_UInt32)('b') << 24 ) | ( (FT_UInt32)('i') << 16 ) | ( (FT_UInt32)('g') << 8 ) | (FT_UInt32)('5') ),
    FT_ENCODING_WANSUNG = ( ( (FT_UInt32)('w') << 24 ) | ( (FT_UInt32)('a') << 16 ) | ( (FT_UInt32)('n') << 8 ) | (FT_UInt32)('s') ),
    FT_ENCODING_JOHAB = ( ( (FT_UInt32)('j') << 24 ) | ( (FT_UInt32)('o') << 16 ) | ( (FT_UInt32)('h') << 8 ) | (FT_UInt32)('a') ),


    FT_ENCODING_MS_SJIS = FT_ENCODING_SJIS,
    FT_ENCODING_MS_GB2312 = FT_ENCODING_GB2312,
    FT_ENCODING_MS_BIG5 = FT_ENCODING_BIG5,
    FT_ENCODING_MS_WANSUNG = FT_ENCODING_WANSUNG,
    FT_ENCODING_MS_JOHAB = FT_ENCODING_JOHAB,

    FT_ENCODING_ADOBE_STANDARD = ( ( (FT_UInt32)('A') << 24 ) | ( (FT_UInt32)('D') << 16 ) | ( (FT_UInt32)('O') << 8 ) | (FT_UInt32)('B') ),
    FT_ENCODING_ADOBE_EXPERT = ( ( (FT_UInt32)('A') << 24 ) | ( (FT_UInt32)('D') << 16 ) | ( (FT_UInt32)('B') << 8 ) | (FT_UInt32)('E') ),
    FT_ENCODING_ADOBE_CUSTOM = ( ( (FT_UInt32)('A') << 24 ) | ( (FT_UInt32)('D') << 16 ) | ( (FT_UInt32)('B') << 8 ) | (FT_UInt32)('C') ),
    FT_ENCODING_ADOBE_LATIN_1 = ( ( (FT_UInt32)('l') << 24 ) | ( (FT_UInt32)('a') << 16 ) | ( (FT_UInt32)('t') << 8 ) | (FT_UInt32)('1') ),

    FT_ENCODING_OLD_LATIN_2 = ( ( (FT_UInt32)('l') << 24 ) | ( (FT_UInt32)('a') << 16 ) | ( (FT_UInt32)('t') << 8 ) | (FT_UInt32)('2') ),

    FT_ENCODING_APPLE_ROMAN = ( ( (FT_UInt32)('a') << 24 ) | ( (FT_UInt32)('r') << 16 ) | ( (FT_UInt32)('m') << 8 ) | (FT_UInt32)('n') )

  } FT_Encoding;
# 692 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_CharMapRec_
  {
    FT_Face face;
    FT_Encoding encoding;
    FT_UShort platform_id;
    FT_UShort encoding_id;

  } FT_CharMapRec;
# 723 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_Face_InternalRec_* FT_Face_Internal;
# 881 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_FaceRec_
  {
    FT_Long num_faces;
    FT_Long face_index;

    FT_Long face_flags;
    FT_Long style_flags;

    FT_Long num_glyphs;

    FT_String* family_name;
    FT_String* style_name;

    FT_Int num_fixed_sizes;
    FT_Bitmap_Size* available_sizes;

    FT_Int num_charmaps;
    FT_CharMap* charmaps;

    FT_Generic generic;


    FT_BBox bbox;

    FT_UShort units_per_EM;
    FT_Short ascender;
    FT_Short descender;
    FT_Short height;

    FT_Short max_advance_width;
    FT_Short max_advance_height;

    FT_Short underline_position;
    FT_Short underline_thickness;

    FT_GlyphSlot glyph;
    FT_Size size;
    FT_CharMap charmap;



    FT_Driver driver;
    FT_Memory memory;
    FT_Stream stream;

    FT_ListRec sizes_list;

    FT_Generic autohint;
    void* extensions;

    FT_Face_Internal internal;



  } FT_FaceRec;
# 1190 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_Size_InternalRec_* FT_Size_Internal;
# 1247 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_Size_Metrics_
  {
    FT_UShort x_ppem;
    FT_UShort y_ppem;

    FT_Fixed x_scale;
    FT_Fixed y_scale;

    FT_Pos ascender;
    FT_Pos descender;
    FT_Pos height;
    FT_Pos max_advance;

  } FT_Size_Metrics;
# 1282 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_SizeRec_
  {
    FT_Face face;
    FT_Generic generic;
    FT_Size_Metrics metrics;
    FT_Size_Internal internal;

  } FT_SizeRec;
# 1305 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_SubGlyphRec_* FT_SubGlyph;
# 1317 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_Slot_InternalRec_* FT_Slot_Internal;
# 1448 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_GlyphSlotRec_
  {
    FT_Library library;
    FT_Face face;
    FT_GlyphSlot next;
    FT_UInt reserved;
    FT_Generic generic;

    FT_Glyph_Metrics metrics;
    FT_Fixed linearHoriAdvance;
    FT_Fixed linearVertAdvance;
    FT_Vector advance;

    FT_Glyph_Format format;

    FT_Bitmap bitmap;
    FT_Int bitmap_left;
    FT_Int bitmap_top;

    FT_Outline outline;

    FT_UInt num_subglyphs;
    FT_SubGlyph subglyphs;

    void* control_data;
    long control_len;

    void* other;

    FT_Slot_Internal internal;

  } FT_GlyphSlotRec;
# 1506 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_Init_FreeType( FT_Library *alibrary );
# 1539 "/usr/include/freetype2/freetype/freetype.h"
  extern void
  FT_Library_Version( FT_Library library,
                      FT_Int *amajor,
                      FT_Int *aminor,
                      FT_Int *apatch );
# 1561 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_Done_FreeType( FT_Library library );
# 1630 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_Parameter_
  {
    FT_ULong tag;
    FT_Pointer data;

  } FT_Parameter;
# 1690 "/usr/include/freetype2/freetype/freetype.h"
  typedef struct FT_Open_Args_
  {
    FT_UInt flags;
    const FT_Byte* memory_base;
    FT_Long memory_size;
    FT_String* pathname;
    FT_Stream stream;
    FT_Module driver;
    FT_Int num_params;
    FT_Parameter* params;

  } FT_Open_Args;
# 1741 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_New_Face( FT_Library library,
               const char* filepathname,
               FT_Long face_index,
               FT_Face *aface );
# 1789 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_New_Memory_Face( FT_Library library,
                      const FT_Byte* file_base,
                      FT_Long file_size,
                      FT_Long face_index,
                      FT_Face *aface );
# 1833 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_Open_Face( FT_Library library,
                const FT_Open_Args* args,
                FT_Long face_index,
                FT_Face *aface );
# 1872 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_Attach_File( FT_Face face,
                  const char* filepathname );
# 1904 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_Attach_Stream( FT_Face face,
                    FT_Open_Args* parameters );
# 1924 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_Done_Face( FT_Face face );
# 1962 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_Set_Char_Size( FT_Face face,
                    FT_F26Dot6 char_width,
                    FT_F26Dot6 char_height,
                    FT_UInt horz_resolution,
                    FT_UInt vert_resolution );
# 2013 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_Set_Pixel_Sizes( FT_Face face,
                      FT_UInt pixel_width,
                      FT_UInt pixel_height );
# 2053 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_Load_Glyph( FT_Face face,
                 FT_UInt glyph_index,
                 FT_Int32 load_flags );
# 2098 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_Load_Char( FT_Face face,
                FT_ULong char_code,
                FT_Int32 load_flags );
# 2310 "/usr/include/freetype2/freetype/freetype.h"
  extern void
  FT_Set_Transform( FT_Face face,
                    FT_Matrix* matrix,
                    FT_Vector* delta );
# 2363 "/usr/include/freetype2/freetype/freetype.h"
  typedef enum FT_Render_Mode_
  {
    FT_RENDER_MODE_NORMAL = 0,
    FT_RENDER_MODE_LIGHT,
    FT_RENDER_MODE_MONO,
    FT_RENDER_MODE_LCD,
    FT_RENDER_MODE_LCD_V,

    FT_RENDER_MODE_MAX

  } FT_Render_Mode;
# 2415 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_Render_Glyph( FT_GlyphSlot slot,
                   FT_Render_Mode render_mode );
# 2439 "/usr/include/freetype2/freetype/freetype.h"
  typedef enum FT_Kerning_Mode_
  {
    FT_KERNING_DEFAULT = 0,
    FT_KERNING_UNFITTED,
    FT_KERNING_UNSCALED

  } FT_Kerning_Mode;
# 2517 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_Get_Kerning( FT_Face face,
                  FT_UInt left_glyph,
                  FT_UInt right_glyph,
                  FT_UInt kern_mode,
                  FT_Vector *akerning );
# 2561 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_Get_Glyph_Name( FT_Face face,
                     FT_UInt glyph_index,
                     FT_Pointer buffer,
                     FT_UInt buffer_max );
# 2587 "/usr/include/freetype2/freetype/freetype.h"
  extern const char*
  FT_Get_Postscript_Name( FT_Face face );
# 2613 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_Select_Charmap( FT_Face face,
                     FT_Encoding encoding );
# 2641 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Error
  FT_Set_Charmap( FT_Face face,
                  FT_CharMap charmap );
# 2669 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_UInt
  FT_Get_Char_Index( FT_Face face,
                     FT_ULong charcode );
# 2717 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_ULong
  FT_Get_First_Char( FT_Face face,
                     FT_UInt *agindex );
# 2751 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_ULong
  FT_Get_Next_Char( FT_Face face,
                    FT_ULong char_code,
                    FT_UInt *agindex );
# 2774 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_UInt
  FT_Get_Name_Index( FT_Face face,
                     FT_String* glyph_name );
# 2832 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Long
  FT_MulDiv( FT_Long a,
             FT_Long b,
             FT_Long c );
# 2867 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Long
  FT_MulFix( FT_Long a,
             FT_Long b );
# 2895 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Long
  FT_DivFix( FT_Long a,
             FT_Long b );
# 2914 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Fixed
  FT_RoundFix( FT_Fixed a );
# 2933 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Fixed
  FT_CeilFix( FT_Fixed a );
# 2952 "/usr/include/freetype2/freetype/freetype.h"
  extern FT_Fixed
  FT_FloorFix( FT_Fixed a );
# 2973 "/usr/include/freetype2/freetype/freetype.h"
  extern void
  FT_Vector_Transform( FT_Vector* vec,
                       FT_Matrix* matrix );






# 492 "cairo.h" 2

cairo_font_t *
cairo_ft_font_create (FT_Library ft_library, FcPattern *pattern);

cairo_font_t *
cairo_ft_font_create_for_ft_face (FT_Face face);

void
cairo_ft_font_destroy (cairo_font_t *ft_font);

FT_Face
cairo_ft_font_face (cairo_font_t *ft_font);

FcPattern *
cairo_ft_font_pattern (cairo_font_t *ft_font);




void
cairo_show_surface (cairo_t *cr,
                    cairo_surface_t *surface,
                    int width,
                    int height);
# 525 "cairo.h"
cairo_operator_t
cairo_current_operator (cairo_t *cr);

void
cairo_current_rgb_color (cairo_t *cr, double *red, double *green, double *blue);
cairo_pattern_t *
cairo_current_pattern (cairo_t *cr);

double
cairo_current_alpha (cairo_t *cr);



double
cairo_current_tolerance (cairo_t *cr);

void
cairo_current_point (cairo_t *cr, double *x, double *y);

cairo_fill_rule_t
cairo_current_fill_rule (cairo_t *cr);

double
cairo_current_line_width (cairo_t *cr);

cairo_line_cap_t
cairo_current_line_cap (cairo_t *cr);

cairo_line_join_t
cairo_current_line_join (cairo_t *cr);

double
cairo_current_miter_limit (cairo_t *cr);



void
cairo_current_matrix (cairo_t *cr, cairo_matrix_t *matrix);



cairo_surface_t *
cairo_current_target_surface (cairo_t *cr);

typedef void (cairo_move_to_func_t) (void *closure,
                                     double x, double y);

typedef void (cairo_line_to_func_t) (void *closure,
                                     double x, double y);

typedef void (cairo_curve_to_func_t) (void *closure,
                                      double x1, double y1,
                                      double x2, double y2,
                                      double x3, double y3);

typedef void (cairo_close_path_func_t) (void *closure);

extern void
cairo_current_path (cairo_t *cr,
                    cairo_move_to_func_t *move_to,
                    cairo_line_to_func_t *line_to,
                    cairo_curve_to_func_t *curve_to,
                    cairo_close_path_func_t *close_path,
                    void *closure);

extern void
cairo_current_path_flat (cairo_t *cr,
                         cairo_move_to_func_t *move_to,
                         cairo_line_to_func_t *line_to,
                         cairo_close_path_func_t *close_path,
                         void *closure);



typedef enum cairo_status {
    CAIRO_STATUS_SUCCESS = 0,
    CAIRO_STATUS_NO_MEMORY,
    CAIRO_STATUS_INVALID_RESTORE,
    CAIRO_STATUS_INVALID_POP_GROUP,
    CAIRO_STATUS_NO_CURRENT_POINT,
    CAIRO_STATUS_INVALID_MATRIX,
    CAIRO_STATUS_NO_TARGET_SURFACE,
    CAIRO_STATUS_NULL_POINTER
} cairo_status_t;

cairo_status_t
cairo_status (cairo_t *cr);

const char *
cairo_status_string (cairo_t *cr);




cairo_surface_t *
cairo_surface_create_for_image (char *data,
                                cairo_format_t format,
                                int width,
                                int height,
                                int stride);



cairo_surface_t *
cairo_surface_create_similar (cairo_surface_t *other,
                              cairo_format_t format,
                              int width,
                              int height);

void
cairo_surface_reference (cairo_surface_t *surface);

void
cairo_surface_destroy (cairo_surface_t *surface);




cairo_status_t
cairo_surface_set_repeat (cairo_surface_t *surface, int repeat);


cairo_status_t
cairo_surface_set_matrix (cairo_surface_t *surface, cairo_matrix_t *matrix);


cairo_status_t
cairo_surface_get_matrix (cairo_surface_t *surface, cairo_matrix_t *matrix);

typedef enum {
    CAIRO_FILTER_FAST,
    CAIRO_FILTER_GOOD,
    CAIRO_FILTER_BEST,
    CAIRO_FILTER_NEAREST,
    CAIRO_FILTER_BILINEAR,
    CAIRO_FILTER_GAUSSIAN
} cairo_filter_t;


cairo_status_t
cairo_surface_set_filter (cairo_surface_t *surface, cairo_filter_t filter);

cairo_filter_t
cairo_surface_get_filter (cairo_surface_t *surface);



cairo_surface_t *
cairo_image_surface_create (cairo_format_t format,
                            int width,
                            int height);

cairo_surface_t *
cairo_image_surface_create_for_data (char *data,
                                     cairo_format_t format,
                                     int width,
                                     int height,
                                     int stride);


cairo_pattern_t *
cairo_pattern_create_for_surface (cairo_surface_t *surface);

cairo_pattern_t *
cairo_pattern_create_linear (double x0, double y0,
                             double x1, double y1);

cairo_pattern_t *
cairo_pattern_create_radial (double cx0, double cy0, double radius0,
                             double cx1, double cy1, double radius1);

void
cairo_pattern_reference (cairo_pattern_t *pattern);

void
cairo_pattern_destroy (cairo_pattern_t *pattern);

cairo_status_t
cairo_pattern_add_color_stop (cairo_pattern_t *pattern,
                              double offset,
                              double red, double green, double blue,
                              double alpha);

cairo_status_t
cairo_pattern_set_matrix (cairo_pattern_t *pattern, cairo_matrix_t *matrix);

cairo_status_t
cairo_pattern_get_matrix (cairo_pattern_t *pattern, cairo_matrix_t *matrix);

typedef enum {
    CAIRO_EXTEND_NONE,
    CAIRO_EXTEND_REPEAT,
    CAIRO_EXTEND_REFLECT
} cairo_extend_t;

cairo_status_t
cairo_pattern_set_extend (cairo_pattern_t *pattern, cairo_extend_t extend);

cairo_extend_t
cairo_pattern_get_extend (cairo_pattern_t *pattern);

cairo_status_t
cairo_pattern_set_filter (cairo_pattern_t *pattern, cairo_filter_t filter);

cairo_filter_t
cairo_pattern_get_filter (cairo_pattern_t *pattern);





cairo_surface_t *
cairo_ps_surface_create (FILE *file,
                         double width_inches,
                         double height_inches,
                         double x_pixels_per_inch,
                         double y_pixels_per_inch);







cairo_surface_t *
cairo_png_surface_create (FILE *file,
                          cairo_format_t format,
                          int width,
                          int height);
# 764 "cairo.h"
cairo_surface_t *
cairo_xlib_surface_create (Display *dpy,
                           Drawable drawable,
                           Visual *visual,
                           cairo_format_t format,
                           Colormap colormap);
# 789 "cairo.h"
cairo_matrix_t *
cairo_matrix_create (void);

void
cairo_matrix_destroy (cairo_matrix_t *matrix);

cairo_status_t
cairo_matrix_copy (cairo_matrix_t *matrix, const cairo_matrix_t *other);

cairo_status_t
cairo_matrix_set_identity (cairo_matrix_t *matrix);

cairo_status_t
cairo_matrix_set_affine (cairo_matrix_t *cr,
                         double a, double b,
                         double c, double d,
                         double tx, double ty);

cairo_status_t
cairo_matrix_get_affine (cairo_matrix_t *matrix,
                         double *a, double *b,
                         double *c, double *d,
                         double *tx, double *ty);

cairo_status_t
cairo_matrix_translate (cairo_matrix_t *matrix, double tx, double ty);

cairo_status_t
cairo_matrix_scale (cairo_matrix_t *matrix, double sx, double sy);

cairo_status_t
cairo_matrix_rotate (cairo_matrix_t *matrix, double radians);

cairo_status_t
cairo_matrix_invert (cairo_matrix_t *matrix);

cairo_status_t
cairo_matrix_multiply (cairo_matrix_t *result, const cairo_matrix_t *a, const cairo_matrix_t *b);

cairo_status_t
cairo_matrix_transform_distance (cairo_matrix_t *matrix, double *dx, double *dy);

cairo_status_t
cairo_matrix_transform_point (cairo_matrix_t *matrix, double *x, double *y);
