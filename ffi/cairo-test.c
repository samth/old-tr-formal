#include <cairo.h>
#include <stdio.h>

#define WIDTH 40
#define HEIGHT 40

int
main (void)
{
    cairo_t *xrs, *cr;
    FILE *file;

    file = fopen ("sample.png","w");

    xrs = cairo_create ();

    cairo_set_target_png (xrs, file,
			  CAIRO_FORMAT_ARGB32,
			  WIDTH,
			  HEIGHT);

    cairo_move_to (xrs, 0.0, 0.0);
    cairo_line_to (xrs, 40.0, 40.0);
    cairo_stroke (xrs);

    cairo_destroy (xrs);

    fclose (file);

    file = fopen("fill2.png", "w");
    cr = cairo_create();
    cairo_set_target_png (xrs, file,
			  CAIRO_FORMAT_ARGB32,
			  100,
			  100);

    cairo_move_to (cr, 50, 10);
    cairo_line_to (cr, 90, 90);
    cairo_rel_line_to (cr, -40, 0.0);
    cairo_curve_to (cr, 20, 90, 20, 50, 50, 50);
    
    cairo_save (cr);
    cairo_set_rgb_color (cr, 0, 0, 1);
    cairo_fill (cr);
    cairo_restore (cr);
    
    cairo_close_path (cr);
    cairo_stroke (cr);

    cairo_destroy (cr);

    fclose (file);

    return 0;
}
