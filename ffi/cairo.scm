(require (lib "foreign.ss"))

(unsafe!)

(define libpixman (ffi-lib "libcairo"))

(define-syntax defcairo-full
  (syntax-rules (:)
    [(_ nm : ty ...)
     (define nm
       (get-ffi-obj (regexp-replaces 'nm '((#rx"-" "_") (#rx"^" "cairo_")))  libpixman (_fun ty ...)))]))

(define-syntax defcairo
  (syntax-rules (: ->)
    [(_ nm : in ... -> ret)
     (defcairo-full nm : _cairo in ... -> ret)]
    [(_ nm) (defcairo-full nm : _cairo -> _void)]
    [(_ nm : in ...)
     (defcairo-full nm : _cairo in ... -> _void)]))

(define-cpointer-type _FILE)

(define-cpointer-type _cairo)
(define-cpointer-type _cairo_surface)
(define-cpointer-type _cairo_matrix)
(define-cpointer-type _cairo_pattern)

(define _format
  (_enum '(format-argb32
           format-rgb24
           format-a8
           format-a1)))

(define _operator
  (_enum '(operator-clear
           operator-src
           operator-dst
           operator-over
           operator-over-reverse
           operator-in
           operator-in-reverse
           operator-out
           operator-out-reverse
           operator-atop
           operator-atop-reverse
           operator-xor
           operator-add
           operator-saturate)))

(defcairo-full create : -> _cairo)
(defcairo reference)
(defcairo destroy)
(defcairo save)
(defcairo restore)

(defcairo-full copy : _cairo _cairo -> _void)

(defcairo set-target-surface : _cairo )

(defcairo set-target-image : _bytes _format _int _int _int)

(defcairo set-target-ps : _FILE _double _double _double _double)

;(defcairo set-target-png : _FILE _format _int _int)

(defcairo set-operator : _operator)

(defcairo set-rgb-color : _double _double _double)

(defcairo set-pattern : _cairo_pattern)

(defcairo set-alpha : _double)

(defcairo set-tolerance : _double)

(define _fill_rule (_enum '(fill-rule-winding fill-rule-even-odd)))

(defcairo set-fill-rule : _fill_rule)

(defcairo set-line-width : _double)

(define _line_cap (_enum '(line-cap-butt line-cap-round line-cap-square)))

(defcairo set-line-cap : _line_cap)

(define _line_join (_enum '(line-join-miter line-join-round line-join-bevel)))

(defcairo set-line-join : _line_join)

(defcairo set-dash : (_ptr i _double) _int _double)

(defcairo set-miter-limit : _double)

(defcairo translate : _double _double)

(defcairo rotate : _double)

(defcairo concat-matrix : _cairo_matrix)

; (defcairo set-matrix : _cairo_matrix)

; (defcairo default-matrix)

; (defcairo identity-matrix)

; (defcairo transform-point : (_ptr i _double) (_ptr i _double))

; (defcairo transform-distance : (_ptr i _double) (_ptr i _double))

; (defcairo inverse-transform-point : (_ptr i _double) (_ptr i _double))

; (defcairo inverse-transform-distance : (_ptr i _double) (_ptr i _double))

(defcairo new-path)

(defcairo move-to : _double _double)

(defcairo line-to : _double _double)

(defcairo curve-to : _double _double _double _double _double _double)

(defcairo arc : _double _double _double _double _double)

(defcairo arc-negative : _double _double _double _double _double)

(defcairo rel-move-to : _double _double)

(defcairo rel-line-to : _double _double)

(defcairo rel-curve-to : _double _double _double _double)

(defcairo rectangle : _double _double _double _double)

(defcairo close-path)

(defcairo stroke)

(defcairo fill)

(defcairo show-page)

(defcairo copy-page)

(defcairo in-stroke : _double _double -> _bool)

(defcairo in-fill : _double _double -> _bool)

(defcairo init-clip)

(defcairo clip)

(defcairo stroke-extents )
