(require (lib "foreign.ss"))

(define libpixman (ffi-lib "libpixman"))

(define-syntax defpx
  (syntax-rules (:)
    [(_ nm : ty ...)
     (define nm
       (get-ffi-obj (regexp-replaces 'nm '((#rx"-" "_") (#rx"^" "pixman_")))  libpixman (_fun ty ...)))]))

(define-syntax defpxst
  (syntax-rules (:)
    [(_ nm : in ...)
     (defpx nm : (out : (_ptr o _region16)) in ... -> _region_status -> out)]))


(define-cpointer-type _region16)

(define _short _uint16)

(define-cstruct _box16 ((x1 _short)
                        (y1 _short)
                        (x2 _short)
                        (y2 _short)))

(define _region_status
  (_enum '(REGION_STATUS_FAILURE
           REGION_STATUS_SUCCESS)))

(define r16 _region16)

(defpx region-create : -> _region16)
(defpx region-create-simple : _box16-pointer -> _region16)
(defpx region-destroy : _region16 -> _void)
(defpx region-translate : _region16 _int _int -> _void)
(defpxst region-copy : _region16)
(defpxst region-intersect : r16 r16)
(defpxst region-union : r16 r16)
(defpxst region-union-rect : r16 _int _int _uint _uint)
(defpxst region-subtract : r16 r16)
(defpxst region-inverse : r16 r16)

(define r (region-create))