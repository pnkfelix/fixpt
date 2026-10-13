;;; `f64`s returned raw (TODO.md §91): `half` returns its `f64` raw to a
;;; caller that takes it so (`term`'s `f64+`, itself returning raw) and
;;; boxed to one that keeps the value (`halves`, in a list); `pick`, polymorphic, returns a boxed
;;; `f64` to a caller that takes it raw; `felem` returns a flat array's
;;; `f64` element raw, `ielem` an `i64` flat array's as its value; `deep`
;;; returns raw through the stack cache's overflows and underflows.
(define-type fvec (flatarrayof f64 @heap))
(define-type ivec (flatarrayof i64 @heap))
(define* half (subr pure (int) f64)
  (lambda (n) (f64* (int->f64 n) .5)))
(define pick (poly ((t type)) (subr pure (bool t t) t))
  (plambda ((t type)) (lambda (b x y) (if b x y))))
(define felem (subr (read @heap) (fvec int) f64)
  (lambda (v i) (flatarray-ref v i)))
(define ielem (subr (read @heap) (ivec int) i64)
  (lambda (v i) (flatarray-ref v i)))
(define* term (subr (read (globals half pick)) (int) f64)
  (lambda (n) (f64+ (half n) ((proj pick f64) (= 0 (remainder n 2)) 1. 2.))))
(define* total (subr (maxeff spin (read (globals term half pick))) (int f64) f64)
  (lambda (n acc) (if (= n 0) acc (total (- n 1) (f64+ acc (term n))))))
(define* halves (subr (maxeff (alloc @heap) spin (read (globals half))) (int) (listof f64 @heap))
  (lambda (n) (if (= n 0) nil (cons (half n) (halves (- n 1))))))
(define* deep (subr (maxeff (alloc @heap) (read @heap) spin (read (globals half))) (int) f64)
  (lambda (n)
    (if (= n 0)
        0.
        (let ((junk (the (listof int @heap) (cons n nil))))
          (f64+ (half (car junk)) (deep (- n 1)))))))
(define* flats (subr (maxeff (alloc @heap) (read @heap) (read (globals felem ielem))) () int)
  (lambda ()
    (let ((fv (the fvec (make-flatarray (f64-flat) 4 2.5)))
          (iv (the ivec (make-flatarray (i64-flat) 4 (int->i64 7)))))
      (+ (f64->int (f64-truncate (f64* 2. (felem fv 1)))) (i64->int (ielem iv 2))))))
(define* raw-returns
  (subr (maxeff (alloc @heap) (read @heap) spin
                (read (globals total term halves deep flats felem ielem half pick)))
        (int) int)
  (lambda (n)
    (+ (f64->int (f64-truncate (total n 0.)))
       (+ (f64->int (f64-truncate (car (halves 9))))
          (+ (f64->int (f64-truncate (deep n))) (flats))))))
(raw-returns 3000)
