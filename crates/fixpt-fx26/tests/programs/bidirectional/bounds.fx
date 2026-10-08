; Local type inference with bounds from both sides (`TODO.md` §66): where a
; union with `int` in it is expected of `(array-ref a i)`, `a` an `(arrayof
; int @r)`, the expected type bounds `array-ref`'s element type from above
; and `a` fixes it, invariant inside the array: `int`, which the union then
; takes. The same of a reference's `get`, and of a pair's `car`.
(define-type v (union int string))
(define a (arrayof int @r) (make-array 3 7))
(define c (ref int @r) (new 5))
(define p (pairof int nil @r) (cons 30 nil))
(define* from-array (subr (read @r) (int) v) (lambda (i) (array-ref a i)))
(define* from-ref (subr (read @r) () v) (lambda () (get c)))
(define* from-pair (subr (read @r) () v) (lambda () (car p)))
(define* as-int (subr pure (v) int) (lambda (x) (typecase x (int n n) (else 0))))
(+ (as-int (from-array 0)) (+ (as-int (from-ref)) (as-int (from-pair))))
