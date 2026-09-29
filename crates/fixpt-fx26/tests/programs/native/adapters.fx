;;; Conversions between the conventions (`docs/research/native-conventions.md`):
;;; a procedure given where one of the other convention is expected is
;;; converted, by an adapter that calls it, and a procedure of the other
;;; convention is called as through `fx`. Run with either convention the
;;; program's, each form as the REPL runs it.
(define inc (subr pure (int) int) (lambda (x) (+ x 1)))
(define n (subr (conv native) pure (int) int) inc)
(define c (subr (conv cellular) pure (int) int) inc)
(define call-n (subr pure ((subr (conv native) pure (int) int)) int) (lambda (f) (f 1)))
(define call-c (subr pure ((subr (conv cellular) pure (int) int)) int) (lambda (f) (f 1)))
(call-n n)
(call-n inc)
(call-c c)
(call-c inc)
((convention native inc) 5)
((convention cellular n) 6)
(define twice (subr pure ((subr (conv fx) pure (int) int) int) int) (lambda (f x) (f (f x))))
(twice n 10)
(twice c 20)
;; Standard operations as values, in either convention.
(define m (subr pure ((subr pure (int int) int) int) int) (lambda (k x) (k x 3)))
(m * 5)
(define app2 (subr (alloc @heap) ((subr (alloc @heap) (int (listof int @heap)) (pairof int (listof int @heap) @heap)) int) (pairof int (listof int @heap) @heap)) (lambda (k x) (k x (cons x nil))))
(app2 cons 7)
;; Native and cellular frames in turn, 300 deep, allocating.
(define* down (subr (maxeff spin (alloc @heap) (read @globals)) (int) (listof int @heap)) (lambda (k) nil))
(define down-n (subr (conv native) (maxeff spin (alloc @heap) (read @globals)) (int) (listof int @heap)) (lambda (k) (down k)))
(define down-c (subr (conv cellular) (maxeff spin (alloc @heap) (read @globals)) (int) (listof int @heap)) (lambda (k) (down-n k)))
(define* down (subr (maxeff spin (alloc @heap) (read @globals)) (int) (listof int @heap)) (lambda (k) (if (= k 0) nil (cons k (down-c (- k 1))))))
(down 3)
(define len (subr (maxeff spin (read @heap) (read @globals)) ((listof int @heap)) int) (lambda (xs) (if (null? xs) 0 (+ 1 (len (cdr xs))))))
(len (down 300))
