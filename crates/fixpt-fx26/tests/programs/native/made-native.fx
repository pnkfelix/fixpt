;;; In a program whose convention is native, every closure cellular code
;;; makes is a native one (`nclosure`), as its type says: here, where the
;;; native compiler declines (`stay-cellular`), a closure a procedure gives
;;; back, a `letrec`'s, whose siblings are patched in, and a standard
;;; operation as a value, a closure in a list, a place's closures (in that
;;; place). Each then called by native code.
(define make-adder (subr spin (int) (subr pure (int) int))
  (lambda (n) (stay-cellular (lambda (x) (+ x n)))))
(define add5 (subr pure (int) int) (make-adder 5))
(define even (subr spin (int) bool)
  (stay-cellular
   (letrec ((ev (subr spin (int) bool) (lambda (k) (if (= k 0) #t (od (- k 1)))))
            (od (subr spin (int) bool) (lambda (k) (if (= k 0) #f (ev (- k 1))))))
     ev)))
(define plus (subr pure (int int) int) (stay-cellular +))
;; A place's closures (`rlambda`), each with its adapter in the same place,
;; a reap, which its collections copy: a `letrec`'s, patched through them.
(define in-place (subr spin (int) int)
  (lambda (n)
    (stay-cellular
     (letreap r
       (letrec ((upto (subr (maxeff (alloc r) (read r) spin) (int (listof int r)) (listof int r))
                  (rlambda r (i acc) (if (= i 0) acc (upto (- i 1) (rcons r i acc)))))
                (total (subr (maxeff (read r) spin) ((listof int r) int) int)
                  (rlambda r (xs acc) (if (null? xs) acc (total (cdr xs) (+ acc (car xs)))))))
         (total (upto n nil) 0))))))
;; One in a list, which no definition's compiling sees.
(define fns (listof (subr pure (int) int) @heap) (stay-cellular (cons (lambda (x) (* x 2)) nil)))
(add5 10)
(even 10)
(plus 2 3)
((car fns) 21)
(in-place 1000)
