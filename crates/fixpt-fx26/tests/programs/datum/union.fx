;;; `datum` is a union (TODO §51): atoms, pairs of datums at `acyclic`,
;;; vectors and bytevectors. Made with `cons` and taken apart by `typecase`
;;; and the shape predicates; a walk through `car` and `cdr` needs no
;;; `spin`, its pairs being acyclic.
(define d datum (list 1 'a "b" #\c #t 2.5))
(define size (subr pure (datum) int)
  (letrec ((size (subr pure (datum) int)
             (lambda (x)
               (typecase x
                 (pair p (+ (size (car p)) (size (cdr p))))
                 (nil n 0)
                 (int i i)
                 (f64 f 100)
                 (string s 1000)
                 (vector v 10000)
                 (else e 1)))))
    size))
(define v datum (datum-list->vector d))
(+ (size d) (size (cons v (cons nil nil))))
