;; => (2 2 3 4)
;; A path, `a::b::c` (TODO.md §296): `(with (with a b) c)` where a value is,
;; `(select (with a b) c)` where a type is, each name of the module before
;; it; at an operator too.
(define make
  (lambda ()
    (module
      (define-generative t int #:seal up #:unseal down)
      (define zero t (up 0))
      (define inc (subr pure (t) t) (lambda (c) (up (+ (down c) 1))))
      (define value (subr pure (t) int) (lambda (c) (down c))))))
(define mid (module (define a (make)) (define b 2) (define add (lambda ((x int)) (+ x 2)))))
(define bump (lambda ((x mid::a::t)) (mid::a::inc x)))
(define one mid::a::t (bump mid::a::zero))
(list (mid::a::value (bump one)) mid::b (mid::add 1) (mid::add mid::b))
