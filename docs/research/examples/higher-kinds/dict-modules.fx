;; => #t
;; "Dictionary passing over modules": today's syntax only, no new kinds.
;;
;; `bag-of` is a module type generic in the element type `a` (ordinary
;; `define-type` with a parameter). Its abstract component `c` stands for
;; "the container type applied to `a`", but `c` itself is never a
;; first-class type-level function: each concrete container is a separate
;; `poly`/`plambda` ("functor", in FX-26's sense: a procedure a caller
;; applies, not Sheldon's dependent-procedure functor) that, given `a`,
;; returns a module whose `c` happens to be whatever that container's real
;; representation is.
(define-type (bag-of (a type))
  (moduleof (abs c type)
            (val empty c)
            (val insert (subr pure (c a) c))
            (val size (subr pure (c) int))))

;; Concrete container #1: a list.
(define list-bags
  (poly ((a type)) (subr pure () (bag-of a)))
  (plambda ((a type))
    (lambda ()
      (module
        (define-type c (listof a acyclic))
        (define empty c nil)
        (define insert (subr pure (c a) c) (lambda (xs x) (cons x xs)))
        (define size (subr pure (c) int) (lambda (xs) (list-length xs)))))))

;; Concrete container #2: just a count, discarding the values entirely.
;; Its `c` is an `int`, nothing like a list -- `use-bag` below cannot tell.
(define count-bags
  (poly ((a type)) (subr pure () (bag-of a)))
  (plambda ((a type))
    (lambda ()
      (module
        (define-type c int)
        (define empty c 0)
        (define insert (subr pure (c a) c) (lambda (n x) (+ n 1)))
        (define size (subr pure (c) int) (lambda (n) n))))))

;; Generic in BOTH the element type `a` (via `poly`/`plambda`, first-order,
;; already native to FX-26) AND the choice of container (via an ordinary
;; higher-order value parameter `make`, whose result's abstract type is
;; opaque inside `with`). This is the whole of what the interim buys: no
;; type built from `(f a)` can be written down, only `with`'s view of
;; whatever operations the module bundles.
(define use-bag
  (poly ((a type))
    (subr pure ((subr pure () (bag-of a)) a a) int))
  (plambda ((a type))
    (lambda (make x y)
      (let ((b (make)))
        (with b (size (insert (insert empty x) y)))))))

(= ((proj use-bag int) (proj list-bags int) 10 20)
   ((proj use-bag int) (proj count-bags int) 10 20))
