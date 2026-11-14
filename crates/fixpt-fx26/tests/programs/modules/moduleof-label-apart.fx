;; => 5
;; A component labelled `t` beside an outer `t`: its binder named apart, so
;; that the module type can say both (`typed-macros.md`, "a `moduleof`'s
;; label and binder written apart").
(define-type t int)
(define-type sig (moduleof (abs #:t inner type)
                           (val wrap (subr pure (t) inner))
                           (val get (subr pure (inner) t))))
(define m sig
  (module (define-generative t int #:seal mk #:unseal un)
          (define wrap (subr pure (int) t) mk)
          (define get (subr pure (t) int) un)))
(define x (select m t) ((with m wrap) 5))
((with m get) x)
