;; A functor, a dependent procedure, whose result's type is made of its
;; argument's twice; and a module to apply it to. For
;; `checker::a_call_through_the_top_level_keeps_its_latent_effect`.
(define-type elt-sig (moduleof (abs t type) (val v t)))
(define double
  (subr (alloc @heap) ((e : elt-sig))
        (moduleof (desc t (productof (1 (select e t)) (2 (select e t)))) (val v t)))
  (lambda ((e elt-sig))
    (module
      (define-type t (productof (1 (select e t)) (2 (select e t))))
      (define v t (product (1 (with e v)) (2 (with e v)))))))
(define m0 (module (define-type t int) (define v t 0)))
