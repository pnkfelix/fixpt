;; => 3
;; A label and binder the use gives, `(abs name type)`: the use's, both.
(define-syntax box-sig
  (-> (dvar type) type)
  (syntax-rules
    ((_ name elem) (moduleof (abs name type)
                             (val #:get (subr pure (name) elem))
                             (val #:make (subr pure (elem) name))))))
(define m (box-sig b int)
  (module (define-generative b int #:seal mk #:unseal un)
          (define get (subr pure (b) int) un)
          (define make (subr pure (int) b) mk)))
(define v (select m b) ((with m make) 3))
((with m get) v)
