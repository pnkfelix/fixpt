;; => 7
;; A template's module type, its abstract type labelled `t`, given a use's
;; type that is the use's own `t`: not captured, its binder renamed.
(define-type t int)
(define-syntax counter-sig
  (-> (type) type)
  (syntax-rules
    ((_ elem) (moduleof (abs #:t t type) (val #:empty t) (val #:add (subr pure (elem t) t))
                        (val #:size (subr pure (t) int))))))
(define m (counter-sig t)
  (module (define-generative t int #:seal mk #:unseal un)
          (define empty t (mk 0))
          (define add (subr pure (int t) t) (lambda (x c) (mk (+ x (un c)))))
          (define size (subr pure (t) int) (lambda (c) (un c)))))
((with m size) ((with m add) 7 (with m empty)))
