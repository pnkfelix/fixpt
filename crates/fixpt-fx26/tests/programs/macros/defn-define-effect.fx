;; => 4
;; An effect the template defines, made fresh, named in a type.
(define-syntax define-quiet
  (macro (bvar) defn)
  (syntax-rules
    ((_ name) (begin (define-effect calm pure) (define name (subr calm () int) (lambda () 4))))))
(define-quiet four)
(four)
