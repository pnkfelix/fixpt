;; => 1
;; Macros that make definitions, inferred: what each defines of what its
;; uses give, its export, which a template using it sees.
(define-syntax define-const
  (syntax-rules ()
    ((_ n e) (define n e))))
(define-syntax define-via
  (syntax-rules ()
    ((_ name) (begin (define-const x 1) (define name x)))))
(define x 100)
(define-via y)
y
