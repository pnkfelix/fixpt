;; => 1
;; What a nested use defines, as its macro's signature says (`(defn …)`):
;; the template's `x` is the one `define-const` made, not the top level's.
(define-syntax define-const
  (macro (bvar expr) (defn (A var)))
  (syntax-rules
    ((_ n e) (define n e))))
(define-syntax define-via
  (macro (bvar) defn)
  (syntax-rules
    ((_ name) (begin (define-const x 1) (define name x)))))
(define x 100)
(define-via y)
y
