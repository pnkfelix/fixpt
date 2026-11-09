;; ! is a procedural macro, whose binding structure no signature says: not in a template
;; A `syntax-rules` template may not use a procedural macro: its signature
;; could not say what the use binds.
(define-syntax id
  (er-macro-transformer (lambda (form rename compare) (car (cdr form)))))
(define-syntax wrap (syntax-rules () ((_ e) (id e))))
(wrap 1)
