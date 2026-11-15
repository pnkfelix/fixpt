;; ! a template's `define-syntax` defines a `syntax-rules` macro: a procedural one's transformer is phase 1's code, not yet in a template
;; A procedural macro's definition in a template.
(define-syntax def-proc
  (-> (bvar) defn)
  (syntax-rules
    ((_ name) (define-syntax name (er-macro-transformer (lambda (f r c) 1))))))
