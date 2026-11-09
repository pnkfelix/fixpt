;; => #t
;; An inferred signature, as hygienic as a written one: the template's `t`
;; against the use's.
(define-syntax my-or
  (syntax-rules ()
    ((_ a b) (let ((t a)) (if t t b)))))
(let ((t #t)) (my-or #f t))
