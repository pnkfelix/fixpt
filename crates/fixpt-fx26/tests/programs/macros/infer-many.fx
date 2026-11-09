;; => (1 2)
;; An expression placed twice: `(many expr)`, inferred, so it runs twice.
(define-syntax both
  (syntax-rules ()
    ((_ e) (list e e))))
(let ((c (new 0)))
  (both (begin (set c (+ (get c) 1)) (get c))))
