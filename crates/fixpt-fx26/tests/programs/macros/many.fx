;; => (1 2)
;; `(many expr)`: placed twice, and run twice, as the signature says it may.
(define-syntax both
  ;; As named: ((e (many expr)))
  ((many expr))
  (syntax-rules ()
    ((_ e) (list e e))))
(let ((c (new 0)))
  (both (begin (set c (+ (get c) 1)) (get c))))
