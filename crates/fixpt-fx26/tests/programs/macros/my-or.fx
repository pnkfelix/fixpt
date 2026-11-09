;; => #t
;; The template's `t` against the use's: `(my-or #f t)` is the use's `t`.
(define-syntax my-or
  ;; As named: ((a expr) (b expr))
  (expr expr)
  (syntax-rules ()
    ((_ a b) (let ((t a)) (if t t b)))))
(let ((t #t)) (my-or #f t))
