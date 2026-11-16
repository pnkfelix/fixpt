;; ! inferred: (macro (_ a @ bvar expr body @ (many expr)) (defn a) (bind a in body))
;; A refused signature inferred, shown in shapes and facts: what a use defines, `(defn a)`.
(define-syntax define-twice
  (syntax-rules
    ((_ a e body) (begin (define a e) (define c (list body (let ((a 1)) body)))))))
(define-twice x 1 2)
