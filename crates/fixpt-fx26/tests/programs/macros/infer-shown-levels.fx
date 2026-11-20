;; ! inferred: (macro (_ a @ bvar expr b @ bvar e2 @ expr body @ (many expr)) (defn a b) (bind a a in e2)
;; A refused signature inferred whose parts are in scope of two levels each, shown in one
;; `bind` each, its levels outermost first.
(define-syntax define-both
  (syntax-rules
    ((_ a e b e2 body)
     (begin (define a e) (define b (let ((a 1)) e2)) (define c (list body (let ((a 1)) body)))))))
(define-both x 1 y 2 3)
