;; => 7
;; A template's `+`, the top level's, the standard one, not the use's own
;; `+`.
(define-syntax plus-one (expr)
  (syntax-rules ()
    ((_ e) (+ e 1))))
(let ((+ (lambda ((a int) (b int)) (* a b)))) (plus-one 6))
