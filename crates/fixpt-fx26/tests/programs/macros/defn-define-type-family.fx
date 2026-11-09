;; => 2
;; A family the template defines, its parameter in scope in its body.
(define-syntax define-pair-list
  (-> (bvar) defn)
  (syntax-rules ()
    ((_ name) (begin (define-type (box (a type)) (listof a)) (define name (box int) (list 1 2))))))
(define-pair-list xs)
(length xs)
