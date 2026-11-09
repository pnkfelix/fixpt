;; ! `e2` is placed in the scope of other bindings than its signature says
;; The second definition's expression is in the scope of the first's name,
;; which a use gives: the signature must say so.
(define-syntax define-both
  (-> (bvar expr bvar expr) defn)
  (syntax-rules ()
    ((_ a e1 b e2) (begin (define a e1) (define b e2)))))
(define-both a 3 b 4)
