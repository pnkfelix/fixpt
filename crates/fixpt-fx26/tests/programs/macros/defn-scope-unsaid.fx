;; ! `e2` is placed in the scope of `a`, but its signature says it is in no scope of the pattern's
;; The second definition's expression is in the scope of the first's name,
;; which a use gives: the signature must say so.
(define-syntax define-both
  (macro (_ bvar expr bvar expr) defn)
  (syntax-rules
    ((_ a e1 b e2) (begin (define a e1) (define b e2)))))
(define-both a 3 b 4)
