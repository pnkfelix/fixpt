;; => (4 0)
;; A template's `tagcase`: its tags keywords, its arms' binders its own.
(define-type opt (sumof (some int) (none unit)))
(define-syntax or-zero
  ;; As named: ((e expr))
  (expr)
  ((_ e) (tagcase e (#:some v v) (#:none u 0))))
(list (or-zero (the opt (sum some 4))) (or-zero (the opt (sum none #u))))
