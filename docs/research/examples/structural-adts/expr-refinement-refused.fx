;;; Refused today: the GADT step. `is-zero` builds only booleans, but
;;; nothing in the type says so, and an arm learns nothing about `a`: the
;;; checker wants an `a` and sees a `bool`. Guards (the note's proposal)
;;; would let the arm know `a = bool`.
(define-type (expr (a type))
  (sumof (lit a)
         (is-zero (expr int))
         (if-e (productof (c (expr bool)) (t (expr a)) (f (expr a))))))
(define* ev (poly ((a type)) (subr spin ((expr a)) a))
  (lambda (e)
    (tagcase e
      (lit x x)
      (is-zero x (= (ev x) 0))
      (if-e (c t f) (if (ev c) (ev t) (ev f))))))
