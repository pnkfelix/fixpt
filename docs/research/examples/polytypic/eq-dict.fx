;;; Equality by dictionary passing: Hinze's polykinded type, by hand.
;;; A type with a type parameter takes the parameter's equality as an
;;; argument (ppx_deriving's "an argument for every type variable").
;;; One copy of list=? serves every element type.
(define int=? (subr pure (int int) bool) (lambda (x y) (= x y)))
(define list=?
  (poly ((t type) (e effect))
    (subr e ((subr e (t t) bool) (listof t acyclic) (listof t acyclic)) bool))
  (lambda (eq xs ys)
    (letrec ((go (subr e ((listof t acyclic) (listof t acyclic)) bool)
               (lambda (xs ys)
                 (cond ((null? xs) (null? ys))
                       ((null? ys) #f)
                       (else (and (eq (car xs) (car ys)) (go (cdr xs) (cdr ys))))))))
      (go xs ys))))
;; Equality at (listof (listof int)) is built by applying, not by copying.
(define ints (listof int acyclic) (cons 1 (cons 2 nil)))
(define lists (listof (listof int acyclic) acyclic) (cons ints (cons ints nil)))
(list=? (lambda (a b) (list=? int=? a b)) lists lists)
