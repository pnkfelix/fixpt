;;; What a set former and a quantifier come to without syntax for them.
;;; SETL's   {x*x : x in s | odd(x)}   and   exists x in s | x > 3
;;; (the second binding its witness). Here over the sorted sets of
;;; sorted-set.fx, with the former's result re-sorted by `adjoin`.
(define-type iset (listof int acyclic))
(define adjoin (subr pure (int iset) iset)
  (lambda (x s)
    (letrec ((go (subr pure (iset) iset)
               (lambda (s)
                 (cond ((null? s) (cons x s))
                       ((= x (car s)) s)
                       ((< x (car s)) (cons x s))
                       (else (cons (car s) (go (cdr s))))))))
      (go s))))
(define former
  (poly ((e effect))
    (subr (maxeff e (read (globals adjoin))) ((subr e (int) int) (subr e (int) bool) iset) iset))
  (lambda (f p s)
    (letrec ((go (subr (maxeff e (read (globals adjoin))) (iset iset) iset)
               (lambda (s out)
                 (cond ((null? s) out)
                       ((p (car s)) (go (cdr s) (adjoin (f (car s)) out)))
                       (else (go (cdr s) out))))))
      (go s (list)))))
;; `exists` with its witness: the witness comes back in a sum, since
;; FX-26 has no binding that outlives the test.
(define exists
  (poly ((e effect))
    (subr e ((subr e (int) bool) iset) (sumof (found int) (none unit))))
  (lambda (p s)
    (letrec ((go (subr e (iset) (sumof (found int) (none unit)))
               (lambda (s)
                 (cond ((null? s) (sum none #u))
                       ((p (car s)) (sum found (car s)))
                       (else (go (cdr s)))))))
      (go s))))
(define s iset (list 1 2 3 4 5 6 7))
(list (former (lambda (x) (* x x)) (lambda (x) (= (modulo x 2) 1)) s)
      (tagcase (exists (lambda (x) (> x 3)) s)
        (found x (the iset (list x)))
        (none u (the iset (list)))))
