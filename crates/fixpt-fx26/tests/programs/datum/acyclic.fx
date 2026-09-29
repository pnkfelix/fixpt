;;; `acyclic`: frozen data found to have no cycle is `acyclic`, and a walk of
;;; it needs no `spin`; data frozen with a cycle takes the other branch.
(define len (subr pure ((listof int acyclic) int) int)
  (letrec ((len (subr pure ((listof int acyclic) int) int)
             (lambda (xs n) (if (null? xs) n (len (cdr xs) (+ n 1))))))
    len))
(define ring (subr pure (int) (listof int const))
  (lambda (n)
    (letfreeze r
      ;; cons-chain: built in r, then frozen
      (let ((ys (the (listof int r) (cons 1 (cons 2 nil)))))
        (begin (set-cdr! (cdr ys) ys) ys)))))
(define line (subr pure (int) (listof int const))
  (lambda (n)
    (letfreeze r
      ;; cons-chain: built in r, then frozen
      (let ((ys (the (listof int r) (cons 1 (cons 2 nil)))))
        (begin (set-car! ys n) ys)))))
(define* count (subr pure ((listof int const)) int) (lambda (xs) (acyclic xs (ok (len ok 0)) -1)))
(+ (* 100 (count (line 5))) (count (ring 5)))
