;;; FX-26 today: a "functor dictionary" -- a container's `fmap` operation,
;;; passed as a value, in place of quantifying over the container itself
;;; (which would need a kind `type -> type`; see ../../higher-kinds.md).
;;; Each concrete container builds its own dictionary; `apply-mapper` is
;;; written once and takes whichever dictionary it is given.
;;;
;;; What this buys: no copy of `apply-mapper` per container (the user's
;;; preference, `dictionary-passing-over-specialization.md`).
;;; What it does NOT buy: nothing ties `fb` to "the same container as
;;; `fa`, applied to `b`". `fa` and `fb` are two independent type
;;; variables, not `(f a)` and `(f b)` for one `f`, so a `mapper` value
;;; could be (mis)built pairing a list with an unrelated `fb`; only the
;;; dictionary's author keeps that promise, not the checker.

(define-type (mapper (a type) (b type) (fa type) (fb type) (e effect))
  (productof (fmap (subr e ((subr e (a) b) fa) fb))))

;; A container's own builder: lists.
(define list-mapper
  (poly ((a type) (b type) (e effect))
    (mapper a b (listof a acyclic) (listof b acyclic) e))
  (plambda ((a type) (b type) (e effect))
    (product
     (fmap (lambda (f xs)
             (letrec ((go (subr e ((listof a acyclic)) (listof b acyclic))
                        (lambda (xs) (if (null? xs) nil (cons (f (car xs)) (go (cdr xs)))))))
               (go xs)))))))

;; A second, unrelated container: an option built from today's sums.
(define-type (option (t type)) (sumof (none unit) (some t)))
(define option-mapper
  (poly ((a type) (b type) (e effect))
    (mapper a b (option a) (option b) e))
  (plambda ((a type) (b type) (e effect))
    (product
     (fmap (lambda (f ox)
             (tagcase ox (none u (sum none u)) (some x (sum some (f x)))))))))

;; The consumer: written once, works for whichever dictionary it is given.
(define apply-mapper
  (poly ((a type) (b type) (fa type) (fb type) (e effect))
    (subr e ((mapper a b fa fb e) (subr e (a) b) fa) fb))
  (lambda (d f xs) ((extract d fmap) f xs)))

(define xs (listof int acyclic) (list 1 2 3))
(define ox (option int) (sum some 5))
(apply-mapper (proj list-mapper int int pure) (lambda (n) (+ n 1)) xs)
(apply-mapper (proj option-mapper int int pure) (lambda (n) (+ n 1)) ox)
