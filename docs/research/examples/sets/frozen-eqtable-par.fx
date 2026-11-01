;;; Refused: two `par` branches looking up the frozen table of
;;; frozen-eqtable.fx. Each lookup writes the keys' region, @k, so the
;;; branches interfere. That write is why the run-time rehash of a
;;; table at `const` (`sets-and-maps.md` §3.2) cannot race today.
(define-type key (pairof int int @k))
(define* frozen-table (subr (maxeff (alloc @k) (write @k)) (key key) (eqtable key int @k const))
  (lambda (a b)
    (letfreeze r
      (let ((t (the (eqtable key int @k r) (make-eqtable (pair-identity)))))
        (begin (eqtable-set! t a 1) (eqtable-set! t b 2) t)))))
(define a key (cons 1 1))
(define b key (cons 2 2))
(define t (eqtable key int @k const) (frozen-table a b))
(par ((x (eqtable-ref t a 0)) (y (eqtable-ref t b 0))) (+ x y))
