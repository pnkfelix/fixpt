;;; Probe: can an identity table be frozen, and then looked up?
;;; The table is built at region `r` inside a `letfreeze`, so it leaves
;;; at `const`; its keys are at `@k`, which stays writable. A lookup on
;;; the frozen table then reads `const` (pure) and writes `@k`.
;;; At run time the lookup may still rehash the table after a collection,
;;; relinking its entries: a write to an object the types call frozen
;;; (`docs/research/sets-and-maps.md` §3.2).
(define-type key (pairof int int @k))
(define* frozen-table (subr (maxeff (alloc @k) (write @k)) (key key) (eqtable key int @k const))
  (lambda (a b)
    (letfreeze r
      (let ((t (the (eqtable key int @k r) (make-eqtable (pair-identity)))))
        (begin (eqtable-set! t a 1) (eqtable-set! t b 2) t)))))
(define a key (cons 1 1))
(define b key (cons 2 2))
(define t (eqtable key int @k const) (frozen-table a b))
(+ (eqtable-ref t a 0) (eqtable-ref t b 0))
