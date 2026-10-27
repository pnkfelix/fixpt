;;; `fixpt query`'s `effect` and `mutates` (`docs/fx26.md`, "Queries"): a
;;; counter at `@ed`, and procedures that write it, may, or do not.
(define-type counter (productof (count (ref int @ed)) (name string)))
(define c counter (product (count (new 0)) (name "keys")))

;; Writes `@ed` itself.
(define* bump! (subr (maxeff (read @ed) (write @ed)) (counter) unit)
  (lambda (k) (set (extract k count) (+ (get (extract k count)) 1))))
;; Writes whatever region it is given: `@ed` once instantiated so.
(define* clear! (poly ((r region)) (subr (write r) ((ref int r)) unit))
  (plambda ((r region)) (lambda (x) (set x 0))))
;; Takes a counter and gives back a procedure that writes it.
(define* bumper (subr pure (counter) (subr (maxeff (read @ed) (write @ed) (read @globals)) () unit))
  (lambda (k) (lambda () (bump! k))))
;; Reads it only.
(define* count-of (subr (read @ed) (counter) int) (lambda (k) (get (extract k count))))
;; Writes another region.
(define other (ref int @elsewhere) (new 0))
(define* poke! (subr (write @elsewhere) (counter) unit) (lambda (k) (set other 1)))

;; `clear!` at `@ed`, bound to a local name; and only called, unnamed.
(define* reset! (subr (write @ed) (counter) unit)
  (lambda (k) (let ((wipe (proj clear! @ed))) (wipe (extract k count)))))
(define* zero! (subr (write @ed) (counter) unit) (lambda (k) (clear! (extract k count))))
;; Any type's identity, bound to a local name at `counter`.
(define* same (poly ((a type)) (subr pure (a) a)) (plambda ((a type)) (lambda (x) x)))
(define* again (subr pure (counter) counter)
  (lambda (k) (let ((keep (proj same counter))) (keep k))))
