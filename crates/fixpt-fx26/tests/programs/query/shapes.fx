;;; How a procedure holds a type, `t`, for `fixpt query`'s `returns`,
;;; `consumes` and `uses` (`docs/fx26.md`, "Queries"): one of each shape,
;;; as the customer given it sees it.
(define-type t (productof (v int)))
(define-type other (productof (w int)))

;; Makes one; takes one; transforms one.
(define* make (subr pure () t) (lambda () (product (v 1))))
(define* take (subr pure (t) unit) (lambda (x) #u))
(define* step (subr pure (t) t) (lambda (x) x))
;; Takes a maker of them: the customer makes each.
(define* drain (subr pure ((subr pure () t)) unit) (lambda (f) #u))
;; Gives the customer's callback a maker, which needs nothing.
(define* lend (subr pure ((subr pure ((subr pure () t)) unit)) unit)
  (lambda (k) (k (lambda () (product (v 1))))))
;; Gives the customer's callback a transformer, which needs one.
(define* lend-step (subr pure ((subr pure ((subr pure (t) t)) unit)) unit)
  (lambda (k) (k (lambda (x) x))))
;; Gives the customer's callback a maker and a taker: it may pass what the
;; one makes to the other, and needs nothing to get one.
(define* lend-both
  (subr pure ((subr pure ((subr pure () t) (subr pure (t) unit)) unit)) unit)
  (lambda (k) (k (lambda () (product (v 1))) (lambda (x) #u))))
;; Mentions only another type.
(define* unrelated (subr pure (other) other) (lambda (x) x))
