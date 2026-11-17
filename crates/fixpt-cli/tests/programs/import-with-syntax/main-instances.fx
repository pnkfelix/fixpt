;; Two instances of `counter.fx`, the macros of each imported: each names
;; its own instance, a binder `a` at a use capturing nothing, `tick-once`
;; and `tick-ten` of `b`'s its own; `as-tally` reads `(select a tally)`.
;; a: 3 3 100 100, then 10 taken off again; b: 2, then 10: (206 12 5).
(define a ((proj (load-module "counter.fx") @globals)))
(define b ((proj (load-module "counter.fx") @globals)))
(import-with-syntax a (except tick-ten))
(import-with-syntax b (only tick-ten))
(tick-twice 3)
(let ((a 100)) (tick-twice a))
(with b (tick 2))
(list (+ (tick 0) (- (with a (tick 10)) (with a (tick 0)))) (tick-ten) (as-tally 5))
