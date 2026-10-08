;; => 15
;; A file of parameters is a `plambda` over them of a `lambda` making the
;; module: two calls, two counts (`module-files/tally-twice.fx`).
(define make (proj (load-module "../module-files/tally-twice.fx") @q @q))
(define a (make))
(define b (make))
(define a-twice (with a tick-twice))
(define b-tick (with b tick))
(begin (a-twice) (a-twice) (+ (* 10 (b-tick)) ((with a tick))))
