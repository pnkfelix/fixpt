;; The client's and the load's procedures, from their `.fasl`s, on one
;; counter: 2, then 3.
(define counters (load-module "counter.fx"))
(define client (load-module "client.fx"))
(define c ((with counters make-counter)))
(let* ((a ((with client bump-twice!) c)) (b ((with counters bump!) c)))
  (int->string (+ (* 10 a) b)))
