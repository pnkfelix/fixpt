;;; Effects and regions in what a client sees, in FX-26 today. The module
;;; keeps its state in a region of its own; its procedure's type says so.

;;; ---- tally.fx ----
(private-regions @tally)
(define count (ref int @tally) (new 0))
(define* tick (subr (maxeff (read @tally) (write @tally)) () int)
  (lambda () (begin (set count (+ (get count) 1)) (get count))))

;;; ---- client.fx : names the module's region, since tick's type does ----
(define* tick-twice (subr (maxeff (read @tally) (write @tally)) () int)
  (lambda () (begin (tick) (tick))))
(tick-twice)                              ; 2
