;;; Hiding what a module does, in FX-26 today: the client is polymorphic in
;;; the effect of the operations it is given (option d of section 2.3).

;;; ---- tally.fx ----
(define-type (tally-ops (e effect)) (productof (tick (subr e () int))))
(private-regions @tally)
(define count (ref int @tally) (new 0))
(define* tick (subr (maxeff (read @tally) (write @tally)) () int)
  (lambda () (begin (set count (+ (get count) 1)) (get count))))

;;; ---- client.fx : never names @tally ----
(define tick-twice (poly ((e effect)) (subr e ((tally-ops e)) int))
  (plambda ((e effect)) (lambda (m) (begin ((extract m tick)) ((extract m tick))))))

;;; ---- main.fx : links the two by application ----
(tick-twice (product (tick tick)))        ; 2
