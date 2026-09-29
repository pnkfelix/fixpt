;;; An abstract type, in FX-26 today: a generative type. Only `up-counter`
;;; and `down-counter` see that a counter is an int.

;;; ---- counter.fx ----
(define-generative counter int)
(define zero counter (up-counter 0))
(define* incr (subr pure (counter) counter) (lambda (c) (up-counter (+ (down-counter c) 1))))
(define* value (subr pure (counter) int) (lambda (c) (down-counter c)))

;;; ---- client.fx ----
(define* three (subr pure () int) (lambda () (value (incr (incr (incr zero))))))
(three)                                   ; 3
;; Accepted today, since every global is visible: nothing yet stops a
;; client from using the conversions. An export list would.
(down-counter zero)                       ; 0
