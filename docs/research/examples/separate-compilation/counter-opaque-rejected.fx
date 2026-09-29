;;; Rejected, as it should be: outside its conversions, a counter is not
;;; an int, in whichever file the client is.

;;; ---- counter.fx ----
(define-generative counter int)
(define zero counter (up-counter 0))

;;; ---- client.fx ----
(+ zero 1)
