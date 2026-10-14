;; ! a monitor's `on-failure` makes the watcher's message of a failure's
;; Refused: `on-failure` makes an int where the watcher takes a report.
(define-type report (sumof (ok int) (failed string)))
(define collector (addr report @p) (spawn (box report r) (begin (receive box) #u)))
(define w (addr int @w)
  (spawn-monitored collector (lambda ((m string)) 0) (box int r) (begin (receive box) #u)))
