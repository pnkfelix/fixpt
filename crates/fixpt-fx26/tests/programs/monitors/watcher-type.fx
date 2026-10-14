;; ! a watcher is a process's address, `(addr M R)`, and this is a int
;; Refused: a watcher that is no address.
(define w (addr int @w)
  (spawn-monitored 7 (lambda ((m string)) 0) (box int r) (begin (receive box) #u)))
