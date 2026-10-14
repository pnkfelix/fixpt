;; ! nondet
;; Messages from two senders arrive in an order of their own: a process that
;; receives is `nondet`, and so is making one, which no mask removes.
(define* start (subr (alloc @w) () (addr int @w))
  (lambda () (spawn (box int p) (begin (receive box) #u))))
