;; Two processes send to one mailbox when a third tells them to: which
;; arrives first is a choice of the schedule's, and the receiver keeps the
;; order it saw. What `nondet` says of a process that receives.
(define log (icell (listof int acyclic) @l) (make-icell))
(define sink (addr int @s)
  (spawn (box int p)
    (let* ((a (receive box)) (b (receive box)))
      (icell-put! log (the (listof int acyclic) (list a b))))))
(define one (addr unit @t) (spawn (box unit p) (begin (receive box) (send sink 1))))
(define two (addr unit @t) (spawn (box unit p) (begin (receive box) (send sink 2))))
(define starter (addr unit @u)
  (spawn (box unit p) (begin (receive box) (send one #u) (send two #u))))
(send starter #u)
(icell-get log)
