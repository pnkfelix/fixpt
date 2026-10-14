;; ! `race`'s branches interfere: one has (receive r) and another (receive r)
;; Refused: two branches that receive from one mailbox, where the loser
;; stopped half way could have taken a message.
(define w (addr int @p) (spawn (box int r) (begin (race (receive box) (receive box)) #u)))
