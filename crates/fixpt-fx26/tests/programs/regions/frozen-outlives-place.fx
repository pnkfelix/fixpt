; Rejected: data frozen into an arena won't outlive the arena, so it cannot
; leave it.
(letrena a (letfreeze (r a) (the (listof int r) (rcons a 1 nil))))
