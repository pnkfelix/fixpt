;; ! `inner` gives more than this names of it: a `modnames` seals a module's own names, not yet those of one inside it; name all of `inner`'s here, or seal it where it is defined
;; A module inside is not sealed to fewer names yet.
(define outer (module (define inner (module (define a int 1) (define b int 2))) (define y int 3)))
(define s (modnames (modnames inner a) y) outer)
