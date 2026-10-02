;; A module's items that name a global, `secret`, which a module read from
;; a file cannot see: it sees only the standard environment.
(define x int (+ secret 1))
