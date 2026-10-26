;; ! an `attempt`'s body may be stopped half way
;; Refused: the body does I/O.
(attempt (write-out "hi") (lambda ((m string)) (sum done #u)))
