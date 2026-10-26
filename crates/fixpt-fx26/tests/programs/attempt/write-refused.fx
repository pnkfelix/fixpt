;; ! an `attempt`'s body may be stopped half way
;; Refused: the body writes a reference others can see, which a failure
;; half way would leave half done.
(define x (ref int @x) (new 0))
(attempt (begin (set x 1) 1) (lambda ((m string)) 2))
