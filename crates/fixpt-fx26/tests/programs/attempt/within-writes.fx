;; ! an `attempt`'s body may be stopped half way
;; `attempt-within`'s body, as `attempt`'s, must do nothing another could see.
(define x (ref int @x) (new 0))
(attempt-within 100 (begin (set x 1) 1) (lambda ((m string)) 2) (lambda () 3))
