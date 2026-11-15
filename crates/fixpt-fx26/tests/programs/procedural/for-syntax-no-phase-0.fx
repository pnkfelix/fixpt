;; ! `begin-for-syntax`
;; Nor is the program's phase 1's: its forms see the standard environment.
(define zero int 0)
(begin-for-syntax (define one int (+ zero 1)))
