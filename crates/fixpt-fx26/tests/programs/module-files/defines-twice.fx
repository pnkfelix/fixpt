;; A module's file that defines a type twice: refused, at its start.
(define-type t int)
(define-type t bool)
(define x t #t)
