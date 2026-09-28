;;; Users of users run again: `g` uses `f` (at any type), `h` uses `g`; after
;;; `f` changes type, both still check, and both are defined again.
(define f int 1)
(define g int (let ((x f)) 2))
(define h int (* g 10))
(define f string "s")
h
