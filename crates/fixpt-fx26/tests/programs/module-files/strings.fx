"A module file whose top-level forms include strings: comments, as in a
module's items (`docs/fx26.md`, Modules)."
(define base int 40)
"Between two definitions."
(hide "Inside a hide." (define secret int 1))
(define answer int (+ base secret))
"Last."
