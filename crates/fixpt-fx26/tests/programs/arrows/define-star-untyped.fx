; Rejected: `define*` finds what a procedure reads, for a type written.
; `(define* name e)`, of no type, was taken for `(define name e)` by both
; checkers, and the expanders read `e` as a type, so a macro's use in it
; was "not a description" (TODO §309).
(define-syntax twice (syntax-rules ((_ x) (* 2 x))))
(define* f (lambda ((x int)) (+ 1 (twice x))))
(f 3)
