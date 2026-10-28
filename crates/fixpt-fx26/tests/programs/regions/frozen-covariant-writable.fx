; Rejected: a place's writable list takes no heap tail; a `set-cdr!` could
; then store a pointer to short-lived data inside long-lived data.
(define heap-list (listof int acyclic) (list 1 2 3))
(letrena r (the (listof int r) (rcons r 5 heap-list)))
