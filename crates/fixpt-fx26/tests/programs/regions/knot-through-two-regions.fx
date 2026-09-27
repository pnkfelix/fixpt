; Rejected: a knot through two regions. A procedure kept in `@r` that calls
; one fetched from `@s` does what that one does too, which reads `@r`; so it
; reads the region it is kept in, however indirectly, and must say `spin`.
(define rr (ref (listof (subr (read @s) () int) @r) @r) (new nil))
(define ss (ref (listof (subr (read @r) () int) @s) @s) (new nil))
(set rr (cons (lambda () ((car (get ss)))) nil))
