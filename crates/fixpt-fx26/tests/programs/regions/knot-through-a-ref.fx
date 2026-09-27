; Rejected: Landin's knot. A procedure kept in `@b` that reads `@b` could be
; fetched from there by itself, and loop with no recursive call; so its type
; must say `spin`.
(define r (ref (listof (subr (read @b) () int) @b) @b) (new nil))
