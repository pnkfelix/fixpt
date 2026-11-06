;; ! a int is expected here, and this is a string
;; A branch no member's type lets run is checked, under the last member, as
;; it would be outside an `allof`: what it says wrong is said.
(define f (allof (subr pure (symbol) int) (subr pure (string) int))
  (lambda (t) (if (null? t) "none" 1)))
