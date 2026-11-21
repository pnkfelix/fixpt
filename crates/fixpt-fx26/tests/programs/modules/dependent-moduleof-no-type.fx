;; ! `base` gives no type `nope`: a member's type names an earlier member's types
;; A member's type names only types its earlier member gives.
(define-type env-t (moduleof (val base (load-moduleof "../module-files/dm-base.fx"))
                             (val user (subr pure () (select base nope)))))
1
