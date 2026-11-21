;; => 2
;; A module whose item is over an earlier item has a dependent module type,
;; `user`'s `(select base t)`, which a binding of it reads as its paths; the
;; member by its place in the module's type, a hidden item's left out.
(define m (module (hide (define one 1))
                  (define base ((load-module "../module-files/dm-base.fx")))
                  (define user ((load-module "../module-files/dm-user.fx") base))))
((with (with m base) value) ((with (with m user) two)))
