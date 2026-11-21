;; A file of one parameter, a bundle of modules whose `user` is over its own
;; `base` (a dependent module type): where a chain of parameters was
;; (Heist's should-work note, entry 11).
(module-parameters ((env (moduleof (val base (load-moduleof "dm-base.fx"))
                                   (val user (load-moduleof "dm-user.fx" base))))))
(define* three (subr pure () int)
  (lambda () (with env (with base (value (next ((with user two))))))))
