;; A file of one parameter, `dm-env.fx`'s module, that includes its members
;; by path, hidden: their names its own, their types the path's,
;; `env.base..t` (`docs/research/dependent-moduleof.md`, step 4); and names
;; one by path, `env::base::value`, which the file is expanded for.
(module-parameters ((env (load-moduleof "dm-env.fx") #:unqualified)))
(hide (include (with env base)) (include (with env user)))
(define* three (subr pure () int) (lambda () (value (next (two)))))
(define* four (subr pure () int) (lambda () (env::base::value (next (next (two))))))
