;; Takes both bundles, the second over the first, and imports the macros of
;; the second's member by a path: a value of the second's and a procedure of
;; the first's meet, the one type; a local `env` and `env2` capture nothing.
(module-parameters ((env (load-moduleof "env.fx") #:qualified)
                    (env2 (load-moduleof "env2.fx" env) #:qualified)))
(hide (include env::m-base) (include env2::m-frame))
(hide (import-with-syntax env2::m-frame (only bump)))
(define v int (value (bump start)))
(define w int (let ((env 0) (env2 0)) (value (bump (bump start)))))
