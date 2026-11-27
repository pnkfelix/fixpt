;; Takes both bundles, the second over the first: a value of the second's and
;; a procedure of the first's meet, the one type.
(module-parameters ((env (load-moduleof "dm-penv.fx") #:qualified)
                    (env2 (load-moduleof "dm-penv2.fx" env) #:qualified)))
(hide (include (with env m-base)) (include (with env2 m-frame)))
(define v int (value (next start)))
