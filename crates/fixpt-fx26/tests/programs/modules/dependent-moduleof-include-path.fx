;; => 9
;; An `include` of a path to a module, `e::base`, in a module and in a module
;; file: its types aliased by the path, `e.base..t`, so that what `e::user`
;; gives `e::base` takes.
(define e ((load-module "../module-files/dm-env.fx")))
(define m (module (hide (include e::base) (include (with e user)))
                  (define* two-on (subr pure () int) (lambda () (value (two))))))
(define fr ((load-module "../module-files/dm-frame-paths.fx") e))
(+ ((with m two-on)) (+ ((with fr three)) ((with fr four))))
