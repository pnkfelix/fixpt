;; => 3
;; A file's module of such a type, given to a file that takes it as its one
;; parameter, typed by `load-moduleof`.
(define e ((load-module "../module-files/dm-env.fx")))
(define fr ((load-module "../module-files/dm-frame-env.fx") e))
((with fr three))
