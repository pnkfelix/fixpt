;; => 17
;; A conductor: a module made once, passed to the module made of it
;; (`TODO.md` §68).
(define dep (load-module "../module-files/linked-dep.fx"))
(define user-file (load-module "../module-files/linked-user.fx"))
(define user ((with user-file make) dep))
(+ (with user v) (string-length ((with user shout) "hi")))
