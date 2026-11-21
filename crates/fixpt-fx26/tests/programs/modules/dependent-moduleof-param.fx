;; => 5
;; A dependent module type as a procedure's parameter's: its members' paths
;; from the parameter, and a `with` of it and then of a member.
(define-type env-t (moduleof (val base (load-moduleof "../module-files/dm-base.fx"))
                             (val user (load-moduleof "../module-files/dm-user.fx" base))))
(define b ((load-module "../module-files/dm-base.fx")))
(define u ((load-module "../module-files/dm-user.fx") b))
(define e env-t (module (define base b) (define user u)))
(define use (subr pure (env-t) int)
  (lambda (m) ((with (with m base) value) ((with (with m user) two)))))
(define opened (subr pure (env-t) int)
  (lambda (m) (with m (with base (value (next ((with user two))))))))
(+ (use e) (opened e))
