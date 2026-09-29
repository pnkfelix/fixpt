;;; EXPECTED TO FAIL: a reading of an arena's counter may not be kept for
;;; after the arena ends, since the place no longer exists then.
;;; MOCK prelude as in place-words.fx.
(define-effect observes (maxeff (read @telemetry) (write @telemetry)))
(define fake (ref int @telemetry) (new 0))
(define* place-words-allocated
  (poly ((p place)) (subr (maxeff (read p) observes) ((place p)) nat))
  (plambda ((p place))
    (lambda ((q (place p))) (begin (set fake (get fake)) (confirm-nat (get fake) (n n) 0)))))

(define later (subr pure () (subr observes () nat))
  (lambda () (letrena r (lambda () (place-words-allocated r)))))
