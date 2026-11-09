;; => 9
;; A template's `rlambda`, its closure made in a place it names.
(define-syntax arena-id (expr)
  (syntax-rules ()
    ((_ e) (letrena p ((rlambda p ((x int)) x) e)))))
(arena-id 9)
