;; => 107
;; A trap in an `attempt`'s body (`car` of `nil`) is its on-failure's
;; value, whatever the machine says of it; the program goes on.
(define* first (subr (read @h) ((listof int @h)) int) (lambda (l) (car l)))
(define* safe-first (subr (maxeff (read @h) nondet) ((listof int @h)) int)
  (lambda (l) (attempt (first l) (lambda ((m string)) (if (string=? m "") 0 100)))))
(+ (safe-first (list 7)) (safe-first nil))
