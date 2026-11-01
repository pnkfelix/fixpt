;; => -1
;; `attempt-within`: a body that fails within its budget gives the
;; on-failure's value, as `attempt`'s does.
(define* first (subr (read @h) ((listof int @h)) int) (lambda (l) (car l)))
(attempt-within 10000 (first nil) (lambda ((m string)) -1) (lambda () -2))
