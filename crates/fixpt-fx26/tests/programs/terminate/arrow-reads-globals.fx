; Rejected: `(-> (param …) result)` is pure, and calling a global reads
; it, `(read (globals inc))`, as `(subr pure …)` refuses too.
(define inc (-> (int) int) (lambda (x) (+ x 1)))
(define inc2 (-> (int) int) (lambda (x) (inc (inc x))))
(inc2 0)
