; `(->* (param …) result)`: a procedure's type with its effect found from
; its `lambda`, a call of itself included: the globals it calls, `spin` if
; it may not end (or reads itself, which a redefinition could make loop),
; what it allocates; under `poly` too.
(define inc (-> (int) int) (lambda (x) (+ x 1)))
(define inc2 (->* (int) int) (lambda (x) (inc (inc x))))
(define count (->* (int) int) (lambda (n) (if (<= n 0) 0 (+ 1 (count (- n 1))))))
(define mk (->* (int) (listof int @h)) (lambda (n) (cons n nil)))
(define ap (poly ((t type)) (->* ((-> (t) t) t) t)) (lambda (f x) (f x)))
(define go (->* (int) int) (lambda (n) (count (car (mk (inc2 n))))))
(+ (go 3) (ap inc 1))
