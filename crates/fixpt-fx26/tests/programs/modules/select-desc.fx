;; => 7
;; `(select m d)` names a transparent description: what it is.
(define n (module (define-type num int) (define x num 5)))
(+ (the (select n num) 2) (with n x))
