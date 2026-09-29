;;; `letrec` procedures lambda-lifted: only called, so each takes what it
;;; would have captured as arguments, and no closure is made each time.
;;; Siblings that call each other (each takes what the other does), a
;;; lambda inside one calling another (it captures the names the call
;;; passes), a loop (still a jump), a call of itself not in tail position,
;;; and a group inside another lifted one, calling it.
(define* f (subr spin (int int) int)
  (lambda (base n)
    (letrec ((up (subr spin (int int) int)
               (lambda (i acc) (if (= i n) acc (up (+ i 1) (+ acc (bump i))))))
             (bump (subr pure (int) int) (lambda (i) (+ i base)))
             (fact (subr spin (int) int) (lambda (k) (if (= k 0) 1 (* k (fact (- k 1))))))
             (later (subr pure (int) (subr spin () int)) (lambda (i) (lambda () (bump i)))))
      (letrec ((twice (subr spin (int) int) (lambda (i) (+ (up i 0) ((later i))))))
        (+ (twice 2) (fact n))))))
(f 10 5)
