; `->*` in a module: every such lambda's effect found before any of its
; lambdas is checked, a module's state included; mutual recursion that
; ends is pure (a module's lambdas are no globals); one that may not end
; says `spin`; a written-out lambda is checked against the effects found.
(define counter
  (module
    (define cell (ref int @h) (new 0))
    (define inc (-> (int) int) (lambda (x) (+ x 1)))
    (define bump (->* () int) (lambda () (begin (set cell (inc (get cell))) (get cell))))
    (define-rec (ev? (->* (nat) bool) (lambda (n) (if (= n 0) #t (od? (- n 1)))))
                (od? (->* (nat) bool) (lambda (n) (if (= n 0) #f (ev? (- n 1))))))
    (define on (->* (int) int) (lambda (n) (if (= n 0) 0 (on (+ n 1)))))
    (define twice (poly ((t type)) (->* ((-> (t) t) t) t)) (lambda (f x) (f (f x))))
    (define user (subr (maxeff (read @h) (write @h)) () int) (lambda () (+ (bump) (bump))))))
(with counter (+ (user) (if (ev? 4) (twice inc 1) 0)))
