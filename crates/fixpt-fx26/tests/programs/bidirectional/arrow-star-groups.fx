; `->*` in `letrec` and `define-rec` groups: each member's effect found
; from its `lambda` once, then with the effects of every member it reaches
; through the group, and `spin` if it may not end (or, at top level, reads
; a member's global, which a redefinition could make loop).
(define inc (-> (int) int) (lambda (x) (+ x 1)))
(define-rec (ev? (->* (nat) bool) (lambda (n) (if (= n 0) #t (od? (- n 1)))))
            (od? (->* (nat) bool) (lambda (n) (if (= n 0) #f (ev? (- n 1))))))
; `get-noisy` names `noisy` but does not call it: it takes `noisy`'s type
; found, not its effect (which says what calling it does), and reads the
; global, a member's, so `spin`.
(define-rec (noisy (->* (int) int) (lambda (k) (inc k)))
            (get-noisy (->* () (subr (read (globals inc)) (int) int)) (lambda () noisy)))
; Ends, and calls no global: pure.
(define total (->* (nat) int)
  (lambda (n)
    (letrec ((go (->* (nat int) int)
               (lambda (k acc) (if (= k 0) acc (go (- k 1) (+ acc k))))))
      (go n 0))))
; `up` reaches `step`, which reads `inc`; `alone` reaches nothing, so is
; pure, as `twice` asks; `kept` is written out, and what it says is what
; reaching it adds.
(define twice (-> ((-> (int) int) int) int) (lambda (g x) (g (g x))))
(define parts (->* (nat) int)
  (lambda (n)
    (letrec ((step (->* (int) int) (lambda (k) (inc k)))
             (up (->* (nat int) int) (lambda (k acc) (if (= k 0) acc (up (- k 1) (step acc)))))
             (kept (subr (alloc @h) (int) (listof int @h)) (lambda (k) (cons k nil)))
             (both (->* (int) int) (lambda (k) (car (kept (step k)))))
             (alone (->* (int) int) (lambda (k) (+ k 1))))
      (+ (up n 0) (+ (both 1) (twice alone 1))))))
; May not end: `spin`.
(define loops (->* (int) int)
  (lambda (n) (letrec ((on (->* (int) int) (lambda (k) (if (= k 0) 0 (on (+ k 1)))))) (on n))))
(+ (if (ev? 4) (total 4) 0) (+ (parts 3) ((get-noisy) 0)))
