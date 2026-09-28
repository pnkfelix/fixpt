;;; Self tail calls of `letrec`-bound procedures, which the compilers make
;;; loops (PLAN.md, 13e), and the calls that must not be. The tests run each
;;; program compiled and lowered to Scheme, and compare.

;; A loop with a `let`'s value on its frame when it jumps back.
(define sum-squares (subr spin (int) int)
  (lambda (n)
    (letrec ((go (subr spin (int int) int)
               (lambda (i acc)
                 (let ((sq (* i i)))
                   (if (> i n) acc (go (+ i 1) (+ acc sq)))))))
      (go 0 0))))

;; A self-call not in tail position: not a loop, and the procedure is boxed.
(define fact (subr spin (int) int)
  (lambda (n)
    (letrec ((f (subr spin (int) int) (lambda (k) (if (= k 0) 1 (* k (f (- k 1)))))))
      (f n))))

;; The name hidden by a parameter: the call is of the parameter.
(define hidden (subr pure (int) int)
  (lambda (n)
    (letrec ((go (subr pure ((subr pure (int) int) int) int)
               (lambda (go k) (go k))))
      (go (lambda ((x int)) (+ x 1)) n))))

;; A procedure that also escapes, as a value: boxed, its tail calls still loops.
(define twice (subr (maxeff spin (read (globals twice))) ((subr (maxeff spin (read (globals twice))) (int int) int) int int) int)
  (lambda (g i a) (g i a)))
(define* escapes (subr spin (int) int)
  (lambda (n)
    (letrec ((go (subr (maxeff spin (read (globals twice))) (int int) int)
               (lambda (i acc)
                 (cond ((= i 0) acc)
                       ((= i 1000) (twice go (- i 1) acc))
                       (else (go (- i 1) (+ acc i)))))))
      (go n 0))))

;; Mutual recursion: both boxed, and neither call a loop.
(define parity (subr spin (int) int)
  (lambda (n)
    (letrec ((ev (subr spin (int) bool) (lambda (k) (if (= k 0) #t (od (- k 1)))))
             (od (subr spin (int) bool) (lambda (k) (if (= k 0) #f (ev (- k 1))))))
      (if (ev n) 1 0))))

;; A loop through a `tagcase`'s arms, with the arms' names on the frame.
(define areas (subr spin (int) int)
  (lambda (n)
    (letrec ((go (subr spin (int int) int)
               (lambda (i acc)
                 (if (= i n)
                     acc
                     (tagcase (the (sumof (sq int) (rect (productof (1 int) (2 int))))
                                   (if (= (modulo i 2) 0) (sum sq i) (sum rect (product (1 i) (2 3)))))
                       (sq s (go (+ i 1) (+ acc (* s s))))
                       (rect (w h) (go (+ i 1) (+ acc (* w h)))))))))
      (go 0 0))))

;; An inner `letrec` of the same name: its calls are its own loop.
(define inner-same (subr spin (int) int)
  (lambda (n)
    (letrec ((go (subr spin (int) int)
               (lambda (i)
                 (if (= i 0)
                     (letrec ((go (subr spin (int) int) (lambda (j) (if (= j 5) j (go (+ j 1)))))) (go 0))
                     (go (- i 1))))))
      (go n))))

(the (listof int @l)
     (cons (sum-squares 100000)
           (cons (fact 10)
                 (cons (hidden 41)
                       (cons (escapes 2000)
                             (cons (parity 101)
                                   (cons (areas 1000)
                                         (cons (inner-same 7) nil))))))))
