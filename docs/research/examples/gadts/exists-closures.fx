;;; FX-26 today: no existential types, so a value "of some type a, with
;;; operations on a" is packed with the operations already applied to it:
;;; the hidden state lives in closures (the object encoding of
;;; existentials). The Haskell
;;;   data Counter where MkCounter :: a -> (a -> a) -> (a -> Int) -> Counter
;;; becomes a counter that knows its own next state. Two counters with
;;; different hidden states (an int, a string) share one type.
(define-type counter (productof (next (subr spin () counter)) (get (subr pure () int))))
(define by-int (subr pure (int) counter)
  (letrec ((mk (subr pure (int) counter)
             (lambda (n) (product (next (lambda () (mk (+ n 1)))) (get (lambda () n))))))
    mk))
(define by-string (subr pure (string) counter)
  (letrec ((mk (subr pure (string) counter)
             (lambda (s)
               (product (next (lambda () (mk (string-append s "x"))))
                        (get (lambda () (string-length s)))))))
    mk))
(define step (subr spin (counter) counter) (lambda (c) ((extract c next))))
(define peek (subr pure (counter) int) (lambda (c) ((extract c get))))
(define cs (listof counter acyclic) (list (by-int 40) (by-string "")))
(+ (peek (step (step (car cs)))) (peek (step (step (car (cdr cs))))))
