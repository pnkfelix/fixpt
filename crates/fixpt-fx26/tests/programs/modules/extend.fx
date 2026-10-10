;; => 109
;; `(extend e0 e1)` (FX-91's, `TODO.md` §69): a module of the values of
;; both, `e1`'s where both have a name. Here `y` is `b`'s: 1 + 20 + 30, and
;; `f`, wanting a module of fewer values in another order, is given one made
;; of the two, and an `extend` itself: 30 - 1 each time.
(define a (module (define x int 1) (define y int 2)))
(define b (module (define y int 20) (define z int 30)))
(define c (extend a b))
(define f (subr pure ((moduleof (val z int) (val x int))) int)
  (lambda (m) (- (with m z) (with m x))))
(+ (+ (with c x) (+ (with c y) (with c z))) (+ (f c) (f (extend a b))))
