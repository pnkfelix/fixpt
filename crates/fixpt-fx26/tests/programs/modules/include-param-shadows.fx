;; => 1123
;; A parameter of an item's lambda shadows a name the module includes, as
;; it would one the module defines (`DONE.md` §69), of another type too:
;; `pick`'s `x`, a `bool`, not the included `int`; and `down`'s `n`, in a
;; `define-rec`. A name the parameters leave alone is still the included
;; one (`y`, `n` in `scaled`).
(define a (module (define x int 1) (define y int 20) (define n int 100)))
(define m
  (module
    (include a)
    (define pick (subr pure (bool) int) (lambda (x) (if x y 2)))
    (define-rec
      (down (subr spin (int int) int)
        (lambda (n acc) (if (= n 0) acc (down (- n 1) (+ acc x))))))
    (define scaled (subr pure (int) int) (lambda (k) (* k n)))))
(+ ((with m pick) #t) (+ ((with m down) 3 0) ((with m scaled) 11)))
