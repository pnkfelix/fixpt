;; => 4
;; A description function to an effect, applied, given where an effect is
;; wanted: `(rw @h)` to `run`'s effect binder. Read as the effect it gives,
;; as it is in an effect; it was read as a type, and refused: "gives a
;; description of kind effect, not a type" (`TODO.md` §211).
(define-type rw (dlambda ((r region)) (maxeff (read r) (write r))))
(define run (poly ((e effect)) (subr e ((subr e () int)) int))
  (plambda ((e effect)) (lambda (f) (f))))
(define go (subr (maxeff (read @h) (write @h) (alloc @h) (read (globals run))) () int)
  (lambda ()
    (let ((c (the (ref int @h) (new 3))))
      ((proj run (rw @h)) (lambda () (begin (set c 4) (get c)))))))
(go)
