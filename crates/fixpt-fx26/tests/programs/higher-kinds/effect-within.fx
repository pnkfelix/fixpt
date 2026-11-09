;; => (2 2 6)
;; A bounded effect variable (TODO.md §226): `run` takes a handler of any
;; effect within reading and writing `r`, and says only that bound, not the
;; handler's own effect, as its latent one: `e` is within it.
(define run (poly ((r region) (e effect (within (maxeff (read r) (write r)))))
              (subr (maxeff (read r) (write r)) ((subr e () int)) int))
  (plambda ((r region) (e effect (within (maxeff (read r) (write r)))))
    (lambda (h) (+ (h) 1))))
(let ((c (the (ref int @c) (new 0))))
  (let ((bump (the (subr (maxeff (read @c) (write @c)) () int)
                   (lambda () (begin (set c (+ (get c) 1)) (get c))))))
    (list ((proj run @c (maxeff (read @c) (write @c))) bump)
          ((proj run @c (read @c)) (lambda () (get c)))
          ((proj run @c pure) (lambda () 5)))))
