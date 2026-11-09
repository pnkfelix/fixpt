;; ! `e` is bound within (read @c), and (write @c) is not: it has (write @c)
;; A handler that writes, where one that only reads is bound (TODO.md §226).
(define run (poly ((r region) (e effect (within (read r))))
              (subr (read r) ((ref int r) (subr e () int)) int))
  (plambda ((r region) (e effect (within (read r)))) (lambda (c h) (+ (get c) (h)))))
(let ((c (the (ref int @c) (new 3))))
  (run c (lambda () (begin (set c 4) 1))))
