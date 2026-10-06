;; => 1
;; A module type with an effect: `(desc e E)` in `moduleof`.
(define m (module
  (define-effect touches (maxeff (read @heap) (write @heap)))
  (define bump (subr touches ((ref int @heap)) unit) (lambda (c) (set c (+ (get c) 1))))))
(define n (moduleof (desc touches (maxeff (read @heap) (write @heap)))
                    (val bump (subr (maxeff (read @heap) (write @heap)) ((ref int @heap)) unit)))
  m)
1
