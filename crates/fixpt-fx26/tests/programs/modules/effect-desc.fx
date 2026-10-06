;; => 3
;; `define-effect` in a module: `(desc touches E)` in its type; outside,
;; `(select m touches)` is `E`, resolved where a type is, as a type's
;; `select` is (`TODO.md` §34).
(define-type cell (ref int @heap))
(define m (module
  (define-effect touches (maxeff (read @heap) (write @heap)))
  (define bump (subr touches (cell) unit) (lambda (c) (set c (+ (get c) 1))))))
(define-effect touches (select m touches))
(define twice (subr (maxeff touches (read (globals m))) (cell) unit)
  (lambda (c) (begin ((with m bump) c) ((with m bump) c))))
(let ((c (the cell (new 1)))) (begin (twice c) (get c)))
