;; => 2
;; A shape named (`define-syntax`) and written as a definition's type: the
;; module given is sealed to its names (`binding-shapes.md`), `secret`
;; left out, its abstract type as the module has it.
(define-syntax counter-shape (modnames zero inc value (abs t)))
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define secret int 41)
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define c counter-shape counter)
(with c (value (inc (inc zero))))
