;; => 42
;; A type declared ahead naming an effect a module gives, re-exported.
(define m (module
  (define-effect touches (maxeff (read @heap) (write @heap)))
  (define bump (subr touches ((ref int @heap)) unit) (lambda (c) (set c (+ (get c) 1))))))
(define-effect touches (select m touches))
(define-type bumper (subr touches ((ref int @heap)) unit))
(define b bumper (with m bump))
(let ((c (the (ref int @heap) (new 41)))) (begin (b c) (get c)))
