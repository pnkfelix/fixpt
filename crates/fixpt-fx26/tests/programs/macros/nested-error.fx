;; ! argument 2 is a bool, where a int is expected
;; An error in text a template made: said where the template wrote it, then
;; each use that made it, innermost first (`fixpt`'s `located`).
(define-syntax add-one
  (expr)
  (syntax-rules ()
    ((_ e) (+ e #t))))
(define-syntax twice-add
  (expr)
  (syntax-rules ()
    ((_ e) (add-one e))))
(twice-add 3)
