;; ! argument 1 is a keyword, where a (subr pure (int) (sumof (#:ok int))) is expected
;; A keyword constructs only at a list's head: given where a procedure is
;; wanted, it is a keyword, as anywhere else.
(define wrap (subr pure ((subr pure (int) (sumof (#:ok int))) int) (sumof (#:ok int)))
  (lambda (f x) (f x)))
(wrap #:ok 1)
