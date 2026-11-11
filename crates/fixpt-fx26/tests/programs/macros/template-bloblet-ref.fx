;; => 33
;; A template writing a form only `scope-forms` has that binds nothing
;; (`TODO.md` §247): `bloblet-ref`, its operands expressions.
(define-syntax field1 (expr) (syntax-rules () ((_ b) (bloblet-ref b 1))))
(define bl (the (bloblet (fields int int) @t) (make-bloblet 0 10 32)))
(+ (field1 bl) 1)
