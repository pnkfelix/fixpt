;; A file's macro whose description has a binder of its own in it: not
;; yet, as the file's descriptions are read through its module whole.
(define-syntax ident () (syntax-rules () ((_) (plambda ((a type)) (lambda ((x a)) x)))))
