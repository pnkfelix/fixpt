;; A file's macro whose description has a binder of its own in it: each
;; name it writes free read as the file has it, one at a time, its binder
;; renamed (`typed-macros.md`, "Decided: macros come with a file").
(define-syntax ident () (syntax-rules ((_) (plambda ((a type)) (lambda ((x a)) x)))))
