;; => 12
;; `hide` at a program's top level: its forms as if written there, a
;; program exporting nothing to hide them from; so a module file's text,
;; its own hidden macros among it, runs as a program.
(hide (define-syntax twice (expr) (syntax-rules () ((_ a) (let ((x a)) (+ x x)))))
      (define base int 5))
(hide (define-syntax plus-base (expr) (syntax-rules () ((_ a) (+ a base)))))
(twice (plus-base 1))
