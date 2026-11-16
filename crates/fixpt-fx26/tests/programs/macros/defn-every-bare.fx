;; ! `c` is a repeated part's: `(c ...)`, every repetition's
;; What a use defines, a repeated part's label named alone.
(define-syntax define-all
  (macro (_ (c @ bvar e @ expr) ...) (defn c))
  (syntax-rules ((_ (c e) ...) (begin (define c e) ...))))
(define-all (x 1) (y 2))
