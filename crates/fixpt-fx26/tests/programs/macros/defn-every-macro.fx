;; ! every repetition's macro binder, `((label (macro …)) ...)`: not yet
;; What a use defines, every repetition's macro, its signature said: not yet.
(define-syntax define-all
  (macro (_ m @ bvar ...) (defn ((m (macro (_) expr)) ...)))
  (syntax-rules ((_ m ...) (begin (define-syntax m (syntax-rules ((_) 1))) ...))))
(define-all one two)
