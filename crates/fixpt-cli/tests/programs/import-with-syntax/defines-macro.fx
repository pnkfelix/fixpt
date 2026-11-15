;; A file's macro that defines a macro: the defined macro's names mean what
;; they do in this file, where the macro that defines it is defined, not
;; where it is used.
(define limit int 10)
(define-syntax define-clamper
  (macro (bvar) defn)
  (syntax-rules
    ((_ name) (define-syntax name (syntax-rules ((_ e) (if (> e limit) limit e)))))))
