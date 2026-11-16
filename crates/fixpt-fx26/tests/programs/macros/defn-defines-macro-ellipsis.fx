;; => (1 2 3)
;; The defined macro's ellipsis, written `(... ...)` (R7RS): every `...` in
;; a template is the template's own.
(define-syntax def-lister
  (macro (_ bvar) defn)
  (syntax-rules
    ((_ name) (define-syntax name (syntax-rules ((_ e (... ...)) (list e (... ...))))))))
(def-lister all)
(all 1 2 3)
