;; A module file's hidden import: its macros the file's own, used by a macro
;; it gives, and not given on.
(define lib (load-module "macros-only.fx"))
(hide (import-with-syntax lib))
(define-syntax quad (macro (_ expr) expr) (syntax-rules ((_ e) (twice (twice e)))))
(define four int (twice 2))
