;; A module file that would give `twice` twice: its import's and its own.
(define lib (load-module "macros-only.fx"))
(import-with-syntax lib)
(define-syntax twice (macro (_ expr) expr) (syntax-rules ((_ e) e)))
