;; `quad`'s `twice` the file's, not this program's: (4 12 0).
(define m (load-module "imports-hidden.fx"))
(import-with-syntax m)
(define-syntax twice (macro (_ expr) expr) (syntax-rules ((_ e) 0)))
(list (with m four) (quad 3) (twice 5))
