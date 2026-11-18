;; A module file using `via-er`, whose transformer renames `pw`, of its
;; file: that macro, not a standard name.
(hide (define k (load-module "renaming.fx")) (import-with-syntax k (only via-er)))
(define a (via-er 7))
