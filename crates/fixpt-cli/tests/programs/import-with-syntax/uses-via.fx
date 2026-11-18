;; A module file using `via`, whose template uses the procedural `pw`, of
;; its file, imported only by the name the importer has it by.
(hide (define k (load-module "renaming.fx")) (import-with-syntax k (only via)))
(define a (via 7))
