;; At a program's top level, `via-er`, whose transformer renames `pw`.
(define k (load-module "renaming.fx"))
(import-with-syntax k (only via-er))
(via-er 7)
