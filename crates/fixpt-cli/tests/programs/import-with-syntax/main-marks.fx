;; The file's trailmark, imported with its macros: a use writes it, and a
;; template of the file's does, each the file's `via`.
(define marks (load-module "marks.fx"))
(import-with-syntax marks)
(list (pick #f via 9) (pick-or-7 #f))
