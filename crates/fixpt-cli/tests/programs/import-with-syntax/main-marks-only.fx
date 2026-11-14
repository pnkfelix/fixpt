;; Only the file's `pick-or-7`: its template's `via` is still the file's,
;; which this program has by no name.
(define marks (load-module "marks.fx"))
(import-with-syntax marks (only pick-or-7))
(pick-or-7 #f)
