;; => 45
;; A string as a module's item is a comment: it binds nothing, is not in
;; the module's type, and does nothing when the module is made. Here
;; between definitions, first and last, inside a `hide`, and as the
;; top-level forms of a file `load-module` reads.
(define m
  (module
    "First."
    (define a int 1)
    "Between."
    (hide "In a hide." (define b int 2) "After one.")
    (define c int (+ a b))
    "Last."))
(define f (load-module "../module-files/strings.fx"))
(+ (+ (with m a) (with m c)) (with f answer))
