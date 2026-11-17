;; A module file importing another's macros (`binding-shapes.md`, step 4;
;; Heist's (b)): used in the file, and given on, as its own are.
(define lib (load-module "lib.fx"))
(import-with-syntax lib)
(define g (lambda ((n int)) (clamp (+ n 1))))
