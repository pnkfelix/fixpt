;; The file's `helper`, not this program's: 6 here, 6 in the file: 66.
(define lib (load-module "procedural.fx"))
(import-with-syntax lib)
(define helper (subr pure (int) int) (lambda (x) (* x 100)))
(+ (* 10 (inc 5)) (with lib six))
