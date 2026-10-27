;; A file offering an operation on another file's abstract type.
(define c (load-module "shared-counter.fx"))
(define bump (subr pure ((select c t)) int) (lambda (v) (+ 1 ((with c value) v))))
