;; A file's macros, imported alone: the use's own `cell`, a string, is not
;; the file's, an int, which the template means by its own `cell`; and a
;; use's type named `a` under a template's binder `a` is not captured.
(define-type cell string)
(define-type a bool)
(define lib (load-module "pairs.fx"))
(import-with-syntax lib (only pair-of cell-list ident))
(define x (pair-of cell) (tuple 7 "seven"))
(define ys (cell-list @heap) (list 1 2 3))
(define f (ident a) (plambda ((b type)) (lambda ((x b) (v bool)) v)))
(+ (+ (extract x 1) (list-length ys))
   (+ (string-length (extract x 2)) (if ((proj f int) 3 #t) 1 0)))
