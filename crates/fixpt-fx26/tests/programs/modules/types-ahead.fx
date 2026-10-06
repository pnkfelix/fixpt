;; => 1
;; A module's type abbreviations are declared ahead, as a program's are:
;; `size` names `tree` before its `define-datatype`, and `tree` is
;; recursive (`TODO.md` §34).
(define m (module
  (define size (subr pure (tree) int) (lambda (t) (tagcase t (leaf () 0) (node (l r) 1))))
  (define-datatype tree (leaf) (node tree tree))
  (define-type forest (listof tree acyclic))
  (define-type pair-of (productof (1 tree) (2 forest)))))
((with m size) ((with m node) ((with m leaf)) ((with m leaf))))
