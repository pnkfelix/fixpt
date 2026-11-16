;; => 6
;; A template writes out the elements of a list a signature gives by ellipsis, each exporting
;; its binder: each element's export is said from the list's pair, its region's root.
(define-syntax my-let
  (macro (_ ((x @ bvar expr) ...) body @ expr) expr (bind (x ...) in body))
  (syntax-rules ((_ ((x e) ...) body) (let ((x e) ...) body))))
(define-syntax two
  (macro (_ expr) expr)
  (syntax-rules ((_ e) (my-let ((a 1) (b 2)) (+ a (+ b e))))))
(two 3)
