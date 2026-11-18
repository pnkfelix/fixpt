;; ! `loop` is a macro's name, which is not bound
;; A template's own binder may not be a macro's name, not yet (TODO.md §295).
(define-syntax loop (macro (_ expr) expr) (syntax-rules ((_ e) e)))
(define-syntax twice (macro (_ expr) expr) (syntax-rules ((_ e) (let ((loop e)) (+ loop loop)))))
(twice 3)
