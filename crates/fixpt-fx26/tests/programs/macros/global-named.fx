;; => 3
;; A template's free name is the top level's where the macro is used,
;; `(with #%toplevel helper)`, whatever binds the name there: not the use's
;; own `helper` (`typed-macros.md`, item 5).
(define helper 3)
(define-syntax use-helper
  ()
  (syntax-rules ()
    ((_) helper)))
(let ((helper 99)) (use-helper))
