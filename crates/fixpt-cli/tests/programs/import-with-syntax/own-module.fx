;; A file's own macro used inside a `module` with an item of a name the
;; macro names, `limit`: renaming the item would change what the module
;; gives (`(with m limit)` would be the file's 10, not 3): refused, for now.
(define limit int 10)
(define-syntax clamp (macro (_ expr) expr)
  (syntax-rules ((_ e) (let ((x e)) (if (> x limit) limit x)))))
(define m (module (define limit int 3) (define y int (clamp 50))))
(define z int (with m limit))
