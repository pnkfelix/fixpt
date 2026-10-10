;; ! `checker` here is the module's own item, made after `lines`, not the `checker` bound outside it
;; A module's items scope over all of it (`letrec*`), so the item `checker`
;; captures the `checker` bound around the module, which `(with checker
;; lines)` meant; said so (`TODO.md` §72), not `lines` used before it is made.
(define entries
  (let ((checker (module (define checker (subr pure (int) int) (lambda (x) (+ x 1)))
                         (define lines (subr pure (int) int) (lambda (x) (* x 2))))))
    (module (define lines (with checker lines))
            (define checker (with checker checker)))))
(define lines (with entries lines))
(define checker (with entries checker))
(define r (+ (lines 10) (checker 10)))
