;; ! `t` is bound by the repetitions before this one, which its name does not tell apart: a repeated part refers to no binder it repeats in its own scope
;; A repeated clause of a `let*` refers to the name it binds itself: in the
;; first repetition the clause before, in the others the repetition before,
;; which a name cannot say.
(define-syntax summed
  (expr ...)
  (syntax-rules ()
    ((_ e ...) (let* ((t 0) (t (+ t e)) ...) 0))))
(summed 1 2 3)
