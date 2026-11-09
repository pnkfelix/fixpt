;; ! `p` is bound by the repetitions before this one, which its name does not tell apart: a repeated part refers to no binder it repeats in its own scope
;; A repeated parameter whose type names it: the repetition before's,
;; which a name cannot say.
(define-syntax chained
  (-> (expr ...) expr)
  (syntax-rules ()
    ((_ e ...) ((lambda ((p (select p t)) ...) 0) e ...))))
(chained 1 2)
