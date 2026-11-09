;; ! `m` is bound by the repetitions before this one, which its name does not tell apart: a repeated part refers to no binder it repeats in its own scope
;; A parameter named, repeated, whose type names it: the repetition
;; before's, which a name cannot say.
(define-syntax chain
  (-> (bvar type ...) defn)
  (syntax-rules ()
    ((_ name f ...) (define name (subr pure ((m : (select m t)) ...) int) (lambda (x) 0)))))
(chain c int int)
