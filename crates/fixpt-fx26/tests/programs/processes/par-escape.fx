;; ! a `par` branch must end where it began
;; A branch may not leave `par` by an escape: its sibling would be left
;; running with nowhere to return to.
(define t (escape-tag int int @e) (make-escape-tag))
(prompt t (par ((a (escape t 1)) (b 2)) (+ a b)) (lambda ((v int)) v))
