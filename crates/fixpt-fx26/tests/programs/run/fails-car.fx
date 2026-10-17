;; A failure, said alike on every machine (`DONE.md` §85): "car or cdr of
;; a non-pair", not Scheme's "expected a pair: ()" nor the evaluator's own.
(car (the (listof int @l) nil))
