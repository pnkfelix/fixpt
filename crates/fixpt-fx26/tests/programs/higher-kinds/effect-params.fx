;; ! a description function to an effect takes regions, places, effects, sizes and conventions
;; An effect family takes no types: an effect is substituted into without
;; looking at types.
(define-type bad (poly ((e (=> (type) effect))) int))
