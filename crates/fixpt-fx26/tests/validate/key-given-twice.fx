;; `validate`'s record of the cheap keys (`parser-ids.fx`'s `validated!`):
;; `path` key (5 0) given full key (1 2), again alike, then (9 2).
(define ids ((proj (load-module "fx26:parser-ids.fx") @s @e @m @c @p)))
((with ids validated!) (with ids path-seen) "path" 5 0 1 2 0 0)
((with ids validated!) (with ids path-seen) "path" 5 0 1 2 0 0)
((with ids validated!) (with ids path-seen) "path" 5 0 9 2 3 4)
(get (with ids validate-why))
