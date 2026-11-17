;; A use of an instance's macro inside a `module` with an item of the
;; instance's name: renaming the item would change what the module gives,
;; and the item would capture the instance: refused, for now.
(define a ((proj (load-module "counter.fx") @globals)))
(import-with-syntax a)
(define m (module (define a 3) (define x int (tick-twice 1))))
(list (with m a) (with m x))
