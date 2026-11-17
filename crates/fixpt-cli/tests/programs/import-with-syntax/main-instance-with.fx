;; A use of an instance's macro inside a `with`, which may give a module of
;; the instance's name: refused, for now.
(define a ((proj (load-module "counter.fx") @globals)))
(define m (module (define a 1)))
(import-with-syntax a)
(with m (tick-twice 3))
