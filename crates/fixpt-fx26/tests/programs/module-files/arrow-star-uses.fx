;; A lambda typed `->*` whose type names what this file imports: its type
;; is made again where the imports are resolved, and is `->*` still, its
;; effect found (`docs/fx26.md`; both checkers alike).
(module-parameters ((r region)))
(define a ((proj (load-module "arrow-star-types.fx") r)))
(import a (type t) (effect e))
(define-type h (subr e (t) t))
(define f (->* (h t) t) (lambda (g x) (g x)))
