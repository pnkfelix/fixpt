;; => 5
;; Probe: does `define-generative`'s declared `rep` see which "brand" `f`
;; is? It cannot -- `rep` is one fixed expression for the whole family, so
;; `f` here is only ever an uninterpreted, invariant marker; the
;; representation is `a` for every choice of `f`. This is why Yallop &
;; White's brand trick (a single `('f, 'a) app` family whose runtime
;; representation silently varies by brand, via an unsafe identity cast
;; outside the type system) cannot be transplanted onto `define-generative`
;; as-is: FX-26 requires one honest, declared `rep` per family, checked
;; once, with no unsafe escape hatch to let it vary per instantiation of
;; `f` the way OCaml's `%identity` does.
(define-generative (app (f type) (a type)) a)
(define-generative list-brand int)
((proj down-app list-brand int) ((proj up-app list-brand int) 5))
