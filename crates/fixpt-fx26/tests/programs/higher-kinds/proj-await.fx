;; `(await r)` given where an effect is expected, as a `proj` argument: an
;; effect to both checkers. The Rust one read it as a type, "expected a
;; type", having no `await` among its descriptions' effect heads (PLAN.md
;; Q13, O15).
(define f (poly ((e effect)) (subr e () int)) (plambda ((e effect)) (lambda () 1)))
(define g (proj f (await @r)))
g
