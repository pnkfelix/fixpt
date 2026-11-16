;; ! a fact under `...` that names what is outside its repetition: not yet (TODO §289)
;; Scheme's `do`: each `step` sees every `v`, no `init` does, which a fact
;; under `...` says, its binders every repetition's, outside its own.
(define-syntax my-do
  (macro (_ ((v @ bvar init @ expr step @ expr) ...) (test @ expr res @ expr) body @ expr)
         expr
    (bind (v ...) in step) ...
    (bind (v ...) in test)
    (bind (v ...) in res)
    (bind (v ...) in body))
  (syntax-rules
    ((_ ((v init step) ...) (test res) body) 0)))
