;; ! `y` is a part repeated in a repeated part, which no fact names yet
;; A fact that names a part repeated in a repeated part: not yet (Heist's
;; `fixpt-nested-repetition.md`, 2026-11-27).
(define-syntax lets
  (macro (_ ((x @ bvar y @ bvar ...) ...) body @ expr) expr
    (bind (y ...) in body))
  (syntax-rules
    ((_ ((x y ...) ...) body) body)))
(lets ((a b c)) 1)
