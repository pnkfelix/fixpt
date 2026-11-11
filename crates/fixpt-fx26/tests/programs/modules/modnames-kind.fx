;; ! `t` is a transparent type of (moduleof (desc t int) (val x int)): `(desc t)`
;; A type is named as the module has it: `modnames` names, it does not make
;; a type abstract (a `moduleof` does).
(define m (module (define-type t int) (define x t 1)))
(define s (modnames x (abs t)) m)
