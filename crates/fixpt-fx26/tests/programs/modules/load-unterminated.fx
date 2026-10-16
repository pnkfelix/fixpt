;; ! in `../module-files/unterminated.fx`, 3:1: unterminated list, expected `)`
;; A file loaded that does not read is refused, said in the file, at the
;; load's start in both checkers (as `load-parameters-bad.fx` and
;; `load-cycle.fx`; the FX-26 one once said these over the whole load).
(define m (load-module "../module-files/unterminated.fx"))
0
