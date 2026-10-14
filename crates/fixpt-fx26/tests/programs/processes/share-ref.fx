;; ! a process may share nothing that can be written, and its body holds `counter`
;; A process may not hold what another can write: a reference here.
(define counter (ref int @c) (new 0))
(define w (addr int @w) (spawn (box int p) (set counter (receive box))))
