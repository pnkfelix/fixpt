;; ! a process may share nothing that can be written, and its body holds `bump`
;; A procedure that writes shared data may not cross into a process either.
(define counter (ref int @c) (new 0))
(define* bump (subr (maxeff (read @c) (write @c)) () unit)
  (lambda () (set counter (+ 1 (get counter)))))
(define w (addr int @w) (spawn (box int p) (begin (receive box) (bump))))
