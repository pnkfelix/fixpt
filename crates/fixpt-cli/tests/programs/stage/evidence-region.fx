;; Evidence of a region (`docs/research/eval.md`, "Evidence"): a module
;; whose value is at a `plambda`'s region parameter, staged against as it
;; was instantiated: a `letregion`'s, of its own, and `@a`, itself.
(define line (subr (io stdout) (string) unit)
  (lambda (s) (begin (write-out (string-append s "\n")) #u)))
(define read-in
  (poly ((r region))
    (subr (maxeff stage spin (io stdout) (read r) (read (globals line)))
          ((regionrep r) (moduleof (val cell (ref int r))) datum) unit))
  (plambda ((r region))
    (lambda (rr m code)
      (stage m (read r) int code
        (p (line (int->string (p))))
        (why (line (string-append "refused: " (extract why message))))
        (given rr)))))
(define main
  (subr (maxeff stage spin (io stdout) (read (globals read-in line))) () int)
  (lambda ()
    (begin
      (letregion r
        (let ((m (module (define cell (ref int r) (new 5)))))
          (begin ((proj read-in r) (reify-region r) m '(get cell))
                 ((proj read-in r) (reify-region r) m '(begin (set cell 6) (get cell))))))
      (let ((m (module (define cell (ref int @a) (new 7)))))
        (begin ((proj read-in @a) (reify-region @a) m '(get cell))
               ((proj read-in @a) (reify-region @a) m '(begin (set cell 8) (get cell)))))
      0)))
