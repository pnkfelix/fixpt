; A one-shot continuation (`TODO.md` §98), resumed once: the rest of the
; prompt's body, `(+ 1 _)`, runs once, as a composable one's would. 43.
(define t (prompt-tag int int (read @globals) @p) (make-continuation-prompt-tag))

(prompt t
  (+ 1 (call-with-oneshot-continuation
         (lambda ((k (oneshot int int (read @globals) @p))) (* 2 (k 20)))
         t))
  (lambda (v) v))
