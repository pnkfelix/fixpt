; Rejected (docs/research/soundness-findings.md, F13): `acyclic?` walks
; data frozen into arena `p`, and so reads `p`, which its type once hid
; (`pure` over any `data`). A closure that walks it would outlive the
; arena and, called later, walk what another arena put there.
(define* stale (subr pure () (subr pure () bool))
  (lambda ()
    (letrena p
      (let ((x (letfreeze (r p) (the (listof int r) (rcons p 1 nil)))))
        (lambda () (acyclic? x))))))
(define* probe (subr (maxeff spin) () bool)
  (lambda ()
    (let ((f (stale)))
      (letrena q
        (let ((c (the (listof int q) (rcons q 2 nil))))
          (begin (set-cdr! c c) (f)))))))
(probe)
