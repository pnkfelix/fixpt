;; => 7
;; A module's `define*`, used as a value by another of its items as the
;; module is made: at its type as written (Heist's, 2026-10-28), here kept
;; in a list of hooks that wants it so.
(define m (module (define-type cmd (subr (maxeff (read @globals) (read @heap)) () int))
                  (define hook (ref (listof (subr pure (int) cmd) acyclic) @heap) (new nil))))
(define mk (lambda ()
             (module (hide (include m))
                     (define* f (subr pure (int) cmd) (lambda (k) (lambda () k)))
                     (define r unit (set hook (list f))))))
(define made (mk))
(((car (get (with m hook))) 7))
