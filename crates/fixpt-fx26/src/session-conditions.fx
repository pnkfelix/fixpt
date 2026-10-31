;; Sessions in the condition-raising style (`docs/research/eval.md`,
;; "Sessions"): a library over the forms, built in, which a program loads as
;; `(load-module "fx26:session-conditions.fx")`.
;;
;; - `commit!`: a pending definition committed to its session, as
;;   `session-commit!` commits it; but a redefinition `raise`d
;;   (`fx26:conditions.fx`) to the handler `key`'s mark holds, whose answer,
;;   a `session-decision`, decides it. The handler may answer, escape to a
;;   `handle` outside (nothing is committed), or capture a continuation and
;;   answer later. A definition that redefines nothing is committed, as
;;   `shadow`; a failure is the value it is, as `session-commit!`'s.
(hide (define conditions (load-module "fx26:conditions.fx")))
(hide (define raise (with conditions raise)))
(define commit!
  (poly ((m type) (r region) (e effect) (k region) (eh effect))
    (subr (maxeff e eh (read r) (write r) (read k))
          ((sessionof m r) (pending e r)
           (mark-key (subr eh (session-redefinition) session-decision) k))
          (sumof (defined string) (failed stage-failure))))
  (plambda ((m type) (r region) (e effect) (k region) (eh effect))
    (lambda (s d key)
      (session-commit! s d
                       (tagcase (session-redefines s d)
                         (fresh u (sum shadow #u))
                         (redefines rd
                           ((proj (proj raise k) session-redefinition session-decision eh)
                            key rd)))))))
