;; Takes env.fx's module, qualified, and includes its `m-base` by a path, in a
;; `hide`: a macro of it names `thing`, which the include brings, so its
;; frame holds it, as a parameter's not `qualified` (`TODO.md` §300).
(module-parameters ((env (load-moduleof "env.fx") #:qualified)))
(hide (include env::m-base))
(define-syntax make-thing (macro (_ e @ expr) expr) (syntax-rules ((_ e) (the thing e))))
