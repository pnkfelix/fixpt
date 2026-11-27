;; Over the first bundle, qualified: it gives out a value of its member's
;; abstract type, `(select (with env m-base) t)`, and its macro names that
;; type through its frame, which its hidden `include` of the path fills.
(module-parameters ((env (load-moduleof "env.fx") #:qualified)))
(hide (include env::m-base))
(define-syntax bump (macro (_ e @ expr) expr) (syntax-rules ((_ e) (the t (next e)))))
(define start t (next zero))
