;; A file of module parameters with a macro of its own that binds the name
;; `loop`, which `together-a.fx` has a macro of (`fasl.rs`; TODO §294).
(module-parameters ((m-a (load-moduleof "together-a.fx"))))
(define-syntax iterate
  (syntax-rules
    ((_ go eff ((x t i) ...) r body)
     (letrec ((go (subr eff (t ...) r) (lambda (x ...) body)))
       (go i ...)))))
(define f (subr pure ((select m-a n)) (select m-a n))
  (lambda (n) (iterate loop pure ((i (select m-a n) n)) (select m-a n) i)))
