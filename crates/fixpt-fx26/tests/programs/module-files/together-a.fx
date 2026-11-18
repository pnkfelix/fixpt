;; A file with a macro `loop`, which `together-b.fx`'s own macro binds as a
;; name: compiled before it in one `compile-file`, `together-b.fasl` keeps
;; its maker still (`fasl.rs`; TODO §294).
(module-parameters ())
(define-syntax loop (syntax-rules ((_ e) e)))
(hide (define m-c (load-module "together-c.fx")))
(define-type n int)
(define three n (loop (with m-c k)))
