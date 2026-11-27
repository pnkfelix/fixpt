;;; What staged code sees, made of the modules a file is given, each
;;; `include`d: their names and types, none restated (Heist's
;;; `fixpt-live-modules.md`, gap 4). The staging is in `included/c.fx`, a
;;; module file over `a.fx` and `b.fx`, as Heist's eval.fx is over view.fx.
(define a (load-module "included/a.fx"))
(define b ((load-module "included/b.fx") a))
(define c ((load-module "included/c.fx") a b))
((with c reload!) '(lambda (p) (string-append "new " (show (mk (extract p y) 0)))))
(write-out (string-append ((with c try)) "\n"))
((with c reload!) '(lambda (p) (begin (write-out "x") "bad")))
(write-out (string-append ((with c try)) "\n"))
