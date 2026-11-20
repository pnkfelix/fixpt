;; ! `begin-for-syntax`: cannot read `no-such-file.fx`
;; A phase-1 form's load of no file is refused at the load.
(begin-for-syntax (define m (load-module "no-such-file.fx")))
