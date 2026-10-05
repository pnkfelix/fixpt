;; A module's file that loads another, from its own directory.
(define opt (load-module "option.fx"))
(define eight int (with opt (tagcase seven (none () 0) (some (x) (+ x 1)))))
