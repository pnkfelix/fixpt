;; A program that loads a module file (`lib.fx`), dumped: its dump is keyed
;; by every file its load read, not only this one (`TODO.md` §189).
(define lib (load-module "lib.fx"))
(define main
  (subr (maxeff (io stdout) (read (globals lib))) () int)
  (lambda ()
    (begin (write-out (string-append "base " (int->string (with lib base)) "\n"))
           0)))
