;; More of `counter.fx`'s program, run after it is resumed (`fixpt resume
;; IMAGE more.fx`): a form run, a definition, and `main` defined again.
(bump!)
(define twice (subr (maxeff (read @heap) (write @heap) (read (globals count bump!))) () int)
  (lambda () (begin (bump!) (bump!) (get count))))
(define main
  (subr (maxeff (io stdout) (read @heap) (write @heap) (read (globals bump! count twice))) () int)
  (lambda () (begin (write-out (string-append "twice: " (int->string (twice)) "\n")) 3)))
