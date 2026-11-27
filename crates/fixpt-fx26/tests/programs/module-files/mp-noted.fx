;; Strings among `module-parameters`' binders, comments, as among a
;; module's items (Heist's should-work note, entry 19).
(module-parameters ("The first base, for its doubling."
                    (a (load-moduleof "mp-base.fx") #:qualified)
                    "Another, apart."
                    (b (load-moduleof "mp-base.fx") #:qualified)
                    "No more."))
(define* both (subr pure () int) (lambda () (+ ((with a twice) 3) ((with b twice) 4))))
