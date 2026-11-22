;; Takes env.fx's module, and imports the macros of its instance of lib.fx,
;; by a path, in a `hide`: they mean that instance's names, through `env`,
;; which a local `env` at a use does not capture.
(module-parameters ((env (load-moduleof "env.fx"))))
(hide (import-with-syntax env::m-lib (only make-thing plus-offset)))
(define one (make-thing (product (n (plus-offset 1)))))
(define two (let ((env 5)) (make-thing (product (n (plus-offset env))))))
