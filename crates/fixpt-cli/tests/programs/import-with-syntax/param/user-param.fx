;; Takes lib.fx's instance as a parameter, and imports its macros, in a
;; `hide`: they mean that instance's names.
(module-parameters
  ((m-base (load-moduleof "base.fx")) (m-lib (load-moduleof "lib.fx" m-base))))
(hide (import-with-syntax m-lib (only make-thing plus-offset)))
(define one (make-thing (product (n (plus-offset 1)))))
