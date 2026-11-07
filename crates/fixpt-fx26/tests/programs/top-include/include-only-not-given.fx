;; ! `secret` is nothing `m` gives
;; `only` and `except` list names the module gives.
(define m (load-module "../module-files/include-lib.fx"))
(include m (only zero secret))
zero
