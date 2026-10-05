;; => 8
;; A loaded file that loads another (`../module-files/nests.fx` loads
;; `option.fx`, from its own directory): both checkers read both, the
;; driver supplying each file to the FX-26 parser where its form is.
(define n (load-module "../module-files/nests.fx"))
(with n eight)
