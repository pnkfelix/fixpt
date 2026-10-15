;; => 3531604001
;; A built-in file of one expression (`load-input`): the arm64 encoder
;; written in FX-26, a module, as a code generator would load it
;; (`TODO.md` §97). `movz x0, #1`.
(define a64 (load-input "fx26:arm64.fx"))
(+ ((with a64 arm-movz) 0 1 0) 1)
