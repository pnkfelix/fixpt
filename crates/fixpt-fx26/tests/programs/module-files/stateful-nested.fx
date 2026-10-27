;; A module file that loads a pure one, then makes state as it is made:
;; refused, and the pure one's load with it (`tests/top.rs`).
(define part (load-module "pure-part.fx"))
(define cell (ref int @heap) (new 0))
