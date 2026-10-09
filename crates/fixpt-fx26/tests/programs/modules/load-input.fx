;; => 42
;; A file of one expression is its value (`load-input`): here a procedure
;; making a module of what it is given. Two loads of a path are one value,
;; made once (`TODO.md` §68).
(define make (load-input "../module-files/maker.fx"))
(define again (load-input "../module-files/maker.fx"))
(let ((a (make 20)) (b (again 1))) (+ (with a twice) (with b twice)))
