;; ! `extend` of a module with abstract types of its own is not supported yet
;; A module with abstract types of its own is not extended, yet (`TODO.md`
;; §69): what the two's abstract types become in the one is to decide.
(define b (module (define x int 1)))
(extend (module (define-generative t int) (define y int 2)) b)
