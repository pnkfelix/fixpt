;;; `nat`: a natural, and an `int`; a literal is one, and `(nat 3)` is
;;; exactly 3. `+` of naturals is a natural of the sum.
(define three (nat 3) 3)
(define four (nat 4) (+ three 1))
(define some nat four)
(define as-int int some)
(define seven (nat 7) (+ three four))
(+ seven as-int)
