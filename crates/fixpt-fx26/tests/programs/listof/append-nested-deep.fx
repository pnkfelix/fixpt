;; => 40
;; `append` nested 40 deep, each call's arguments synthesized to
;; instantiate it: each looked at once, so checked in time linear in the
;; depth (both checkers checked a `vsubr`'s arguments again, and took time
;; exponential in it: 12 deep took a second, 17 deep minutes; `TODO.md` §277).
(define xs (listof int acyclic)
  (append (cons 39 nil) (append (cons 38 nil) (append (cons 37 nil) (append (cons 36 nil)
  (append (cons 35 nil) (append (cons 34 nil) (append (cons 33 nil) (append (cons 32 nil)
  (append (cons 31 nil) (append (cons 30 nil) (append (cons 29 nil) (append (cons 28 nil)
  (append (cons 27 nil) (append (cons 26 nil) (append (cons 25 nil) (append (cons 24 nil)
  (append (cons 23 nil) (append (cons 22 nil) (append (cons 21 nil) (append (cons 20 nil)
  (append (cons 19 nil) (append (cons 18 nil) (append (cons 17 nil) (append (cons 16 nil)
  (append (cons 15 nil) (append (cons 14 nil) (append (cons 13 nil) (append (cons 12 nil)
  (append (cons 11 nil) (append (cons 10 nil) (append (cons 9 nil) (append (cons 8 nil)
  (append (cons 7 nil) (append (cons 6 nil) (append (cons 5 nil) (append (cons 4 nil)
  (append (cons 3 nil) (append (cons 2 nil) (append (cons 1 nil) (append (cons 0 nil)
  nil)))))))))))))))))))))))))))))))))))))))))
(list-length xs)
