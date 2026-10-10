;; => 6
;; A hidden `include` of a module with abstract types of its own: its items
;; used inside, none of its names shown (`TODO.md` §69).
(define m (module (hide (include (module (define-generative t int)
                                         (define z t (up-t 5))
                                         (define get (subr pure (t) int) (lambda (c) (down-t c))))))
                  (define w int (+ (get z) 1))))
(with m w)
