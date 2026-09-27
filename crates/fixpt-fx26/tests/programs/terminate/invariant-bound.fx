;;; Up to `n`, which every call passes on unchanged; and down to it, in the
;;; other member of a pair that passes it back and forth.
(define up (subr pure (int int) int) (lambda (i n) (if (< i n) (up (+ i 1) n) i)))
(define-rec (down (subr pure (int int) int) (lambda (i n) (if (> i n) (down2 (- i 1) n) i)))
            (down2 (subr pure (int int) int) (lambda (i n) (if (> i n) (down (- i 1) n) i))))
(+ (up 0 10) (down 10 0))
