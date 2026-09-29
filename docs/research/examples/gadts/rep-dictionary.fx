;;; FX-26 today: a type representation as a dictionary of the operations
;;; a generic function needs, built by one constructor per type former.
;;; `show` works at any type that has a `rep`. What the GADT `Rep a` adds
;;; is that a rep can be *inspected*: a `tagcase` on it learns what `a`
;;; is, so one generic function can serve every operation, and two reps can
;;; be compared to give an `(eq a b)`. A dictionary is closed: only the
;;; operations put in it.
(define-type (rep (a type)) (productof (show (subr pure (a) string))))
(define r-int (rep int) (product (show (lambda ((n int)) (int->string n)))))
(define r-bool (rep bool) (product (show (lambda ((b bool)) (if b "#t" "#f")))))
(define r-pair
  (poly ((a type) (b type)) (subr pure ((rep a) (rep b)) (rep (productof (l a) (r b)))))
  (lambda (ra rb)
    (product (show (lambda ((p (productof (l a) (r b))))
                     (let ((open (string-append "(" ((extract ra show) (extract p l))))
                           (close (string-append ((extract rb show) (extract p r)) ")")))
                       (string-append open (string-append " . " close))))))))
(define show (poly ((a type)) (subr pure ((rep a) a) string)) (lambda (r x) ((extract r show) x)))
(show (r-pair r-int (r-pair r-bool r-int)) (product (l 1) (r (product (l #t) (r 2)))))
