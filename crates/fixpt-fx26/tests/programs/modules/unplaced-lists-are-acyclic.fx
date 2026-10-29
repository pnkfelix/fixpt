;; => 18
;; A list a call makes where nothing says its region is `acyclic`, the
;; `poly` only making data there (Heist's request, 2026-10-29, `TODO.md`
;; §174): so it is given, with nothing said, to what takes an `acyclic`
;; list, in each of the shapes that needed `(the (listof T acyclic) …)`:
;; a `let`'s binding, an `if` in one, a lambda's result given to a `poly`,
;; a call's result given to another, a primitive's list given to one.
(define* map (poly ((p place) (r region))
               (subr (maxeff (read (acyclic p)) (alloc r) spin)
                     ((subr pure (int) int) (listof int (acyclic p)))
                     (listof int r)))
  (plambda ((p place) (r region))
    (lambda (f l) (if (null? l) (the (listof int r) nil) (cons (f (car l)) (map f (cdr l)))))))
(define* len (subr spin ((listof int acyclic)) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (len (cdr xs))))))
(define inc (subr pure (int) int) (lambda (x) (+ x 1)))
(define xs (listof int acyclic) (list 1 2 3))
(define in-let int (let ((ys (map inc xs))) (len ys)))
(define in-if int (let ((ys (if (null? xs) xs (map inc xs)))) (len ys)))
(define nested int (len (map inc (map inc xs))))
(define from-list int (len (map inc (list 1 2 3))))
(define one (->* ((listof int acyclic)) int) (lambda (l) (len (map inc l))))
(+ in-let (+ in-if (+ nested (+ from-list (+ (one xs) 3)))))
