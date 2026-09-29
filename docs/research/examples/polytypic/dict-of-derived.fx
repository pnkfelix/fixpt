;;; Type classes by hand: a dictionary is a product of operations. The
;;; instance for a datatype would be its derived functions, as
;;; (product (eq tree=?) (show tree->datum)) from derived-copy.fx; the
;;; instance for a type constructor is a function from dictionaries to a
;;; dictionary (Haskell's `instance Eq a => Eq [a]`); consumers
;;; such as `member` are written once and take the dictionary.
(define-type (eqd (t type) (e effect))
  (productof (eq (subr e (t t) bool)) (show (subr e (t) datum))))
(define int-d (eqd int pure)
  (product (eq (lambda (x y) (= x y))) (show (lambda (x) (datum-int x)))))
(define list-d
  (poly ((t type) (e effect)) (subr pure ((eqd t e)) (eqd (listof t acyclic) e)))
  (lambda (d)
    (product
     (eq (lambda (xs ys)
           (letrec ((go (subr e ((listof t acyclic) (listof t acyclic)) bool)
                      (lambda (xs ys)
                        (cond ((null? xs) (null? ys)) ((null? ys) #f)
                              (else (and ((extract d eq) (car xs) (car ys)) (go (cdr xs) (cdr ys))))))))
             (go xs ys))))
     (show (lambda (xs)
             (letrec ((go (subr e ((listof t acyclic)) datum)
                        (lambda (xs)
                          (if (null? xs) (datum-list (the (listof datum @l) nil))
                              (datum-cons ((extract d show) (car xs)) (go (cdr xs)))))))
               (go xs)))))))
(define member
  (poly ((t type) (e effect)) (subr e ((eqd t e) t (listof t acyclic)) bool))
  (lambda (d x xs)
    (letrec ((go (subr e ((listof t acyclic)) bool)
               (lambda (xs) (and (not (null? xs)) (or ((extract d eq) x (car xs)) (go (cdr xs)))))))
      (go xs))))
(define xss (listof (listof int acyclic) acyclic)
  (cons (cons 1 nil) (cons (cons 2 (cons 3 nil)) nil)))
(member (list-d int-d) (cons 2 (cons 3 nil)) xss)
((extract (list-d (list-d int-d)) show) xss)
