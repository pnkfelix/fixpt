;; => 2
;; A transparent type function, `(dlambda ((a type)) (listof a @heap))`,
;; sealed as an abstract constructor; and a dependent procedure over any
;; container, applying its constructor at two types in one call.
;; What walking a list and building another may do.
(define-effect walks (maxeff (read @heap) (alloc @heap) spin))
(define-type container
  (moduleof (abs f (=> (type) type))
            (val wrap (poly ((a type)) (subr (alloc @heap) (a) (f a))))
            (val size (poly ((a type)) (subr (maxeff (read @heap) spin) ((f a)) int)))
            (val fmap (poly ((a type) (b type))
                        (subr walks ((subr pure (a) b) (f a)) (f b))))))
(define lists container
  (module
    (define-type f (dlambda ((a type)) (listof a @heap)))
    (define wrap (poly ((a type)) (subr (alloc @heap) (a) (f a)))
      (plambda ((a type)) (lambda (x) (list x x))))
    (define-rec (size (poly ((a type)) (subr (maxeff (read @heap) spin) ((f a)) int))
      (plambda ((a type)) (lambda (xs) (if (null? xs) 0 (+ 1 ((proj size a) (cdr xs))))))))
    (define-rec (fmap (poly ((a type) (b type))
                        (subr walks ((subr pure (a) b) (f a)) (f b)))
      (plambda ((a type) (b type))
        (lambda (g xs) (if (null? xs) nil (cons (g (car xs)) ((proj fmap a b) g (cdr xs))))))))))
(define pair-up
  (subr (maxeff (read @heap) (alloc @heap) spin)
        ((c container) ((select c f) int))
        ((select c f) (productof (l int) (r int))))
  (lambda ((c container) (xs ((select c f) int)))
    (with c ((proj fmap int (productof (l int) (r int))) (lambda (x) (product (l x) (r x))) xs))))
(let ((c lists))
  (with c ((proj size (productof (l int) (r int))) (pair-up c ((proj wrap int) 3)))))
