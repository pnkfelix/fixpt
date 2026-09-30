;;; FX-26 today, generative: Okasaki's nested sequence (Bird and Meertens'
;;; `Nest`), `(seq a) = nil | cons a (seq (pair a))`. Expansive: the tail is
;;; a sequence of pairs. Two lemmas, each a guarded structural identity
;;; that calls itself at the growing argument `(pair a)`, handing itself a
;;; coercion for pairs built from the one it was given:
;;; - `seq-up`, variance: (seq a) <= (seq b) given a <= b;
;;; - `seq-twin`: (seq a) <= (seq2 b) given a <= b, between two families
;;;   of one shape.
(define-type (pair (a type)) (productof (l a) (r a)))
(define-generative (seq (a type))
  (sumof (nil unit) (cons (productof (hd a) (tl (seq (pair a)))))))
(define-generative (seq2 (a type))
  (sumof (nil unit) (cons (productof (hd a) (tl (seq2 (pair a)))))))
(define* seq-up (proves (poly ((a type) (b type)) (<= (seq a) (seq b)) (<= a b)))
  (lambda (f s)
    (up-seq (tagcase (down-seq s)
              (nil u (sum nil u))
              (cons (hd tl)
                (sum cons (product (hd (f hd))
                                   (tl (seq-up (lambda ((p (pair a)))
                                                 (product (l (f (extract p l)))
                                                          (r (f (extract p r)))))
                                               tl)))))))))
(define* seq-twin (proves (poly ((a type) (b type)) (<= (seq a) (seq2 b)) (<= a b)))
  (lambda (f s)
    (up-seq2 (tagcase (down-seq s)
               (nil u (sum nil u))
               (cons (hd tl)
                 (sum cons (product (hd (f hd))
                                    (tl (seq-twin (lambda ((p (pair a)))
                                                    (product (l (f (extract p l)))
                                                             (r (f (extract p r)))))
                                                  tl)))))))))
(define small (seq (sumof (x int)))
  (up-seq (sum cons (product (hd (sum x 1)) (tl (up-seq (sum nil #u)))))))
(define wide (seq (sumof (x int) (y bool))) small)        ; by seq-up
(define other (seq2 (sumof (x int) (y bool))) small)      ; by seq-twin
