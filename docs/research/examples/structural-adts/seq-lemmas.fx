;;; FX-26 today, generative: Okasaki's nested sequence (Bird and Meertens'
;;; `Nest`), `(seq a) = nil | cons a (seq (pair a))`. Expansive: the tail is
;;; a sequence of pairs. Two lemmas, each a guarded structural identity
;;; that calls itself at the growing argument `(pair a)`, handing itself a
;;; coercion for pairs built from the one it was given:
;;; - `seq-up`, variance: (seq a) <= (seq b) given a <= b;
;;; - `seq-twin`: (seq a) <= (seq2 b) given a <= b, between two families
;;;   of one shape.
(define-type (pair (a type)) (tupof (l a) (r a)))
(define-generative (seq (a type))
  (oneof (nil unit) (cons (tupof (hd a) (tl (seq (pair a)))))))
(define-generative (seq2 (a type))
  (oneof (nil unit) (cons (tupof (hd a) (tl (seq2 (pair a)))))))
(define* seq-up (proves (poly ((a type) (b type)) (<= (seq a) (seq b)) (<= a b)))
  (lambda (f s)
    (up-seq (tagcase (down-seq s)
              (nil u (one nil u))
              (cons (hd tl)
                (one cons (tup (hd (f hd))
                                   (tl (seq-up (lambda ((p (pair a)))
                                                 (tup (l (f (extract p l)))
                                                          (r (f (extract p r)))))
                                               tl)))))))))
(define* seq-twin (proves (poly ((a type) (b type)) (<= (seq a) (seq2 b)) (<= a b)))
  (lambda (f s)
    (up-seq2 (tagcase (down-seq s)
               (nil u (one nil u))
               (cons (hd tl)
                 (one cons (tup (hd (f hd))
                                    (tl (seq-twin (lambda ((p (pair a)))
                                                    (tup (l (f (extract p l)))
                                                             (r (f (extract p r)))))
                                                  tl)))))))))
(define small (seq (oneof (x int)))
  (up-seq (one cons (tup (hd (one x 1)) (tl (up-seq (one nil #u)))))))
(define wide (seq (oneof (x int) (y bool))) small)        ; by seq-up
(define other (seq2 (oneof (x int) (y bool))) small)      ; by seq-twin
