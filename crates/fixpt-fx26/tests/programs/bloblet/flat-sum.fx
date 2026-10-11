;; => (1 21 1 0 8 24 99 7 0 -1)
;; Flat sums (`TODO.md` §77): a tag, then the variant at the widest one's
;; alignment. With no key, the tag is a byte indexing the owner's fields,
;; which hold the labels; with a key, `u8`, `u16` or `u32`, the labels are
;; numbers, stored as they are. `blobref-variant!` sets the tag and gives a
;; blobref to the variant; `tagcase` gives each arm one.
(define-type shape (sumof (circle f64) (square (productof (w i32) (h i32)))))
(define-type o (bloblet (fields symbol symbol) @b))
(define b o (make-bloblet 48 'square 'circle))
(define arr (blobref o (arrayof shape 2)) (blobref-at b 0))
(define c (blobref o f64) (blobref-variant! (blobref-index arr 0) 'circle))
(blobref-set! c 2.5)
(define sq (blobref o (productof (w i32) (h i32))) (blobref-variant! (blobref-index arr 1) 'square))
(blobref-set! (extract sq w) 7)
(blobref-set! (extract sq h) 3)
(define what (subr (read @b) ((blobref o shape)) int)
  (lambda (s)
    (tagcase s
      (circle x 1)
      (square p (* (i32->int (blobref-get (extract p w)))
                   (i32->int (blobref-get (extract p h))))))))
(define-type k (sumof u16 (0 f64) (7 i32)))
(define kr (blobref o k) (blobref-at b 32))
(blobref-set! (blobref-variant! kr 7) 99)
(list (what (blobref-index arr 0)) (what (blobref-index arr 1))
      (bloblet-byte b 0) (bloblet-byte b 16)
      (blobref-offset c) (blobref-offset sq)
      (tagcase kr (0 x 0) (7 y (i32->int (blobref-get y))))
      (bloblet-byte b 32) (bloblet-byte b 33)
      (tagcase (blobref-index arr 1) (circle x 0) (else y -1)))
