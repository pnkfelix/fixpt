;; => (24 32 40 7 4 8 16)
;; Flat products and arrays (`TODO.md` §77), laid out as C does: each
;; scalar aligned to its size, a product padded to its widest member.
;; `extract` of a blobref to a product, and `blobref-index` of one to an
;; array, give blobrefs to the part, at its offset: no bytes are copied.
(define-type pt (productof (x f64) (n i32) (y f64)))
(define-type pts (arrayof pt 3))
(define-type o (bloblet (fields) @b))
(define b o (make-bloblet 72))
(define arr (blobref o pts) (blobref-at b 0))
(define p1 (blobref o pt) (blobref-index arr 1))
(blobref-set! (extract p1 y) 2.5)
(blobref-set! (extract p1 n) 7)
;; An `i32` then an `f64`: the `f64` at 8, after 4 bytes of padding.
(define-type q (productof (a i32) (b i32) (c f64) (d i32)))
(define q0 (blobref o q) (blobref-at b 0))
(list (blobref-offset (extract p1 x)) (blobref-offset (extract p1 n))
      (blobref-offset (extract p1 y))
      (i32->int (blobref-get (extract (blobref-index arr 1) n)))
      (blobref-offset (extract q0 b)) (blobref-offset (extract q0 c))
      (blobref-offset
       (extract (blobref-index (the (blobref o (arrayof q 2)) (blobref-at b 0)) 0) d)))
