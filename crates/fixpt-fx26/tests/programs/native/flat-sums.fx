;;; Flat sums natively (`TODO.md` §77): an array of them, each made one
;;; variant or the other by `blobref-variant!`, the tag an index into the
;;; owner's fields, then read back by `tagcase`; a numeric key too; and
;;; loops that allocate as they go, so that a collection moves the owner
;;; under the refs they hold.
(define-type shape (sumof (circle f64) (square (productof (w i32) (h i32)))))
(define-type o (bloblet (fields symbol symbol) @heap))
(define-type shapes (blobref o (arrayof shape 8)))
(define* fill (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin) (shapes int) int)
  (lambda (arr i)
    (if (= i 8)
        0
        (begin
          (if (= (modulo i 2) 0)
              (blobref-set! (blobref-variant! (blobref-index arr i) 'circle) (int->f64 i))
              (let ((sq (blobref-variant! (blobref-index arr i) 'square)))
                (begin (blobref-set! (extract sq w) (int->i32 i))
                       (blobref-set! (extract sq h) (int->i32 3)))))
          (let ((junk (list i i i))) (fill arr (+ i 1)))))))
(define* area (subr (maxeff (read @heap)) ((blobref o shape)) int)
  (lambda (s)
    (tagcase s
      (circle c (f64->int (blobref-get c)))
      (square p (* (i32->int (blobref-get (extract p w)))
                   (i32->int (blobref-get (extract p h))))))))
(define* total (subr (maxeff (alloc @heap) (read @heap) spin) (shapes int int) int)
  (lambda (arr i acc)
    (if (= i 8)
        acc
        (let ((junk (list i i i)))
          (total arr (+ i 1) (+ (* acc 10) (area (blobref-index arr i))))))))
(define-type k (sumof u16 (0 f64) (7 i32)))
(define* keyed (subr (maxeff (read @heap)) ((blobref o k)) int)
  (lambda (r) (tagcase r (0 x -1) (else y (blobref-offset y)))))
(define-type ints (listof int @heap))
(define* flat-sums (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin) (int) ints)
  (lambda (n)
    (let* ((b (the o (make-bloblet 144 'square 'circle)))
           (arr (the shapes (blobref-at b 0)))
           (kr (the (blobref o k) (blobref-at b 128))))
      (begin
        (fill arr 0)
        (blobref-set! (blobref-variant! kr 7) (int->i32 n))
        (list (total arr 0 0) (keyed kr) (bloblet-byte b 0) (bloblet-byte b 16)
              (bloblet-byte b 128) (bloblet-byte b 129))))))
(flat-sums 5)
