;; => 10.0
;; A flat array of a length not literal (TODO.md §77) runs to the end of its
;; owner's suffix: here a record's samples, after its count. Binding the
;; record's blobref names its length (`r`), and the samples have that length;
;; procedures polymorphic in the length take them, the size solved from the
;; argument.
(define-type blob (bloblet (fields) @heap))
(define-type rec (productof (count u32) (pad u32) (data (arrayof f64 finite))))
(define* fill!
  (poly ((n size))
    (subr (maxeff (read @heap) (write @heap) spin) ((blobref blob (arrayof f64 n)) int int) unit))
  (plambda ((n size))
    (lambda (s i k)
      (if (>= i k)
          #u
          (begin (blobref-set! (blobref-index s i) (int->f64 i)) ((proj fill! n) s (+ i 1) k))))))
(define* total
  (poly ((n size))
    (subr (maxeff (read @heap) spin) ((blobref blob (arrayof f64 n)) int int f64) f64))
  (plambda ((n size))
    (lambda (s i k acc)
      (if (>= i k)
          acc
          (let ((x (blobref-get (blobref-index s i))))
            ((proj total n) s (+ i 1) k (f64+ acc x)))))))
(define main
  (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin (read (globals fill! total))) () f64)
  (lambda ()
    (let* ((b (the blob (make-bloblet 48)))
           (r (the (blobref blob rec) (blobref-at b 0)))
           (s (extract r data)))
      (begin (fill! s 0 5) (total s 0 5 0.)))))
(main)
