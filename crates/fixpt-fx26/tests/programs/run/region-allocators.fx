;;; Every allocator with a region to allocate in: a reference, an array, an
;;; I-cell and a bloblet, made in a `letrena`'s region, used there, and
;;; only an int given back.
(define tally (subr spin (int) int)
  (lambda (n)
    (letrena r
      (let* ((acc (the (ref int r) (rnew r 0)))
             (xs (the (arrayof int r) (rmake-array r n 1)))
             (c (the (icell int r) (rmake-icell r)))
             (blob (the (bloblet (fields int int) r) (rmake-bloblet r 0 10 20))))
        (letrec ((go (subr (maxeff (read r) (write r) spin) (int) unit)
                   (lambda (i)
                     (if (= i n)
                         #u
                         (begin (set acc (+ (get acc) (array-ref xs i))) (go (+ i 1)))))))
          (begin
            (go 0)
            (icell-put! c (get acc))
            (+ (icell-get c) (+ (bloblet-ref blob 0) (bloblet-ref blob 1)))))))))

;; cons-chain: the list is in @l
(the (listof int @l) (cons (tally 5) (cons (tally 100) nil)))
