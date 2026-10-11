;; => 50
;; A procedure inlined where it is called keeps what the checker found in
;; it: a blobref's field (`%suffix-ref+`, not a field of the blobref), a
;; scalar's layout, a flat sum's. `area` is inlined in `total`.
(define-type shape (sumof u8 (0 f64) (1 (productof (w f64) (h f64)))))
(define-type o (bloblet (fields) @heap))
(define-type arr (blobref o (arrayof shape 10)))
(define* fill (subr (maxeff (read @heap) (write @heap) spin) (arr int) unit)
  (lambda (a i)
    (if (= i 10)
        #u
        (begin
          (if (= (modulo i 2) 0)
              (blobref-set! (blobref-variant! (blobref-index a i) 0) (int->f64 i))
              (let ((sq (blobref-variant! (blobref-index a i) 1)))
                (begin (blobref-set! (extract sq w) 2.0) (blobref-set! (extract sq h) 3.0))))
          (fill a (+ i 1))))))
(define* area (subr (maxeff (read @heap)) ((blobref o shape)) f64)
  (lambda (s)
    (tagcase s
      (0 c (blobref-get c))
      (1 p (f64* (blobref-get (extract p w)) (blobref-get (extract p h)))))))
(define* total (subr (maxeff (read @heap) spin) (arr int f64) f64)
  (lambda (a i acc)
    (if (= i 10) acc (total a (+ i 1) (f64+ acc (area (blobref-index a i)))))))
(let* ((b (the o (make-bloblet 240))) (a (the arr (blobref-at b 0))))
  (begin (fill a 0) (f64->int (total a 0 0.0))))
