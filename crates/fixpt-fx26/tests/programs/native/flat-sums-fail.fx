;;; A flat sum's variant set to a label none of the owner's fields holds,
;;; and a tag past the owner's fields: in line natively, each fails as the
;;; primitive says (`direct.rs`'s `flat_sums_as_the_rust_machine_gives_them`).
(define-type s (sumof (a f64) (b f64)))
(define-type o (bloblet (fields symbol) @heap))
(define* mk (subr (maxeff (alloc @heap) (read @heap)) (int) (blobref o s))
  (lambda (k) (blobref-at (the o (make-bloblet 16 'a)) 0)))
(define* var (subr (maxeff (alloc @heap) (read @heap) (write @heap)) (int) int)
  (lambda (k) (blobref-offset (blobref-variant! (mk k) 'b))))
(define* tag (subr (maxeff (alloc @heap) (read @heap) (write @heap)) (int) int)
  (lambda (k)
    (let ((r (mk k)))
      (begin (bloblet-set-byte! (blobref-owner r) 0 k) (tagcase r (a x 1) (b y 2))))))
