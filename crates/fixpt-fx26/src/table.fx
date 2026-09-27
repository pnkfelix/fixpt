;;; Hash tables, written in FX-26 over bloblets (PLAN.md §11, step 7).
;;;
;;; A table is a bloblet of its key's hash and equality, an array of
;;; buckets, and a count. A bucket is an association list; an entry is a
;;; pair `(key . value)`, changed in place when a key is set again. When
;;; there are more entries than buckets, the buckets double.
;;;
;;; Generic in the key, the value and the region, as `cons` is. A table of
;;; symbols to ints in `@r`:
;;;   (the (table symbol int @r) (make-table symbol-hash symbol=?))

(define-type (bucket (k type) (v type) (r region)) (listof (pairof k v r) r))
(define-type (table (k type) (v type) (r region))
  (bloblet (fields (subr pure (k) int) (subr pure (k k) bool) (arrayof (bucket k v r) r) int) r))


(define symbol-hash (subr pure (symbol) int) (lambda (s) (symbol-name-hash s)))

(define make-table
  (poly ((r region)) (poly ((k type) (v type))
    (subr (alloc r) ((subr pure (k) int) (subr pure (k k) bool)) (table k v r))))
  (plambda ((r region)) (plambda ((k type) (v type))
    (lambda ((hash (subr pure (k) int)) (same (subr pure (k k) bool)))
      (the (table k v r) (make-bloblet 0 hash same (make-array 8 nil) 0))))))

;;; The entry for `key` in a bucket, or nil.
(define bucket-find
  (poly ((r region)) (poly ((k type) (v type))
    (subr (maxeff (read r) spin) ((bucket k v r) k (subr pure (k k) bool)) (pairof k v r))))
  (plambda ((r region)) (plambda ((k type) (v type))
    (lambda ((b (bucket k v r)) (key k) (same (subr pure (k k) bool)))
      (cond ((null? b) nil)
            ((same (car (car b)) key) (car b))
            (else (bucket-find (cdr b) key same)))))))

;;; Which bucket `key` belongs in, of `n`.
(define bucket-of
  (poly ((r region)) (poly ((k type) (v type))
    (subr (read r) ((table k v r) k int) int)))
  (plambda ((r region)) (plambda ((k type) (v type))
    (lambda ((t (table k v r)) (key k) (n int)) (modulo ((bloblet-ref t 0) key) n)))))

(define table-ref
  (poly ((r region)) (poly ((k type) (v type))
    (subr (maxeff (read r) spin) ((table k v r) k v) v)))
  (plambda ((r region)) (plambda ((k type) (v type))
    (lambda ((t (table k v r)) (key k) (default v))
      (let* ((buckets (bloblet-ref t 2))
             (e (bucket-find (array-ref buckets (bucket-of t key (array-length buckets))) key (bloblet-ref t 1))))
        (if (null? e) default (cdr e)))))))

(define table-has?
  (poly ((r region)) (poly ((k type) (v type))
    (subr (maxeff (read r) spin) ((table k v r) k) bool)))
  (plambda ((r region)) (plambda ((k type) (v type))
    (lambda ((t (table k v r)) (key k))
      (let ((buckets (bloblet-ref t 2)))
        (not (null? (bucket-find (array-ref buckets (bucket-of t key (array-length buckets))) key (bloblet-ref t 1)))))))))

(define table-count
  (poly ((r region)) (poly ((k type) (v type)) (subr (read r) ((table k v r)) int)))
  (plambda ((r region)) (plambda ((k type) (v type)) (lambda ((t (table k v r))) (bloblet-ref t 3)))))

;;; Move every entry of bucket `b` into the array `new`.
(define rehash-bucket
  (poly ((r region)) (poly ((k type) (v type))
    (subr (maxeff (read r) (write r) (alloc r) spin) ((table k v r) (bucket k v r) (arrayof (bucket k v r) r)) unit)))
  (plambda ((r region)) (plambda ((k type) (v type))
    (lambda ((t (table k v r)) (b (bucket k v r)) (new (arrayof (bucket k v r) r)))
      (if (null? b)
          #u
          (let ((j (bucket-of t (car (car b)) (array-length new))))
            (begin (array-set! new j (cons (car b) (array-ref new j)))
                   (rehash-bucket t (cdr b) new))))))))

(define rehash-array
  (poly ((r region)) (poly ((k type) (v type))
    (subr (maxeff (read r) (write r) (alloc r) spin) ((table k v r) (arrayof (bucket k v r) r) (arrayof (bucket k v r) r) int) unit)))
  (plambda ((r region)) (plambda ((k type) (v type))
    (lambda ((t (table k v r)) (old (arrayof (bucket k v r) r)) (new (arrayof (bucket k v r) r)) (i int))
      (if (= i (array-length old))
          #u
          (begin (rehash-bucket t (array-ref old i) new)
                 (rehash-array t old new (+ i 1))))))))

;;; Double the buckets once there are more entries than buckets.
(define table-grow
  (poly ((r region)) (poly ((k type) (v type))
    (subr (maxeff (read r) (write r) (alloc r) spin) ((table k v r)) unit)))
  (plambda ((r region)) (plambda ((k type) (v type))
    (lambda ((t (table k v r)))
      (let ((old (bloblet-ref t 2)))
        (if (> (bloblet-ref t 3) (array-length old))
            (let ((new (the (arrayof (bucket k v r) r) (make-array (* 2 (array-length old)) nil))))
              (begin (rehash-array t old new 0)
                     (bloblet-set! t 2 new)))
            #u))))))

(define table-set!
  (poly ((r region)) (poly ((k type) (v type))
    (subr (maxeff (read r) (write r) (alloc r) spin) ((table k v r) k v) unit)))
  (plambda ((r region)) (plambda ((k type) (v type))
    (lambda ((t (table k v r)) (key k) (value v))
      (let* ((buckets (bloblet-ref t 2))
             (i (bucket-of t key (array-length buckets)))
             (e (bucket-find (array-ref buckets i) key (bloblet-ref t 1))))
        (if (null? e)
            (begin (array-set! buckets i (cons (cons key value) (array-ref buckets i)))
                   (bloblet-set! t 3 (+ (bloblet-ref t 3) 1))
                   (table-grow t))
            (set-cdr! e value)))))))
