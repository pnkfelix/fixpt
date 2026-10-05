;;; Hash tables, written in FX-26 over bloblets (PLAN.md §11, step 7).
;;;
;;; A table is a bloblet of its key's hash and equality, an array of
;;; buckets, and a count. A bucket is an association list, its spine
;;; `acyclic` (made by `cons` onto a bucket, never written), so that walking
;;; it ends; an entry is a pair `(key . value)` in the table's region,
;;; changed in place when a key is set again. When there are more entries
;;; than buckets, the buckets double.
;;;
;;; Generic in the key, the value and the region, as `cons` is. A table of
;;; symbols to ints in `@r`:
;;;   (the (table symbol int @r) (make-table symbol-hash symbol=?))
(define-type (bucket (k type) (v type) (r region)) (listof (pairof k v r) acyclic))
(define-type (bucket-array (k type) (v type) (r region)) (arrayof (bucket k v r) r))
;; A key's hash, and whether two keys are the same.
(define-type (key-hash (k type)) (subr pure (k) int))
(define-type (key-same (k type)) (subr pure (k k) bool))
(define-type (table (k type) (v type) (r region))
  (bloblet (fields (key-hash k) (key-same k) (bucket-array k v r) int) r))

;;; Rehashing: moving the entries of an `a` into new buckets, as `b` says,
;;; reading, writing and consing in the table's region.
(define-type (rehashing (k type) (v type) (r region) (a type) (b type))
  (subr (maxeff (read @globals) (read r) (write r) (alloc r)) ((table k v r) a b) unit))

;; The procedures, a module (`TODO.md` §34: the front end into modules,
;; a file at a time); the types above it, which it and other files name.
(define tables
  (module
    ;; Whether `n` names the empty list: `nil`, or `no-pair`, the same value at
    ;; any pair type (`standard.rs`).
    (define std-nil-name? (subr pure (string) bool)
      (lambda (n) (or (string=? n "nil") (string=? n "no-pair"))))
    (define symbol-hash (subr pure (symbol) int) (lambda (s) (symbol-name-hash s)))

    (define make-table
      (poly ((r region)) (poly ((k type) (v type))
        (subr (alloc r) ((key-hash k) (key-same k)) (table k v r))))
      (plambda ((r region)) (plambda ((k type) (v type))
        (lambda ((hash (key-hash k)) (same (key-same k)))
          (the (table k v r) (make-bloblet 0 hash same (make-array 8 nil) 0))))))

    ;;; The entry for `key` in a bucket, or nil.
    (define-rec (bucket-find
      (poly ((r region)) (poly ((k type) (v type))
        (subr (maxeff (read @globals) (read r)) ((bucket k v r) k (key-same k)) (pairof k v r))))
      (plambda ((r region)) (plambda ((k type) (v type))
        (lambda ((b (bucket k v r)) (key k) (same (key-same k)))
          (cond ((null? b) no-pair)
                ((same (car (car b)) key) (car b))
                (else (bucket-find (cdr b) key same))))))))

    ;;; Which bucket `key` belongs in, of `n`.
    (define bucket-of
      (poly ((r region)) (poly ((k type) (v type))
        (subr (read r) ((table k v r) k int) int)))
      (plambda ((r region)) (plambda ((k type) (v type))
        (lambda ((t (table k v r)) (key k) (n int)) (modulo ((bloblet-ref t 0) key) n)))))

    ;;; The entry for `key` in `t`, or nil.
    (define table-entry
      (poly ((r region)) (poly ((k type) (v type))
        (subr (maxeff (read @globals) (read r)) ((table k v r) k) (pairof k v r))))
      (plambda ((r region)) (plambda ((k type) (v type))
        (lambda ((t (table k v r)) (key k))
          (let* ((buckets (bloblet-ref t 2))
                 (b (array-ref buckets (bucket-of t key (array-length buckets)))))
            (bucket-find b key (bloblet-ref t 1)))))))

    (define table-ref
      (poly ((r region)) (poly ((k type) (v type))
        (subr (maxeff (read @globals) (read r)) ((table k v r) k v) v)))
      (plambda ((r region)) (plambda ((k type) (v type))
        (lambda ((t (table k v r)) (key k) (default v))
          (let ((e (table-entry t key)))
            (if (null? e) default (cdr e)))))))

    (define table-has?
      (poly ((r region)) (poly ((k type) (v type))
        (subr (maxeff (read @globals) (read r)) ((table k v r) k) bool)))
      (plambda ((r region)) (plambda ((k type) (v type))
        (lambda ((t (table k v r)) (key k))
          (not (null? (table-entry t key)))))))

    (define table-count
      (poly ((r region)) (poly ((k type) (v type)) (subr (read r) ((table k v r)) int)))
      (plambda ((r region)) (plambda ((k type) (v type))
        (lambda ((t (table k v r))) (bloblet-ref t 3)))))

    ;;; Move every entry of bucket `b` into the array `new`.
    (define-rec (rehash-bucket
      (poly ((r region)) (poly ((k type) (v type))
        (rehashing k v r (bucket k v r) (bucket-array k v r))))
      (plambda ((r region)) (plambda ((k type) (v type))
        (lambda ((t (table k v r)) (b (bucket k v r)) (new (bucket-array k v r)))
          (if (null? b)
              #u
              (let ((j (bucket-of t (car (car b)) (array-length new))))
                (begin (array-set! new j (cons (car b) (array-ref new j)))
                       (rehash-bucket t (cdr b) new)))))))))

    ;;; Buckets `i` on of `old` into the table's, new ones.
    (define-rec (rehash-array
      (poly ((r region)) (poly ((k type) (v type))
        (rehashing k v r (bucket-array k v r) int)))
      (plambda ((r region)) (plambda ((k type) (v type))
        (lambda ((t (table k v r)) (old (bucket-array k v r)) (i int))
          (if (>= i (array-length old))
              #u
              (begin (rehash-bucket t (array-ref old i) (bloblet-ref t 2))
                     (rehash-array t old (+ i 1)))))))))

    ;;; Double the buckets once there are more entries than buckets.
    (define table-grow
      (poly ((r region)) (poly ((k type) (v type))
        (subr (maxeff (read @globals) (read r) (write r) (alloc r)) ((table k v r)) unit)))
      (plambda ((r region)) (plambda ((k type) (v type))
        (lambda ((t (table k v r)))
          (let ((old (bloblet-ref t 2)))
            (if (> (bloblet-ref t 3) (array-length old))
                (let ((new (the (bucket-array k v r) (make-array (* 2 (array-length old)) nil))))
                  (begin (bloblet-set! t 2 new)
                         (rehash-array t old 0)))
                #u))))))

    (define table-set!
      (poly ((r region)) (poly ((k type) (v type))
        (subr (maxeff (read @globals) (read r) (write r) (alloc r)) ((table k v r) k v) unit)))
      (plambda ((r region)) (plambda ((k type) (v type))
        (lambda ((t (table k v r)) (key k) (value v))
          (let* ((buckets (bloblet-ref t 2))
                 (i (bucket-of t key (array-length buckets)))
                 (e (bucket-find (array-ref buckets i) key (bloblet-ref t 1))))
            (if (null? e)
                (begin (array-set! buckets i (cons (cons key value) (array-ref buckets i)))
                       (bloblet-set! t 3 (+ (bloblet-ref t 3) 1))
                       (table-grow t))
                (set-cdr! e value)))))))))

;; What other files use, as before the module; its helpers stay inside it.
(define std-nil-name? (with tables std-nil-name?))
(define symbol-hash (with tables symbol-hash))
(define make-table (with tables make-table))
(define table-ref (with tables table-ref))
(define table-has? (with tables table-has?))
(define table-set! (with tables table-set!))
(define table-count (with tables table-count))
