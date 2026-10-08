;;; HASHTABLE0 -- Hashtable benchmark. Tests only eq? and eqv? hashtables.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/hashtable0.scm),
;;; ported to FX-26. Larceny's input: 50 iterations of
;;; (hash-table-eq-tests 100000 make-eq-hash-table) then
;;; (hash-table-eq-tests 100000 make-eqv-hash-table).
;;; Answer: 102005 (the size of the last table: 2005 plus the number of
;;; items added to stress it), if every test passed; if one failed, the
;;; answer is the number of the last test that failed, negated.
;;;
;;; THIS MEASURES A HASH TABLE WRITTEN HERE, IN FX-26, NOT LARCENY'S.
;;; FX-26 has no hash tables as a standard operation, no `eq?` on objects
;;; and no hashing by address, so the port carries its own table and gives
;;; each key object an identity to hash and compare:
;;; - The table is `crates/fixpt-fx26/src/table.fx`'s design, written for
;;;   these keys and values: a bloblet of an array of association-list
;;;   buckets (spines frozen, entries changed in place) and a count, the
;;;   buckets doubling past one entry each, starting at 8. A key's bucket is
;;;   its identity modulo the number of buckets.
;;; - A key is a frozen pair of its identity and the object: each object a
;;;   key is made for (the string, symbol, vector and lists the benchmark
;;;   makes) gets a fresh serial number, negative, from a counter; a fixnum
;;;   key is its own identity, its value (n2, the one fixnum key, is not
;;;   negative). `eq?` and `eqv?` on keys compare identities, so the eq?
;;;   and the eqv? tables are the same table, as they are for these keys.
;;;   Making a key costs a pair more than its object.
;;; - Keys' objects and the values are `datum`s, Scheme values: the values
;;;   are symbols (made once, as quoted symbols are) and fixnums, which
;;;   cost nothing to make a datum of. `(eq? 'a v)` is asked of a datum as
;;;   "is a symbol, and `symbol=?` to a"; `(eq? not-found v)`, of the fresh
;;;   list `not-found`, as "is a list whose first element is the symbol
;;;   not-found" (the only such value the table could hold is none).
;;; - `report-failure!` records the failure; it prints nothing. The unused
;;;   escape `exit` (`call-with-current-continuation`) is left out.

; Copyright 2007 William D Clinger.
;
; Permission to copy this software, in whole or in part, to use this
; software for any lawful purpose, and to redistribute this software
; is granted subject to the restriction that all copies made of this
; software must include this copyright notice in full.
;
; I also request that you send me a copy of any improvements that you
; make to this software so that they may be incorporated within it to
; the benefit of the Scheme community.

(define-type key (pairof int datum acyclic))          ; (identity . object)
(define-type entry (union nil (pairof key datum @heap)))          ; (key . value)
(define-type bucket (listof entry acyclic))
(define-type table (bloblet (fields (arrayof bucket @heap) int) @heap))  ; buckets, count
(define-effect tables (maxeff (read @heap) (write @heap) (alloc @heap) spin))

;;; Keys.

(define serial (ref int @heap) (new 0))

;; A key for an object, with a fresh identity.
(define* make-key (subr tables (datum) key)
  (lambda (obj)
    (begin (set serial (- (get serial) 1))
           (cons (get serial) obj))))

;; A fixnum key: its value is its identity.
(define* fixnum-key (subr pure (int) key)
  (lambda (n) (cons n n)))

(define* same-key? (subr pure (key key) bool)
  (lambda (a b) (= (car a) (car b))))

;;; The table.

(define* make-table (subr tables () table)
  (lambda () (make-bloblet 0 (the (arrayof bucket @heap) (make-array 8 nil)) 0)))

(define* bucket-of (subr pure (key int) int)
  (lambda (key n) (modulo (car key) n)))

;; The entry for `key` in a bucket, or nil.
(define* bucket-find (subr tables (bucket key) entry)
  (lambda (b key)
    (cond ((null? b) no-pair)
          ((same-key? (car (car b)) key) (car b))
          (else (bucket-find (cdr b) key)))))

(define* hash-table-ref/default (subr tables (table key datum) datum)
  (lambda (t key default)
    (let* ((buckets (bloblet-ref t 0))
           (e (bucket-find (array-ref buckets (bucket-of key (array-length buckets))) key)))
      (if (null? e) default (cdr e)))))

(define* hash-table-size (subr tables (table) int)
  (lambda (t) (bloblet-ref t 1)))

;; Move every entry of bucket `b` into the array `new`.
(define* rehash-bucket (subr tables (bucket (arrayof bucket @heap)) unit)
  (lambda (b new)
    (if (null? b)
        #u
        (let ((j (bucket-of (car (car b)) (array-length new))))
          (begin (array-set! new j (cons (car b) (array-ref new j)))
                 (rehash-bucket (cdr b) new))))))

;; Double the buckets once there are more entries than buckets.
(define* table-grow (subr tables (table) unit)
  (lambda (t)
    (let ((old (bloblet-ref t 0)))
      (if (> (bloblet-ref t 1) (array-length old))
          (let ((new (the (arrayof bucket @heap) (make-array (* 2 (array-length old)) nil))))
            (letrec ((rehash-array (subr (maxeff tables (read (globals rehash-bucket bucket-of))) (int) unit)
                       (lambda (i)
                         (if (>= i (array-length old))
                             #u
                             (begin (rehash-bucket (array-ref old i) new)
                                    (rehash-array (+ i 1)))))))
              (begin (rehash-array 0)
                     (bloblet-set! t 0 new))))
          #u))))

(define* hash-table-set! (subr tables (table key datum) unit)
  (lambda (t key value)
    (let* ((buckets (bloblet-ref t 0))
           (i (bucket-of key (array-length buckets)))
           (e (bucket-find (array-ref buckets i) key)))
      (if (null? e)
          (begin (array-set! buckets i (cons (cons key value) (array-ref buckets i)))
                 (bloblet-set! t 1 (+ (bloblet-ref t 1) 1))
                 (table-grow t))
          (set-cdr! e value)))))

(define-type maker (subr (maxeff tables (read (globals make-table))) () table))
(define make-eq-hash-table maker (lambda () (make-table)))
(define make-eqv-hash-table maker (lambda () (make-table)))

;;; The benchmark.

; Crude test rig, just for benchmarking.

(define failures (ref (listof int @heap) @heap) (new nil))

(define* report-failure! (subr tables (int) unit)
  (lambda (n) (set failures (cons n (get failures)))))

(define datum-nil datum nil)
(define sym-a datum 'a)
(define sym-b datum 'b)
(define sym-c datum 'c)
(define sym-d datum 'd)
(define sym-e datum 'e)

;; (eq? s v), s a symbol
(define* eq-symbol? (subr pure (datum datum) bool)
  (lambda (s v) (and (symbol? s) (symbol? v) (symbol=? s v))))

;; (eq? not-found v)
(define* not-found? (subr pure (datum) bool)
  (lambda (v)
    (and (pair? v)
         (symbol? (car v))
         (symbol=? (car v) 'not-found))))

; The parameter n2 is the number of items to be added to the table
; during the stress phase.

(define* hash-table-eq-tests (subr tables (int maker) int)
  (lambda (n2 maker)
    (let ((test (lambda ((n int) (passed? bool))
                  (if (not passed?)
                      (report-failure! n)
                      #u))))
      (let ((t (maker))
            (not-found (the datum (cons 'not-found nil)))
            (x1 (make-key "abc"))                       ; (string #\a #\b #\c)
            (sym1 (make-key 'sym1))
            (vec1 (make-key (datum-list->vector (the datum (cons 'vec1 nil)))))
            (pair1 (make-key (the datum (cons -1 nil))))
            (n2-key (fixnum-key n2))
            (n1 1000)             ; population added in first phase
           ;(n2 10000)            ; population added in second phase
            (n3 1000))            ; population added in third phase

        (let ((hash-table-get (lambda ((t table) (key key))
                                (hash-table-ref/default t key #f)))
              ;; (do ((i 0 (+ i 1))) ((= i n)) (hash-table-set! t (list i) i))
              (add (lambda ((t table) (n int))
                     (letrec ((loop (subr (maxeff tables (read (globals hash-table-set! bucket-of bucket-find same-key? table-grow
                                                                          rehash-bucket make-key serial datum-nil)))
                                          (int) unit)
                                (lambda (i)
                                  (if (= i n)
                                      #u
                                      (begin (hash-table-set! t (make-key (cons i datum-nil)) i)
                                             (loop (+ i 1)))))))
                       (loop 0)))))
          (begin
            (test 1 (not-found? (hash-table-ref/default t x1 not-found)))
            (hash-table-set! t x1 sym-a)
            (test 2 (eq-symbol? sym-a (hash-table-get t x1)))
            (hash-table-set! t sym1 sym-b)
            (test 3 (eq-symbol? sym-a (hash-table-get t x1)))
            (test 4 (eq-symbol? sym-b (hash-table-get t sym1)))
            (hash-table-set! t vec1 sym-c)
            (test 5 (eq-symbol? sym-a (hash-table-get t x1)))
            (test 6 (eq-symbol? sym-b (hash-table-get t sym1)))
            (test 7 (eq-symbol? sym-c (hash-table-get t vec1)))
            (hash-table-set! t n2-key sym-d)
            (test 8 (eq-symbol? sym-a (hash-table-get t x1)))
            (test 9 (eq-symbol? sym-b (hash-table-get t sym1)))
            (test 10 (eq-symbol? sym-c (hash-table-get t vec1)))
            (test 11 (eq-symbol? sym-d (hash-table-get t n2-key)))

            (hash-table-set! t pair1 sym-e)

            (add t n1)
            (test 12 (eq-symbol? sym-e (hash-table-get t pair1)))
            (add t n2)
            (test 13 (eq-symbol? sym-e (hash-table-get t pair1)))
            (letrec ((loop (subr (maxeff tables (read (globals hash-table-set! bucket-of bucket-find same-key? table-grow
                                                                 rehash-bucket make-key serial datum-nil
                                                                 hash-table-ref/default report-failure! failures
                                                                 eq-symbol? sym-e)))
                                 (int) unit)
                       (lambda (i)
                         (if (= i n3)
                             #u
                             (begin
                               (test 14 (eq-symbol? sym-e (hash-table-get t pair1)))
                               (hash-table-set! t (make-key (cons i datum-nil)) i)
                               (loop (+ i 1)))))))
              (loop 0))
            (test 15 (eq-symbol? sym-a (hash-table-get t x1)))
            (test 16 (eq-symbol? sym-b (hash-table-get t sym1)))
            (test 17 (eq-symbol? sym-c (hash-table-get t vec1)))
            (test 18 (eq-symbol? sym-d (hash-table-get t n2-key)))
            (test 19 (eq-symbol? sym-e (hash-table-get t pair1)))

            (hash-table-size t)))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 100000)
(define input2 int 100000)
(define iterations int 50)

(define* run (subr tables (int int) int)
  (lambda (i result)
    (if (= i 0)
        result
        (begin (hash-table-eq-tests input1 make-eq-hash-table)
               (run (- i 1) (hash-table-eq-tests input2 make-eqv-hash-table))))))
(let ((result (run iterations 0)))
  (if (null? (get failures)) result (- 0 (car (get failures)))))
