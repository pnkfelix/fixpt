;;; SET -- Set benchmark for (scheme set).
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/set.scm),
;;; ported to FX-26. Larceny's input: 5 iterations of (go 6).
;;; Answer: (x0 x1 x2 x3 x4 x5).
;;;
;;; FX-26 has no (scheme set), (scheme comparator) or (scheme hash-table),
;;; so the layers under the benchmark are written here:
;;; - SRFI 113's sets, after Larceny's (John Cowan's reference
;;;   implementation, lib/SRFI/srfi/113.body.scm): a set ("sob") is a
;;;   record of a hash table of elements to counts and a comparator, and
;;;   each operation the benchmark calls is written as there: `set-find`
;;;   and `set=?` escape from a walk with `call/cc` (`cwcc`), `set-remove`
;;;   and `set-filter` walk into an empty copy, `set-union` walks both
;;;   sets, `set-adjoin` copies, `set->list` folds.
;;; - SRFI 69's hash tables, after Larceny's (lib/SRFI/srfi/%3a69.sls):
;;;   `hash-table-update!/default` a ref then a set, and
;;;   `hash-table-walk` a snapshot of the entries, keys and values in two
;;;   new vectors, then a walk of those.
;;; - UNDER THEM, A HASH TABLE WRITTEN HERE, not Larceny's R6RS hashtables
;;;   (which FX-26 does not have): `crates/fixpt-fx26/src/table.fx`'s
;;;   design, an array of association-list buckets, 8 at first, doubling
;;;   past one entry each, a key's bucket its hash modulo the number of
;;;   buckets; deleting (which the benchmark never does) is left out.
;;; - SRFI 128's comparators, after Larceny's (lib/SRFI/srfi/128.body*.scm,
;;;   Larceny's `equal-hash` from src/Lib/Common/hash.sch): a comparator
;;;   is a record of a type test, an equality and a hash function (no
;;;   ordering: the benchmark orders only symbols, with `symbol<?`,
;;;   called directly). The default comparator's hash of a list is
;;;   `((make-hasher) (equal-hash obj))`, `equal-hash` walking the list
;;;   with a budget of 32; of a fixnum, `equal-hash`'s; sets hash with
;;;   SRFI 113's `sob-hash`. The type test of `permutation-comparator`
;;;   is `list?`, a walk, run on every insertion as there; the others are
;;;   `#t`, since FX-26's types already say so.
;;; What else differs, and why:
;;; - A set of symbols, of sets, of lists and of ints are each a `(sob
;;;   T)`, one polymorphic type, and `set-comparator` is one global for
;;;   each element type it compares sets of (sets of symbols, sets of
;;;   lists), since a global is of one type.
;;; - `symbol-hash`, Larceny's stored hash of a symbol's name (a string
;;;   hash of 27 bits or so), is FX-26's `symbol-name-hash` modulo 2^27.
;;;   `(symbol-hash obj)`, `equal-hash` and `sob-hash` are otherwise as
;;;   there, so that the sums in `sob-hash` stay within fixnums, as they
;;;   do in Larceny for n = 6.
;;; - `set-find`'s failure, `'ignored` in the benchmark, never used (the
;;;   sets are never empty), is a thunk that fails (`car` of nil).
;;; - Checks that the arguments are sets of the same comparator, and
;;;   `sob-multi?` (these are sets, never bags), are left out.
;;; - `list-sort` is Larceny's merge sort (`sort!!`, as in listsort.fx),
;;;   for symbols.
;;; - The comparators' procedures are kept in data, so each has one type,
;;;   `cmps`, which reads every global some of them reads.

(define-effect cmps
  (maxeff (read @heap) (write @heap) (alloc @heap) spin
          (read (globals symbol-hash syms-list? syms-equal? hasher salt hash-bound syms-hash-on-equal
                         combine fixnum-hash set=? sob-hash bucket-find hash-table-ref/default
                         hash-table-size hash-table-walk table-find))))

(define-type syms (listof symbol @heap))
(define-type ints (listof int @heap))

;; A comparator: type test, equality, hash.
(define-type (comparator (k type))
  (bloblet (fields (subr cmps (k) bool) (subr cmps (k k) bool) (subr cmps (k) int)) @heap))
(define-type (entry (k type)) (pairof k int @heap))
(define-type (bucket (k type)) (listof (entry k) acyclic))
;; A hash table: its comparator's equality and hash, buckets, count.
(define-type (table (k type))
  (bloblet (fields (subr cmps (k k) bool) (subr cmps (k) int) (arrayof (bucket k) @heap) int) @heap))
;; A set: its hash table and comparator.
(define-type (sob (k type)) (bloblet (fields (table k) (comparator k)) @heap))

;;; The hash table.

(define* make-table
  (poly ((k type)) (subr cmps ((subr cmps (k k) bool) (subr cmps (k) int)) (table k)))
  (plambda ((k type))
    (lambda (same hash)
      (make-bloblet 0 same hash (the (arrayof (bucket k) @heap) (make-array 8 nil)) 0))))

(define* bucket-find
  (poly ((k type)) (subr cmps ((bucket k) k (subr cmps (k k) bool)) (entry k)))
  (plambda ((k type))
    (lambda (b key same)
      (cond ((null? b) nil)
            ((same (car (car b)) key) (car b))
            (else (bucket-find (cdr b) key same))))))

(define* table-find
  (poly ((k type)) (subr cmps ((table k) k) (entry k)))
  (plambda ((k type))
    (lambda (t key)
      (let ((buckets (bloblet-ref t 2)))
        (bucket-find (array-ref buckets (modulo ((bloblet-ref t 1) key) (array-length buckets)))
                     key
                     (bloblet-ref t 0))))))

(define* hash-table-ref/default
  (poly ((k type)) (subr cmps ((table k) k int) int))
  (plambda ((k type))
    (lambda (t key default)
      (let ((e (table-find t key)))
        (if (null? e) default (cdr e))))))

(define* hash-table-contains?
  (poly ((k type)) (subr cmps ((table k) k) bool))
  (plambda ((k type))
    (lambda (t key) (not (null? (table-find t key))))))

(define* hash-table-size
  (poly ((k type)) (subr (read @heap) ((table k)) int))
  (plambda ((k type)) (lambda (t) (bloblet-ref t 3))))

;; Move every entry of bucket `b` into the array `new`.
(define* rehash-bucket
  (poly ((k type)) (subr cmps ((table k) (bucket k) (arrayof (bucket k) @heap)) unit))
  (plambda ((k type))
    (lambda (t b new)
      (if (null? b)
          #u
          (let ((j (modulo ((bloblet-ref t 1) (car (car b))) (array-length new))))
            (begin (array-set! new j (cons (car b) (array-ref new j)))
                   (rehash-bucket t (cdr b) new)))))))

;; Double the buckets once there are more entries than buckets.
(define* table-grow
  (poly ((k type)) (subr cmps ((table k)) unit))
  (plambda ((k type))
    (lambda (t)
      (let ((old (bloblet-ref t 2)))
        (if (> (bloblet-ref t 3) (array-length old))
            (let ((new (the (arrayof (bucket k) @heap) (make-array (* 2 (array-length old)) nil))))
              (letrec ((rehash-array (subr (maxeff cmps (read (globals rehash-bucket))) (int) unit)
                         (lambda (i)
                           (if (>= i (array-length old))
                               #u
                               (begin (rehash-bucket t (array-ref old i) new)
                                      (rehash-array (+ i 1)))))))
                (begin (rehash-array 0)
                       (bloblet-set! t 2 new))))
            #u)))))

(define* hash-table-set!
  (poly ((k type)) (subr cmps ((table k) k int) unit))
  (plambda ((k type))
    (lambda (t key value)
      (let* ((buckets (bloblet-ref t 2))
             (i (modulo ((bloblet-ref t 1) key) (array-length buckets)))
             (e (bucket-find (array-ref buckets i) key (bloblet-ref t 0))))
        (if (null? e)
            (begin (array-set! buckets i (cons (cons key value) (array-ref buckets i)))
                   (bloblet-set! t 3 (+ (bloblet-ref t 3) 1))
                   (table-grow t))
            (set-cdr! e value))))))

;; SRFI 69's (hash-table-set! ht key (f (hash-table-ref/default ht key default))),
;; for the one `f` sets use, (lambda (value) 1).
(define* hash-table-update!/default-1
  (poly ((k type)) (subr cmps ((table k) k int) unit))
  (plambda ((k type))
    (lambda (t key default)
      (let ((value (hash-table-ref/default t key default)))
        (hash-table-set! t key 1)))))

;; hashtable-copy: the same buckets, each entry copied.
(define* hash-table-copy
  (poly ((k type)) (subr cmps ((table k)) (table k)))
  (plambda ((k type))
    (lambda (t)
      (let* ((old (bloblet-ref t 2))
             (new (the (arrayof (bucket k) @heap) (make-array (array-length old) nil))))
        (letrec ((copy-bucket (subr cmps ((bucket k)) (bucket k))
                   (lambda (b) (if (null? b) nil (cons (cons (car (car b)) (cdr (car b))) (copy-bucket (cdr b))))))
                 (loop (subr cmps (int) (table k))
                   (lambda (i)
                     (if (= i (array-length old))
                         (make-bloblet 0 (bloblet-ref t 0) (bloblet-ref t 1) new (bloblet-ref t 3))
                         (begin (array-set! new i (copy-bucket (array-ref old i)))
                                (loop (+ i 1)))))))
          (loop 0))))))

;; SRFI 69's hash-table-walk: (hashtable-entries ht), two new vectors,
;; then (vector-for-each f keys values).
(define* hash-table-walk
  (poly ((k type) (e effect)) (subr (maxeff e cmps) ((table k) (subr e (k int) unit)) unit))
  (plambda ((k type) (e effect))
    (lambda (t f)
      (let* ((buckets (bloblet-ref t 2))
             (n (bloblet-ref t 3)))
        (if (= n 0)
            #u
            (let* ((first (car (car (letrec ((nonempty (subr cmps (int) (bucket k))
                                               (lambda (i) (if (null? (array-ref buckets i)) (nonempty (+ i 1)) (array-ref buckets i)))))
                                      (nonempty 0)))))
                   (keys (the (arrayof k @heap) (make-array n first)))
                   (values (the (arrayof int @heap) (make-array n 0))))
              (letrec ((fill-bucket (subr cmps ((bucket k) int) int)
                         (lambda (b j)
                           (if (null? b)
                               j
                               (begin (array-set! keys j (car (car b)))
                                      (array-set! values j (cdr (car b)))
                                      (fill-bucket (cdr b) (+ j 1))))))
                       (fill (subr cmps (int int) unit)
                         (lambda (i j)
                           (if (= i (array-length buckets))
                               #u
                               (fill (+ i 1) (fill-bucket (array-ref buckets i) j)))))
                       (walk (subr (maxeff e cmps) (int) unit)
                         (lambda (i)
                           (if (= i n)
                               #u
                               (begin (f (array-ref keys i) (array-ref values i))
                                      (walk (+ i 1)))))))
                (begin (fill 0 0)
                       (walk 0)))))))))

;;; Comparators (SRFI 128).

(define* comparator-test-type
  (poly ((k type)) (subr cmps ((comparator k) k) bool))
  (plambda ((k type)) (lambda (c x) ((bloblet-ref c 0) x))))

(define* comparator-equal?
  (poly ((k type)) (subr cmps ((comparator k) k k) bool))
  (plambda ((k type)) (lambda (c a b) ((bloblet-ref c 1) a b))))

(define* comparator-hash
  (poly ((k type)) (subr cmps ((comparator k) k) int))
  (plambda ((k type)) (lambda (c x) ((bloblet-ref c 2) x))))

(define hash-bound int 33554432)
(define salt int 16064047)

;; Larceny's symbol-hash (see above).
(define* symbol-hash (subr pure (symbol) int)
  (lambda (s) (modulo (symbol-name-hash s) 134217728)))

;; string<? on symbols' names.
(define* symbol<? (subr spin (symbol symbol) bool)
  (lambda (a b)
    (let ((s (symbol->string a)) (t (symbol->string b)))
      (letrec ((loop (subr spin (int) bool)
                 (lambda (i)
                   (cond ((= i (string-length t)) #f)
                         ((= i (string-length s)) #t)
                         ((< (char->integer (string-ref s i)) (char->integer (string-ref t i))) #t)
                         ((> (char->integer (string-ref s i)) (char->integer (string-ref t i))) #f)
                         (else (loop (+ i 1)))))))
        (loop 0)))))

;; Larceny's equal-hash (src/Lib/Common/hash.sch), for what it is given
;; here: fixnums not negative, and lists of symbols.
(define* combine (subr pure (int int) int)
  (lambda (hash adjustment) (modulo (+ hash (+ hash (+ hash adjustment))) 16777216)))
(define* fixnum-hash (subr pure (int) int)                ; (object-hash x)
  (lambda (x) (combine x 9000000)))
(define* syms-hash-on-equal (subr (maxeff (read @heap) spin) (syms int) int)
  (lambda (x budget)
    (cond ((<= budget 0) 2321004)                           ; adj:weird
          ((null? x) (combine 3 3000444))                   ; (object-hash '())
          (else
           (let ((budget (quotient budget 2)))
             (combine (if (> budget 0) (symbol-hash (car x)) 2321004)
                      (syms-hash-on-equal (cdr x) budget)))))))
;; ((make-hasher) n)
(define* hasher (subr pure (int) int)
  (lambda (n) (+ (modulo (* salt 33) hash-bound) n)))

(define* syms-equal? (subr (maxeff (read @heap) spin) (syms syms) bool)
  (lambda (a b)
    (cond ((null? a) (null? b))
          ((null? b) #f)
          ((symbol=? (car a) (car b)) (syms-equal? (cdr a) (cdr b)))
          (else #f))))

(define* syms-list? (subr (maxeff (read @heap) spin) (syms) bool)
  (lambda (x) (if (null? x) #t (syms-list? (cdr x)))))

(define symbol-comparator (comparator symbol)
  ;; (make-comparator symbol? eq? (lambda (sym1 sym2) ...) symbol-hash)
  (make-bloblet 0
                (lambda ((x symbol)) #t)
                (lambda ((a symbol) (b symbol)) (symbol=? a b))
                (lambda ((x symbol)) (symbol-hash x))))

(define permutation-comparator (comparator syms)
  ;; (make-comparator list? equal? permutation<? default-hash)
  (make-bloblet 0
                (lambda ((x syms)) (syms-list? x))
                (lambda ((a syms) (b syms)) (syms-equal? a b))
                (lambda ((x syms)) (hasher (syms-hash-on-equal x 32)))))

(define* make-default-comparator (subr (alloc @heap) () (comparator int))
  (lambda ()
    (make-bloblet 0
                  (lambda ((x int)) #t)
                  (lambda ((a int) (b int)) (= a b))           ; default-equality, type 6
                  (lambda ((x int)) (fixnum-hash x)))))        ; default-hash, number-hash

;;; Sets (SRFI 113).

(define* make-sob
  (poly ((k type)) (subr cmps ((comparator k)) (sob k)))
  (plambda ((k type))
    (lambda (comparator)
      (make-bloblet 0 (make-table (bloblet-ref comparator 1) (bloblet-ref comparator 2)) comparator))))

(define* sob-copy
  (poly ((k type)) (subr cmps ((sob k)) (sob k)))
  (plambda ((k type))
    (lambda (sob) (make-bloblet 0 (hash-table-copy (bloblet-ref sob 0)) (bloblet-ref sob 1)))))

(define* sob-empty-copy
  (poly ((k type)) (subr cmps ((sob k)) (sob k)))
  (plambda ((k type)) (lambda (sob) (make-sob (bloblet-ref sob 1)))))

;; (sob-increment! sob element 1), for a set
(define* sob-increment!
  (poly ((k type)) (subr cmps ((sob k) k) unit))
  (plambda ((k type))
    (lambda (sob element)
      (begin (comparator-test-type (bloblet-ref sob 1) element)   ; check-element
             (hash-table-update!/default-1 (bloblet-ref sob 0) element 0)))))

(define* set-contains?
  (poly ((k type)) (subr cmps ((sob k) k) bool))
  (plambda ((k type)) (lambda (set member) (hash-table-contains? (bloblet-ref set 0) member))))

(define* set-empty?
  (poly ((k type)) (subr cmps ((sob k)) bool))
  (plambda ((k type)) (lambda (set) (= 0 (hash-table-size (bloblet-ref set 0))))))

(define* set-find
  (poly ((k type) (e effect)) (subr (maxeff e cmps) ((subr e (k) bool) (sob k) (subr cmps () k)) k))
  (plambda ((k type) (e effect))
    (lambda (pred sob failure)
      (cwcc
       (lambda ((return (subr (goto @k) (k) void)))
         (begin
           (hash-table-walk (bloblet-ref sob 0)
                            (lambda ((key k) (value int))
                              (if (pred key) (return key) #u)))
           (failure)))))))

;; set-filter and set-remove, as sob-filter
(define* set-filter
  (poly ((k type) (e effect)) (subr (maxeff e cmps) ((subr e (k) bool) (sob k)) (sob k)))
  (plambda ((k type) (e effect))
    (lambda (pred sob)
      (let ((result (sob-empty-copy sob)))
        (begin
          (hash-table-walk (bloblet-ref sob 0)
                           (lambda ((key k) (value int))
                             (if (pred key) (sob-increment! result key) #u)))
          result)))))

(define* set-remove
  (poly ((k type) (e effect)) (subr (maxeff e cmps) ((subr e (k) bool) (sob k)) (sob k)))
  (plambda ((k type) (e effect))
    (lambda (pred set) (set-filter (lambda ((x k)) (not (pred x))) set))))

(define* set-map
  (poly ((a type) (b type) (e effect)) (subr (maxeff e cmps) ((subr e (a) b) (comparator b) (sob a)) (sob b)))
  (plambda ((a type) (b type) (e effect))
    (lambda (proc comparator sob)
      (let ((result (make-sob comparator)))
        (begin
          (hash-table-walk (bloblet-ref sob 0)
                           (lambda ((key a) (value int)) (sob-increment! result (proc key))))
          result)))))

(define* set-adjoin
  (poly ((k type)) (subr cmps ((sob k) k) (sob k)))
  (plambda ((k type))
    (lambda (set element)
      (let ((result (sob-copy set)))
        (begin (sob-increment! result element)
               result)))))

(define* set=?
  (poly ((k type)) (subr cmps ((sob k) (sob k)) bool))
  (plambda ((k type))
    (lambda (sob1 sob2)
      ;; dyadic-sob=?
      (cwcc
       (lambda ((return (subr (goto @k) (bool) void)))
         (let ((ht1 (bloblet-ref sob1 0))
               (ht2 (bloblet-ref sob2 0)))
           (begin
             (if (not (= (hash-table-size ht1) (hash-table-size ht2)))
                 (return #f)
                 #u)
             (hash-table-walk ht1
                              (lambda ((key k) (value int))
                                (if (not (= value (hash-table-ref/default ht2 key 0)))
                                    (return #f)
                                    #u)))
             #t)))))))

(define* set-union
  (poly ((k type)) (subr cmps ((sob k) (sob k)) (sob k)))
  (plambda ((k type))
    (lambda (sob1 sob2)
      (let ((result (sob-empty-copy sob1)))
        ;; dyadic-sob-union!
        (let ((sob1-ht (bloblet-ref sob1 0))
              (sob2-ht (bloblet-ref sob2 0))
              (result-ht (bloblet-ref result 0)))
          (begin
            (hash-table-walk sob1-ht
                             (lambda ((key k) (value1 int))
                               (let ((value2 (hash-table-ref/default sob2-ht key 0)))
                                 (hash-table-set! result-ht key (if (> value1 value2) value1 value2)))))
            (hash-table-walk sob2-ht
                             (lambda ((key k) (value2 int))
                               (let ((value1 (hash-table-ref/default sob1-ht key 0)))
                                 (if (= value1 0)
                                     (hash-table-set! result-ht key value2)
                                     #u))))
            result))))))

;; set->list, as sob-fold of cons: sob-for-each calls the procedure
;; `value` times (do-n-times), here once.
(define* set->list
  (poly ((k type)) (subr cmps ((sob k)) (listof k @heap)))
  (plambda ((k type))
    (lambda (sob)
      (let ((result (the (ref (listof k @heap) @heap) (new nil))))
        (begin
          (hash-table-walk (bloblet-ref sob 0)
                           (lambda ((key k) (value int))
                             (letrec ((do-n-times (subr cmps (int) unit)
                                        (lambda (n)
                                          (if (> n 0)
                                              (begin (set result (cons key (get result)))
                                                     (do-n-times (- n 1)))
                                              #u))))
                               (do-n-times value))))
          (get result))))))

(define* list->set
  (poly ((k type)) (subr cmps ((comparator k) (listof k @heap)) (sob k)))
  (plambda ((k type))
    (lambda (comparator list)
      (let ((sob (make-sob comparator)))
        (letrec ((loop (subr (maxeff cmps (read (globals comparator-test-type hash-table-set! hash-table-update!/default-1 rehash-bucket sob-increment! table-grow))) ((listof k @heap)) (sob k))
                   (lambda (l) (if (null? l) sob (begin (sob-increment! sob (car l)) (loop (cdr l)))))))
          (loop list))))))

;; sob-hash: (sob-fold (lambda (element result) (+ (hash element) (* result 33))) 5381 sob)
(define* sob-hash
  (poly ((k type)) (subr cmps ((sob k)) int))
  (plambda ((k type))
    (lambda (sob)
      (let ((hash (bloblet-ref (bloblet-ref sob 1) 2))
            (result (the (ref int @heap) (new 5381))))
        (begin
          (hash-table-walk (bloblet-ref sob 0)
                           (lambda ((key k) (value int))
                             (letrec ((do-n-times (subr cmps (int) unit)
                                        (lambda (n)
                                          (if (> n 0)
                                              (begin (set result (+ (hash key) (* (get result) 33)))
                                                     (do-n-times (- n 1)))
                                              #u))))
                               (do-n-times value))))
          (get result))))))

;; set-comparator, (make-comparator set? set=? #f sob-hash), for sets of
;; symbols and for sets of lists
(define set-comparator-syms (comparator (sob symbol))
  (make-bloblet 0
                (lambda ((x (sob symbol))) #t)
                (lambda ((a (sob symbol)) (b (sob symbol))) (set=? a b))
                (lambda ((x (sob symbol))) (sob-hash x))))
(define set-comparator-perms (comparator (sob syms))
  (make-bloblet 0
                (lambda ((x (sob syms))) #t)
                (lambda ((a (sob syms)) (b (sob syms))) (set=? a b))
                (lambda ((x (sob syms))) (sob-hash x))))

;; set-find's failure (see above)
(define* no-element
  (poly ((k type)) (subr cmps () k))
  (plambda ((k type)) (lambda () (car (the (listof k @heap) nil)))))

;;; The benchmark.

;;; Returns the union of the sets contained in s,
;;; which must be non-empty (else there's no way to know what
;;; the comparator should be for the result).

(define* big-set-union (subr cmps ((sob (sob syms))) (sob syms))
  (lambda (s)
    (letrec ((loop (subr (maxeff cmps (read (globals comparator-test-type hash-table-set! hash-table-update!/default-1 make-sob make-table no-element rehash-bucket set-empty? set-filter set-find set-remove set-union sob-empty-copy sob-increment! table-grow))) ((sob (sob syms)) (sob syms)) (sob syms))
               (lambda (s partial-result)
                 (if (set-empty? s)
                     partial-result
                     (let* ((s0 (set-find (lambda ((x (sob syms))) #t) s no-element))
                            (s (set-remove (lambda ((y (sob syms))) (set=? s0 y)) s)))
                       (loop s (set-union s0 partial-result)))))))
      (let* ((s0 (set-find (lambda ((x (sob syms))) #t) s no-element))
             (s (set-remove (lambda ((y (sob syms))) (set=? s0 y)) s)))
        (loop s s0)))))

;;; SRFI 113 now includes a post-finalization note that says
;;; the order of arguments to set-unfold should be as used here.

(define* symbols (subr cmps (int) (sob symbol))
  (lambda (n)
    ;; (set-unfold (lambda (i) (= i n)) (lambda (i) (string->symbol ...)) (lambda (i) (+ i 1)) 0 symbol-comparator)
    (let ((result (make-sob symbol-comparator)))
      (letrec ((loop (subr (maxeff cmps (read (globals comparator-test-type hash-table-set! hash-table-update!/default-1 rehash-bucket sob-increment! table-grow))) (int) (sob symbol))
                 (lambda (seed)
                   (if (= seed n)
                       result
                       (begin (sob-increment! result (string->symbol (string-append "x" (int->string seed))))
                              (loop (+ seed 1)))))))
        (loop 0)))))

;;; SRFI 113 now includes a post-finalization note that says
;;; the order of arguments to set-map should be as used here.

(define* powerset (subr cmps ((sob symbol)) (sob (sob symbol)))
  (lambda (universe)
    (if (set-empty? universe)
        (let ((s (make-sob set-comparator-syms)))   ; (set set-comparator universe)
          (begin (sob-increment! s universe) s))
        (let* ((x (set-find (lambda ((x symbol)) #t) universe no-element))
               (u2 (set-remove (lambda ((y symbol)) (symbol=? x y)) universe))
               (pu2 (powerset u2)))
          (set-union pu2
                     (set-map (lambda ((y (sob symbol)))
                                (set-adjoin y x))
                              set-comparator-syms
                              pu2))))))

;;; SRFI 113 now includes a post-finalization note that says
;;; the order of arguments to set-map and set-unfold should be
;;; as used here.

(define* take (subr cmps (syms int) syms)
  (lambda (lis k) (if (= k 0) nil (cons (car lis) (take (cdr lis) (- k 1))))))
(define* drop (subr cmps (syms int) syms)
  (lambda (lis k) (if (= k 0) lis (drop (cdr lis) (- k 1)))))
(define* append2 (subr cmps (syms syms) syms)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (append2 (cdr xs) ys)))))
(define* syms-length (subr cmps (syms) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (syms-length (cdr xs))))))
(define* iota (subr cmps (int) ints)
  (lambda (count)
    (letrec ((loop (subr cmps (int int ints) ints)
               (lambda (count val ans)
                 (if (<= count 0) ans (loop (- count 1) (- val 1) (cons val ans))))))
      (loop count (- count 1) nil))))

(define* permutations (subr cmps ((sob symbol)) (sob syms))
  (lambda (universe)
    (if (set-empty? universe)
        (let ((s (make-sob permutation-comparator)))   ; (set permutation-comparator '())
          (begin (sob-increment! s nil) s))
        (let* ((x (set-find (lambda ((x symbol)) #t) universe no-element))
               (u2 (set-remove (lambda ((y symbol)) (symbol=? x y)) universe))
               (perms2 (permutations u2)))
          (big-set-union
           (set-map (lambda ((perm syms))
                      (set-map (lambda ((i int))
                                 (append2 (take perm i)
                                          (cons x (drop perm i))))
                               permutation-comparator
                               (list->set
                                (make-default-comparator)
                                (iota (+ 1 (syms-length perm))))))
                    set-comparator-perms
                    perms2))))))

;; Larceny's list-sort (sort!!, merge!!; see listsort.fx), for symbols.
(define* merge!! (subr cmps (syms syms) syms)
  (lambda (a b)
    (letrec ((loop (subr (maxeff cmps (read (globals symbol<?))) (syms syms syms) unit)
               (lambda (r a b)
                 (if (symbol<? (car b) (car a))
                     (begin (set-cdr! r b)
                            (if (null? (cdr b)) (set-cdr! b a) (loop b a (cdr b))))
                     (begin (set-cdr! r a)
                            (if (null? (cdr a)) (set-cdr! a b) (loop a (cdr a) b)))))))
      (cond ((null? a) b)
            ((null? b) a)
            ((symbol<? (car b) (car a))
             (begin (if (null? (cdr b)) (set-cdr! b a) (loop b a (cdr b))) b))
            (else
             (begin (if (null? (cdr a)) (set-cdr! a b) (loop a (cdr a) b)) a))))))

(define* list-sort (subr cmps (syms) syms)
  (lambda (seq0)
    (let ((seq (the (ref syms @heap) (new (append2 seq0 nil)))))   ; (list-copy seq)
      (letrec ((step (subr (maxeff cmps (read (globals merge!! symbol<?))) (int) syms)
                 (lambda (n)
                   (cond ((> n 2)
                          (let* ((j (quotient n 2))
                                 (a (step j))
                                 (k (- n j))
                                 (b (step k)))
                            (merge!! a b)))
                         ((= n 2)
                          (let ((x (car (get seq)))
                                (y (car (cdr (get seq))))
                                (p (get seq)))
                            (begin
                              (set seq (cdr (cdr (get seq))))
                              (if (symbol<? y x)
                                  (begin (set-car! p y) (set-car! (cdr p) x))
                                  #u)
                              (set-cdr! (cdr p) nil)
                              p)))
                         ((= n 1)
                          (let ((p (get seq)))
                            (begin (set seq (cdr (get seq)))
                                   (set-cdr! p nil)
                                   p)))
                         (else (the syms nil))))))
        (step (syms-length (get seq)))))))

(define* go (subr cmps (int) syms)
  (lambda (n)
    (let* ((universe (symbols n))
           (subsets (powerset universe))
           (perms (permutations universe))
           (syms (set-filter (lambda ((syms (sob symbol)))
                               (set-contains? perms (set->list syms)))
                             subsets)))
      (list-sort (set->list (car (set->list syms)))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 6)
(define iterations int 5)

(define* run (subr cmps (int syms) syms)
  (lambda (i result) (if (= i 0) result (run (- i 1) (go input1)))))
(run iterations nil)
