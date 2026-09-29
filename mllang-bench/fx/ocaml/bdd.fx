;;; BDD -- binary decision diagrams: build the hidden weighted bit function
;;; of n variables, hash-consed, with memo caches, and test it.
;;;
;;; From OCaml's classic test programs (testsuite/tests/misc/bdd.ml, ocaml
;;; commit 7da997d28b1a), ported to FX-26; "Translated to OCaml by Xavier
;;; Leroy", "Original code written in SML by ...". The original builds
;;; (hwb 20), its default, tests it on 10 random assignments, and prints
;;; "OK" (the reference output) or "FAILED". The port does the same, once,
;;; and its value is the number of nodes made (`nodeC`) if every test
;;; passed, 0 otherwise: a nonzero value is the reference's "OK". Answer:
;;; 26116.
;;;
;;; What the port changes:
;;; - `bdd` is a `define-datatype`; `Zero` and `One` are made once, as the
;;;   globals `zero` and `one`, which the original also defines, where
;;;   OCaml's constant constructors are immediates. `not`, `eval` are
;;;   `bdd-not`, `bdd-eval`, since FX-26 has those names already.
;;; - `x lsl k` is `x * 2^k`, and `x land sz_1` (sz_1 one less than a power
;;;   of 2, x not negative) is `x modulo (sz_1 + 1)`.
;;; - The generator: OCaml computes `seed * 25173 + 17431` in 63 bits,
;;;   wrapping, and keeps the low bit. FX-26's integers are checked for
;;;   overflow, so the port keeps the seed modulo 2^32, which leaves that
;;;   bit, and so every assignment drawn, as it is.
;;; - `for` loops are local recursive procedures. The two `assert false`
;;;   arms (a bucket holding a `Zero` or `One`, which never happens) give
;;;   back the bucket's node and do nothing, respectively.

(define-datatype bdd (b-one) (b-zero) (node bdd int int bdd))
(define zero bdd (b-zero))
(define one bdd (b-one))

(define-type vars-type (arrayof bool @heap))
(define-type bucket (listof bdd @heap))
(define-type table (arrayof bucket @heap))
(define-effect heapy (maxeff (read @heap) (write @heap) (alloc @heap) spin))

(define* bdd-eval (subr (maxeff (read @heap) spin) (bdd vars-type) bool)
  (lambda (bdd vars)
    (tagcase bdd
      (b-zero () #f)
      (b-one () #t)
      (node (l v id h) (if (array-ref vars v) (bdd-eval h vars) (bdd-eval l vars))))))

(define get-id (subr pure (bdd) int)
  (lambda (bdd)
    (tagcase bdd
      (node (l v id h) id)
      (b-zero () 0)
      (b-one () 1))))

(define init-size-1 int (- (* 8 1024) 1))
(define node-c (ref int @heap) (new 1))
(define sz-1 (ref int @heap) (new init-size-1))
(define htab (ref table @heap) (new (make-array (+ (get sz-1) 1) (the bucket nil))))
(define n-items (ref int @heap) (new 0))
(define hash-val (subr pure (int int int) int)
  (lambda (x y v) (+ (+ (* x 2) y) (* v 4))))

(define* resize (subr heapy (int) unit)
  (lambda (new-size)
    (let* ((arr (get htab))
           (new-sz-1 (- new-size 1))
           (new-arr (the table (make-array new-size (the bucket nil)))))
      (letrec ((copy-bucket (subr (maxeff heapy (read (globals get-id hash-val))) (bucket) unit)
                 (lambda (bucket)
                   (if (null? bucket)
                       #u
                       (let ((n (car bucket)) (ns (cdr bucket)))
                         (tagcase n
                           (node (l v id h)
                             (let ((ind (modulo (hash-val (get-id l) (get-id h) v) (+ new-sz-1 1))))
                               (begin
                                 (array-set! new-arr ind (cons n (array-ref new-arr ind)))
                                 (copy-bucket ns))))
                           (else x #u))))))
               (loop (subr (maxeff heapy (read (globals get-id hash-val sz-1))) (int) unit)
                 (lambda (n)
                   (if (<= n (get sz-1))
                       (begin (copy-bucket (array-ref arr n)) (loop (+ n 1)))
                       #u))))
        (begin
          (loop 0)
          (set htab new-arr)
          (set sz-1 new-sz-1))))))

(define* insert (subr heapy (int int int int bucket bdd) unit)
  (lambda (idl idh v ind bucket new-node)
    (if (<= (get n-items) (get sz-1))
        (begin
          (array-set! (get htab) ind (cons new-node bucket))
          (set n-items (+ (get n-items) 1)))
        (begin
          (resize (+ (+ (get sz-1) (get sz-1)) 2))
          (let ((ind (modulo (hash-val idl idh v) (+ (get sz-1) 1))))
            (array-set! (get htab) ind (cons new-node (array-ref (get htab) ind))))))))

(define* mk-node (subr (maxeff heapy (read @globals)) (bdd int bdd) bdd)
  (lambda (low v high)
    (let ((idl (get-id low))
          (idh (get-id high)))
      (if (= idl idh)
          low
          (let* ((ind (modulo (hash-val idl idh v) (+ (get sz-1) 1)))
                 (bucket (array-ref (get htab) ind)))
            (letrec ((lookup (subr (maxeff heapy (read @globals)) (bucket) bdd)
                       (lambda (b)
                         (if (null? b)
                             (let ((n (node low v (begin (set node-c (+ (get node-c) 1)) (get node-c)) high)))
                               (begin (insert (get-id low) (get-id high) v ind bucket n) n))
                             (let ((n (car b)) (ns (cdr b)))
                               (tagcase n
                                 (node (l v2 id h)
                                   (if (and (= v v2) (= idl (get-id l)) (= idh (get-id h)))
                                       n
                                       (lookup ns)))
                                 (else x n)))))))
              (lookup bucket)))))))

(define-datatype ordering (less) (equal) (greater))

(define cmp-var (subr (read (globals less greater equal)) (int int) ordering)
  (lambda (x y) (cond ((< x y) (less)) ((> x y) (greater)) (else (equal)))))

(define* mk-var (subr (maxeff heapy (read @globals)) (int) bdd)
  (lambda (x) (mk-node zero x one)))

(define cache-size int 1999)
(define andslot1 (arrayof int @heap) (make-array cache-size 0))
(define andslot2 (arrayof int @heap) (make-array cache-size 0))
(define andslot3 (arrayof bdd @heap) (make-array cache-size zero))
(define xorslot1 (arrayof int @heap) (make-array cache-size 0))
(define xorslot2 (arrayof int @heap) (make-array cache-size 0))
(define xorslot3 (arrayof bdd @heap) (make-array cache-size zero))
(define notslot1 (arrayof int @heap) (make-array cache-size 0))
(define notslot2 (arrayof bdd @heap) (make-array cache-size one))
(define* hash (subr pure (int int) int)
  (lambda (x y) (modulo (+ (* x 2) y) cache-size)))

(define* bdd-not (subr (maxeff heapy (read @globals)) (bdd) bdd)
  (lambda (n)
    (tagcase n
      (b-zero () one)
      (b-one () zero)
      (node (l v id r)
        (let ((h (modulo id cache-size)))
          (if (= id (array-ref notslot1 h))
              (array-ref notslot2 h)
              (let ((f (mk-node (bdd-not l) v (bdd-not r))))
                (begin (array-set! notslot1 h id) (array-set! notslot2 h f) f))))))))

(define* and2 (subr (maxeff heapy (read @globals)) (bdd bdd) bdd)
  (lambda (n1 n2)
    (tagcase n1
      (node (l1 v1 i1 r1)
        (tagcase n2
          (node (l2 v2 i2 r2)
            (let ((h (hash i1 i2)))
              (if (and (= i1 (array-ref andslot1 h)) (= i2 (array-ref andslot2 h)))
                  (array-ref andslot3 h)
                  (let ((f (tagcase (cmp-var v1 v2)
                             (equal () (mk-node (and2 l1 l2) v1 (and2 r1 r2)))
                             (less () (mk-node (and2 l1 n2) v1 (and2 r1 n2)))
                             (greater () (mk-node (and2 n1 l2) v2 (and2 n1 r2))))))
                    (begin
                      (array-set! andslot1 h i1)
                      (array-set! andslot2 h i2)
                      (array-set! andslot3 h f)
                      f)))))
          (b-zero () zero)
          (b-one () n1)))
      (b-zero () zero)
      (b-one () n2))))

;; (xor uses the and-cache, as the original does.)
(define* xor (subr (maxeff heapy (read @globals)) (bdd bdd) bdd)
  (lambda (n1 n2)
    (tagcase n1
      (node (l1 v1 i1 r1)
        (tagcase n2
          (node (l2 v2 i2 r2)
            (let ((h (hash i1 i2)))
              (if (and (= i1 (array-ref andslot1 h)) (= i2 (array-ref andslot2 h)))
                  (array-ref andslot3 h)
                  (let ((f (tagcase (cmp-var v1 v2)
                             (equal () (mk-node (xor l1 l2) v1 (xor r1 r2)))
                             (less () (mk-node (xor l1 n2) v1 (xor r1 n2)))
                             (greater () (mk-node (xor n1 l2) v2 (xor n1 r2))))))
                    (begin
                      (array-set! andslot1 h i1)
                      (array-set! andslot2 h i2)
                      (array-set! andslot3 h f)
                      f)))))
          (b-zero () n1)
          (b-one () (bdd-not n1))))
      (b-zero () n2)
      (b-one () (bdd-not n2)))))

(define* hwb (subr (maxeff heapy (read @globals)) (int) bdd)
  (lambda (n)
    (letrec ((h (subr (maxeff heapy (read @globals)) (int int) bdd)
               (lambda (i j)
                 (if (= i j)
                     (mk-var i)
                     (xor (and2 (bdd-not (mk-var j)) (h i (- j 1)))
                          (and2 (mk-var j) (g i (- j 1)))))))
             (g (subr (maxeff heapy (read @globals)) (int int) bdd)
               (lambda (i j)
                 (if (= i j)
                     (mk-var i)
                     (xor (and2 (bdd-not (mk-var i)) (h (+ i 1) j))
                          (and2 (mk-var i) (g (+ i 1) j)))))))
      (h 0 (- n 1)))))

;; Testing
(define seed (ref int @heap) (new 0))

(define* random (subr (maxeff (read @heap) (write @heap)) () bool)
  (lambda ()
    (begin
      (set seed (modulo (+ (* (get seed) 25173) 17431) 4294967296))
      (> (modulo (get seed) 2) 0))))

(define* random-vars (subr heapy (int) vars-type)
  (lambda (n)
    (let ((vars (the vars-type (make-array n #f))))
      (letrec ((loop (subr (maxeff heapy (read (globals random seed))) (int) vars-type)
                 (lambda (i)
                   (if (<= i (- n 1))
                       (begin (array-set! vars i (random)) (loop (+ i 1)))
                       vars))))
        (loop 0)))))

;; `=` on booleans.
(define eq-bool (subr pure (bool bool) bool)
  (lambda (a b) (if a b (not b))))

(define* test-hwb (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (bdd vars-type) bool)
  (lambda (bdd vars)
    ;; We should have
    ;;    eval bdd vars = vars.(n-1) if n > 0
    ;;    eval bdd vars = false if n = 0
    ;; where n is the number of "true" elements in vars.
    (let ((ntrue (the (ref int @heap) (new 0))))
      (letrec ((loop (subr (maxeff (read @heap) (write @heap) spin) (int) unit)
                 (lambda (i)
                   (if (<= i (- (array-length vars) 1))
                       (begin
                         (if (array-ref vars i) (set ntrue (+ (get ntrue) 1)) #u)
                         (loop (+ i 1)))
                       #u))))
        (begin
          (loop 0)
          (eq-bool (bdd-eval bdd vars)
                   (if (> (get ntrue) 0) (array-ref vars (- (get ntrue) 1)) #f)))))))

;; The inputs, where no compiler can fold them: globals.
(define n int 20)
(define ntests int 10)

(define* main (subr (maxeff heapy (read @globals)) () int)
  (lambda ()
    (let ((bdd (hwb n))
          (succeeded (the (ref bool @heap) (new #t))))
      (letrec ((loop (subr (maxeff heapy (read @globals)) (int) unit)
                 (lambda (i)
                   (if (<= i ntests)
                       (begin
                         (set succeeded (and (get succeeded) (test-hwb bdd (random-vars n))))
                         (loop (+ i 1)))
                       #u))))
        (begin
          (loop 1)
          (if (get succeeded) (get node-c) 0))))))
(main)
