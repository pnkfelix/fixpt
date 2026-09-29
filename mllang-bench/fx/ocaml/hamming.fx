;;; HAMMING -- the Hamming numbers (2^i 3^j 5^k), as a lazy stream that
;;; merges three maps of itself, with numbers of 37 digits.
;;;
;;; From OCaml's classic test programs (testsuite/tests/misc/hamming.ml,
;;; ocaml commit 7da997d28b1a), ported to FX-26. The original prints the
;;; 88001st to 88100th Hamming numbers (indices 88000 to 88099, from 0),
;;; once. The port builds the stream afresh and walks it that far
;;; `iterations` = 10 times, and where the original prints a number it adds
;;; to a checksum: the sum, over those 100 numbers, of the number's place
;;; (1 to 100) times the sum of its three limbs, below. Answer:
;;; 38618242609892126, which is that checksum of the reference output's 100
;;; numbers.
;;;
;;; What the port changes:
;;; - Numbers: the original "rolls its own 37-digit numbers", pairs of
;;;   int64s, (low, high), base 10^18. FX-26's integers have 61 bits and
;;;   are checked for overflow, so 5 * 10^18 cannot be made; the port rolls
;;;   triples instead, (lo, mid, hi), base 10^12, products; `mul` and `cmp`
;;;   do what the original's do, a limb more.
;;; - Laziness: an `'a Lazy.t` is a memo cell, a ref holding either a thunk
;;;   (`delayed`) or its value (`forced`); `force` runs the thunk once and
;;;   keeps the value. (OCaml's check for a cell forced while it is being
;;;   forced is left out: nothing here does that.) The recursive values
;;;   `hamming`, `ham2`, `ham3` and `ham5` are tied through the cells: the
;;;   cell `hamming` is made first, holding a thunk never run, and set once
;;;   the other three exist.
;;; - `map` and `merge` are polymorphic in OCaml, and used at one type; here
;;;   they are at that type. `iter_interval`'s tuple (start, stop) is two
;;;   arguments.

(define-type num (productof (lo int) (mid int) (hi int)))

(define digit int 1000000000000)

(define* mul (subr pure (int num) num)
  (lambda (n p)
    (let* ((l (* n (extract p lo)))
           (m (+ (* n (extract p mid)) (quotient l digit))))
      (product (lo (modulo l digit))
               (mid (modulo m digit))
               (hi (+ (* n (extract p hi)) (quotient m digit)))))))

(define* cmp (subr pure (num num) int)
  (lambda (n p)
    (cond ((< (extract n hi) (extract p hi)) -1)
          ((> (extract n hi) (extract p hi)) 1)
          ((< (extract n mid) (extract p mid)) -1)
          ((> (extract n mid) (extract p mid)) 1)
          ((< (extract n lo) (extract p lo)) -1)
          ((> (extract n lo) (extract p lo)) 1)
          (else 0))))

(define* x2 (subr pure (num) num) (lambda (p) (mul 2 p)))
(define* x3 (subr pure (num) num) (lambda (p) (mul 3 p)))
(define* x5 (subr pure (num) num) (lambda (p) (mul 5 p)))

(define nn1 num (product (lo 1) (mid 0) (hi 0)))

;; This is where the interesting stuff begins.

(define-effect lazy-eff (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)))
;; (A datatype may not name a type defined after it, so `lcons` is
;; written out in `lstate`.)
(define-datatype lstate
  (delayed (subr lazy-eff () (productof (hd num) (tl (ref lstate @heap)))))
  (forced (productof (hd num) (tl (ref lstate @heap)))))
(define-type llist (ref lstate @heap))
(define-type lcons (productof (hd num) (tl llist)))

(define* lazy (subr (alloc @heap) ((subr lazy-eff () lcons)) llist)
  (lambda (thunk) (new (delayed thunk))))

(define* force (subr lazy-eff (llist) lcons)
  (lambda (l)
    (tagcase (get l)
      (forced (v) v)
      (delayed (thunk) (let ((v (thunk))) (begin (set l (forced v)) v))))))

(define* map (subr lazy-eff ((subr (read @globals) (num) num) llist) llist)
  (lambda (f l)
    (lazy (lambda ()
            (let ((c (force l)))
              (product (hd (f (extract c hd))) (tl (map f (extract c tl)))))))))

(define* merge (subr lazy-eff ((subr pure (num num) int) llist llist) llist)
  (lambda (cmp l1 l2)
    (lazy (lambda ()
            (let* ((c1 (force l1)) (c2 (force l2))
                   (x1 (extract c1 hd)) (ll1 (extract c1 tl))
                   (x2 (extract c2 hd)) (ll2 (extract c2 tl))
                   (c (cmp x1 x2)))
              (cond ((= c 0) (product (hd x1) (tl (merge cmp ll1 ll2))))
                    ((< c 0) (product (hd x1) (tl (merge cmp ll1 l2))))
                    (else (product (hd x2) (tl (merge cmp l1 ll2))))))))))

(define* iter-interval (subr lazy-eff ((subr (maxeff (read @heap) (write @heap)) (num) unit) llist int int) unit)
  (lambda (f l start stop)
    (if (= stop 0)
        #u
        (let ((c (force l)))
          (begin
            (if (<= start 0) (f (extract c hd)) #u)
            (iter-interval f (extract c tl) (- start 1) (- stop 1)))))))

;; let rec hamming = lazy (Cons (nn1, merge cmp ham2 (merge cmp ham3 ham5)))
;;     and ham2 = lazy (force (map x2 hamming))
;;     and ham3 = lazy (force (map x3 hamming))
;;     and ham5 = lazy (force (map x5 hamming))
(define* make-hamming (subr lazy-eff () llist)
  (lambda ()
    (letrec ((never (subr lazy-eff () lcons) (lambda () (never))))
      (let* ((hamming (lazy never))
             (ham2 (lazy (lambda () (force (map x2 hamming)))))
             (ham3 (lazy (lambda () (force (map x3 hamming)))))
             (ham5 (lazy (lambda () (force (map x5 hamming))))))
        (begin
          (set hamming (delayed (lambda ()
                                  (product (hd nn1)
                                           (tl (merge cmp ham2 (merge cmp ham3 ham5)))))))
          hamming)))))

;; The inputs, where no compiler can fold them: globals.
(define start int 88000)
(define stop int 88100)
(define iterations int 10)

;; `pr`, which printed a number, adds it to the checksum.
(define* main (subr lazy-eff () int)
  (lambda ()
    (let ((sum (the (ref int @heap) (new 0)))
          (place (the (ref int @heap) (new 0))))
      (begin
        (iter-interval
         (lambda ((p num))
           (begin
             (set place (+ (get place) 1))
             (set sum (+ (get sum) (* (get place) (+ (extract p lo) (+ (extract p mid) (extract p hi))))))))
         (make-hamming) start stop)
        (get sum)))))

(define* run (subr lazy-eff (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (main)))))
(run iterations 0)
