;;; The checker, in FX-26: effects, sets of atoms kept sorted, so
;;; `(maxeff e (maxeff e pure))` and `e` are one effect; the order is this
;;; file's own, and printing follows it. After `check-types.fx`; part of
;;; the checker, `check-types.fx` first.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-types-types (load-module "fx26:check-types-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig)))
    (module

;; The types it uses of the files before it.
(hide (include check-types-types))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types))

;; Booleans in order, false first.
(define k-bool-cmp (->* (bool bool) int)
  (lambda (f g) (k-int-cmp (if f 1 0) (if g 1 0))))
(define k-region-rank (->* (k-region) int)
  (lambda (r)
    (tagcase r
      (r-const (n) 0) (r-fresh (i n) 1) (r-var (v) 2) (r-frozen (p f) 3) (r-heap () 4)
      (r-global (g) 5) (r-globals () 6))))
;; Two names in order: the same symbol at once, else by their text.
(define k-name-cmp (->* (symbol symbol) int)
  (lambda (n m) (if (symbol=? n m) 0 (symbol-compare n m))))
(define k-region-cmp (->* (k-region k-region) int)
  (lambda (r s)
    (let ((c (k-int-cmp (k-region-rank r) (k-region-rank s))))
      (if (= c 0)
          (tagcase r
            (r-const (n) (tagcase s (r-const (m) (k-name-cmp n m)) (else y 0)))
            (r-fresh (i n) (tagcase s (r-fresh (j m) (k-int-cmp i j)) (else y 0)))
            (r-var (v) (tagcase s (r-var (w) (k-int-cmp v w)) (else y 0)))
            (r-frozen (p f)
              (tagcase s
                (r-frozen (q g) (let ((c (k-int-cmp p q))) (if (= c 0) (k-bool-cmp f g) c)))
                (else y 0)))
            (r-heap () 0)
            (r-global (g) (tagcase s (r-global (h) (k-name-cmp g h)) (else y 0)))
            (r-globals () 0))
          c))))
;; The same as `(= (k-region-cmp r s) 0)`, the names compared as symbols:
;; one comparison, where the order compares their names.
(define k-region=? (->* (k-region k-region) bool)
  (lambda (r s)
    (tagcase r
      (r-const (n) (tagcase s (r-const (m) (symbol=? n m)) (else y #f)))
      (r-fresh (i n) (tagcase s (r-fresh (j m) (= i j)) (else y #f)))
      (r-var (v) (tagcase s (r-var (w) (= v w)) (else y #f)))
      (r-frozen (p f) (tagcase s (r-frozen (q g) (and (= p q) (bool=? f g))) (else y #f)))
      (r-heap () (tagcase s (r-heap () #t) (else y #f)))
      (r-global (g) (tagcase s (r-global (h) (symbol=? g h)) (else y #f)))
      (r-globals () (tagcase s (r-globals () #t) (else y #f))))))

(define k-atom-rank (->* (k-atom) int)
  (lambda (a)
    (tagcase a
      (a-read (r) 0) (a-write (r) 1) (a-alloc (r) 2)
      (a-goto (r) 3) (a-comefrom (r) 4) (a-await (r) 5)
      (a-init (r) 6) (a-send (r) 7) (a-receive (r) 8)
      (a-spin () 9) (a-io (k) 9) (a-nondet () 9) (a-var (v) 10) (a-app (v ds) 11))))
;; The atom's region; a variable's is none, shown as a binder -1.
(define k-atom-region (->* (k-atom) k-region)
  (lambda (a)
    (tagcase a
      (a-read (r) r) (a-write (r) r) (a-alloc (r) r)
      (a-goto (r) r) (a-comefrom (r) r) (a-await (r) r)
      (a-init (r) r) (a-send (r) r) (a-receive (r) r)
      (a-spin () (r-var -1)) (a-io (k) (r-var -1)) (a-nondet () (r-var -1)) (a-var (v) (r-var -1))
      (a-app (v ds) (r-var -1)))))
(define k-has-region? (->* (k-atom) bool) (lambda (a) (< (k-atom-rank a) 9)))
;; The effect variable an atom is, or -1.
(define k-atom-var (->* (k-atom) int)
  (lambda (a) (tagcase a (a-var (v) v) (else y -1))))
;; What orders two atoms of one rank with no region: a variable's number,
;; or an effect application's.
(define k-atom-key (->* (k-atom) int)
  (lambda (a) (tagcase a (a-var (v) v) (a-app (v ds) v) (else y -1))))
;; A convention as a number: one of FX-26's own, or its binder.
(define k-conv-code (->* (k-conv) int)
  (lambda (c) (tagcase c (cv-cellular () -1) (cv-native () -2) (cv-fx () -3) (cv-var (v) v))))
;; What an effect application was given; none for any other atom.
(define k-atom-args (->* (k-atom) (listof k-desc acyclic))
  (lambda (a) (tagcase a (a-app (v ds) ds) (else y nil))))
;; Descriptions given an effect function, ranked by kind.
(define k-earg-rank (->* (k-desc) int)
  (lambda (d) (tagcase d (dr (r) 0) (de (e) 1) (dz (z) 2) (dc (c) 3) (else y 4))))
(define k-terms-cmp (->* (k-terms k-terms) int)
  (lambda (ts us)
    (cond ((null? ts) (if (null? us) 0 -1))
          ((null? us) 1)
          (else
           (let ((c (k-int-cmp (car (car ts)) (car (car us)))))
             (cond ((not (= c 0)) c)
                   ((not (= (cdr (car ts)) (cdr (car us))))
                    (k-int-cmp (cdr (car ts)) (cdr (car us))))
                   (else (k-terms-cmp (cdr ts) (cdr us)))))))))
;; Sizes in order: `finite` first, then by constant and terms.
(define k-size-cmp (->* (k-size k-size) int)
  (lambda (m n)
    (tagcase m
      (sz-finite () (tagcase n (sz-finite () 0) (else y -1)))
      (sz-lin (k ts)
        (tagcase n
          (sz-finite () 1)
          (sz-lin (j us)
            (let ((c (k-int-cmp k j)))
              (if (= c 0) (k-terms-cmp ts us) c))))))))
;; Where an atom is in the order effects are kept in, in one integer: its
;; kind, its region's kind, and a number (a variable's, a fresh region's, a
;; frozen place's), from the high bits down (`TODO.md`, effects by key).
;; Names (constant regions, globals) tie here, and are ordered by their
;; hashes (`k-name-hash-cmp`): the order is not alphabetical, which only
;; showing an effect needs (`k-globals-shown`).
(define k-region-ord (->* (k-region) int)
  (lambda (r)
    (tagcase r
      (r-const (n) 0)
      (r-fresh (i n) (+ 4503599627370496 i))
      (r-var (v) (+ 9007199254740992 (+ v 1099511627776)))
      (r-frozen (p f) (+ 13510798882111488 (+ (* 2 (+ p 1099511627776)) (if f 1 0))))
      (r-heap () 18014398509481984)
      (r-global (g) 22517998136852480)
      (r-globals () 27021597764222976))))
(define k-atom-ord (->* (k-atom) int)
  (lambda (a)
    (tagcase a
      (a-read (r) (k-region-ord r))
      (a-write (r) (+ 72057594037927936 (k-region-ord r)))
      (a-alloc (r) (+ 144115188075855872 (k-region-ord r)))
      (a-goto (r) (+ 216172782113783808 (k-region-ord r)))
      (a-comefrom (r) (+ 288230376151711744 (k-region-ord r)))
      (a-await (r) (+ 360287970189639680 (k-region-ord r)))
      (a-init (r) (+ 432345564227567616 (k-region-ord r)))
      (a-send (r) (+ 504403158265495552 (k-region-ord r)))
      (a-receive (r) (+ 576460752303423488 (k-region-ord r)))
      (a-spin () 648518346341351424)
      ;; After `spin`, by kind, then `nondet`, as the Rust checker's `Atom`
      ;; orders them.
      (a-io (k) (+ 648518346341351425 k))
      (a-nondet () 648518346341351440)
      (a-var (v) (+ 720575940379279360 (+ v 1099511627776)))
      (a-app (v ds) (+ 792633534417207296 (+ v 1099511627776))))))
;; Two names by their stored hashes; by their text only if those are equal.
(define k-name-hash-cmp (->* (symbol symbol) int)
  (lambda (n m)
    (if (symbol=? n m)
        0
        (let ((h (symbol-name-hash n)) (g (symbol-name-hash m)))
          (cond ((< h g) -1) ((< g h) 1) (else (symbol-compare n m)))))))
;; Two regions whose `k-region-ord` is the same: names by `k-name-hash-cmp`.
(define k-region-tie (->* (k-region k-region) int)
  (lambda (r s)
    (tagcase r
      (r-const (n) (tagcase s (r-const (m) (k-name-hash-cmp n m)) (else y 0)))
      (r-global (g) (tagcase s (r-global (h) (k-name-hash-cmp g h)) (else y 0)))
      (else y 0))))
;; Atoms in order: by `k-atom-ord`, one comparison of integers; a tie, by the
;; names of their regions, or an effect application's by what it was given.
(define-rec
  (k-atom-cmp (->* (k-atom k-atom) int)
    (lambda (a b)
      (let ((x (k-atom-ord a)) (y (k-atom-ord b)))
        (cond ((< x y) -1)
              ((< y x) 1)
              (else
               (tagcase a
                 (a-app (v ds) (k-eargs-cmp ds (k-atom-args b)))
                 (else z (k-region-tie (k-atom-region a) (k-atom-region b)))))))))
  (k-eargs-cmp (->* (k-descs k-descs) int)
    (lambda (xs ys)
      (cond ((null? xs) (if (null? ys) 0 -1))
            ((null? ys) 1)
            (else
             (let ((c (k-earg-cmp (car xs) (car ys))))
               (if (= c 0) (k-eargs-cmp (cdr xs) (cdr ys)) c))))))
  (k-earg-cmp (->* (k-desc k-desc) int)
    (lambda (x y)
      (let ((c (k-int-cmp (k-earg-rank x) (k-earg-rank y))))
        (if (not (= c 0))
            c
            (tagcase x
              (dr (r) (tagcase y (dr (s) (k-region-cmp r s)) (else z 0)))
              (de (e) (tagcase y (de (f) (k-effs-cmp e f)) (else z 0)))
              (dz (m) (tagcase y (dz (n) (k-size-cmp m n)) (else z 0)))
              (dc (a) (tagcase y (dc (b) (k-int-cmp (k-conv-code a) (k-conv-code b))) (else z 0)))
              (else z 0))))))
  (k-effs-cmp (->* (k-eff k-eff) int)
    (lambda (e f)
      (cond ((null? e) (if (null? f) 0 -1))
            ((null? f) 1)
            (else
             (let ((c (k-atom-cmp (car e) (car f))))
               (if (= c 0) (k-effs-cmp (cdr e) (cdr f)) c)))))))
(define k-atom-with (->* (k-atom k-region) k-atom)
  (lambda (a r)
    (tagcase a
      (a-read (x) (a-read r)) (a-write (x) (a-write r)) (a-alloc (x) (a-alloc r))
      (a-goto (x) (a-goto r)) (a-comefrom (x) (a-comefrom r)) (a-await (x) (a-await r))
      (a-init (x) (a-init r)) (a-send (x) (a-send r)) (a-receive (x) (a-receive r))
      (a-spin () a) (a-io (k) a) (a-nondet () a) (a-var (v) a) (a-app (v ds) a))))
;; Whether `a` comes before `b`, and whether they are one atom.
(define k-atom<? (->* (k-atom k-atom) bool)
  (lambda (a b) (< (k-atom-cmp a b) 0)))
(define k-atom=? (->* (k-atom k-atom) bool)
  (lambda (a b) (= (k-atom-cmp a b) 0)))

(define k-insert (->* (k-atom k-eff) k-eff)
  (lambda (a e)
    (if (null? e)
        (cons a nil)
        (let ((c (k-atom-cmp a (car e))))
          (cond ((< c 0) (cons a e)) ((= c 0) e) (else (cons (car e) (k-insert a (cdr e)))))))))
(define k-union-each (->* (k-eff k-eff) k-eff)
  (lambda (x y) (if (null? x) y (k-union-each (cdr x) (k-insert (car x) y)))))
(define k-sorted? (->* (k-eff) bool)
  (lambda (e)
    (or (null? e) (null? (cdr e)) (and (k-atom<? (car e) (car (cdr e))) (k-sorted? (cdr e))))))
(define k-merge (->* (k-eff k-eff) k-eff)
  (lambda (x y)
    (cond ((null? x) y)
          ((null? y) x)
          (else
           (let ((c (k-atom-cmp (car x) (car y))))
             (cond ((< c 0) (cons (car x) (k-merge (cdr x) y)))
                   ((= c 0) (cons (car x) (k-merge (cdr x) (cdr y))))
                   (else (cons (car y) (k-merge x (cdr y))))))))))
;; `x` and `y` together, sorted as `k-insert` keeps an effect: a merge, when
;; `x` is sorted too (as effects made here are), else one atom at a time.
(define k-union (->* (k-eff k-eff) k-eff)
  (lambda (x y) (if (k-sorted? x) (k-merge x y) (k-union-each x y))))
(define k-contains? (->* (k-eff k-atom) bool)
  (lambda (e a) (cond ((null? e) #f) ((k-atom=? (car e) a) #t) (else (k-contains? (cdr e) a)))))
;; Whether `a` is in `e`, or, reading or writing one global, `e` does so to
;; `@globals`.
(define k-covered? (->* (k-eff k-atom) bool)
  (lambda (e a)
    (or (k-contains? e a)
        (tagcase a
          (a-read (r) (tagcase r (r-global (g) (k-contains? e (a-read (r-globals)))) (else y #f)))
          (a-write (r) (tagcase r (r-global (g) (k-contains? e (a-write (r-globals)))) (else y #f)))
          ;; An I-cell's fill is within writing its region.
          (a-init (r) (k-contains? e (a-write r)))
          ;; Data frozen into a place as it is made, the place's allocation.
          (a-alloc (r)
            (tagcase r
              (r-frozen (p f) (and (>= p 0) (k-contains? e (a-alloc (r-var p)))))
              (else y #f)))
          (else y #f)))))
;; Whether `e` makes data frozen into a place: what only `k-covered?` sees
;; within the place's allocation.
(define k-frozen-alloc? (->* (k-eff) bool)
  (lambda (e)
    (and (not (null? e))
         (or (tagcase (car e)
               (a-alloc (r) (tagcase r (r-frozen (p f) (>= p 0)) (else y #f)))
               (else y #f))
             (k-frozen-alloc? (cdr e))))))
(define k-within-each? (->* (k-eff k-eff) bool)
  (lambda (x y) (or (null? x) (and (k-covered? y (car x)) (k-within-each? (cdr x) y)))))
;; `k-within?` of sorted effects, `rg` and `wg` whether `y` reads and writes
;; `@globals`, which cover reading and writing any one global.
(define k-within-sorted? (->* (k-eff k-eff bool bool) bool)
  (lambda (x y rg wg)
    (cond ((null? x) #t)
          ((tagcase (car x)
             (a-read (r) (and rg (tagcase r (r-global (g) #t) (else z #f))))
             (a-write (r) (and wg (tagcase r (r-global (g) #t) (else z #f))))
             (else z #f))
           (k-within-sorted? (cdr x) y rg wg))
          ((null? y) #f)
          (else
           (let ((c (k-atom-cmp (car x) (car y))))
             (cond ((< c 0) #f)
                   ((= c 0) (k-within-sorted? (cdr x) (cdr y) rg wg))
                   (else (k-within-sorted? x (cdr y) rg wg))))))))
;; Whether every atom of `x` is covered by `y` (`k-covered?`): both sorted,
;; as effects made here are, by one walk of the two; else atom by atom.
(define k-within? (->* (k-eff k-eff) bool)
  (lambda (x y)
    (if (and (k-sorted? x) (k-sorted? y) (not (k-has-init? x)) (not (k-frozen-alloc? x)))
        (let ((rg (k-contains? y (a-read (r-globals)))) (wg (k-contains? y (a-write (r-globals)))))
          (k-within-sorted? x y rg wg))
        (k-within-each? x y))))
;; Whether `e` fills an I-cell: what only `k-covered?` sees within a write.
(define k-has-init? (->* (k-eff) bool)
  (lambda (e)
    (and (not (null? e)) (or (tagcase (car e) (a-init (r) #t) (else y #f)) (k-has-init? (cdr e))))))
(define k-eff=? (->* (k-eff k-eff) bool)
  (lambda (x y) (and (k-within? x y) (k-within? y x))))
(define k-one (->* (k-atom) k-eff) (lambda (a) (cons a nil)))
(define k-allocates? (->* (k-eff) bool)
  (lambda (e) (cond ((null? e) #f) ((= (k-atom-rank (car e)) 2) #t) (else (k-allocates? (cdr e))))))
;; The module, the lambda given its modules, and the loads, closed.
)))
