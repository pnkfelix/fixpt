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
(define a-alloc (with check-types-types a-alloc))
(define a-app (with check-types-types a-app))
(define a-await (with check-types-types a-await))
(define a-comefrom (with check-types-types a-comefrom))
(define a-goto (with check-types-types a-goto))
(define a-read (with check-types-types a-read))
(define a-spin (with check-types-types a-spin))
(define a-var (with check-types-types a-var))
(define a-write (with check-types-types a-write))
(define cv-cellular (with check-types-types cv-cellular))
(define cv-fx (with check-types-types cv-fx))
(define cv-native (with check-types-types cv-native))
(define cv-var (with check-types-types cv-var))
(define dc (with check-types-types dc))
(define de (with check-types-types de))
(define dr (with check-types-types dr))
(define dz (with check-types-types dz))
(define-type k-atom (select check-types-types k-atom))
(define-type k-conv (select check-types-types k-conv))
(define-type k-desc (select check-types-types k-desc))
(define-type k-descs (select check-types-types k-descs))
(define-type k-eff (select check-types-types k-eff))
(define-type k-region (select check-types-types k-region))
(define-type k-size (select check-types-types k-size))
(define-type k-terms (select check-types-types k-terms))
(define-effect kreads (select check-types-types kreads))
(define r-const (with check-types-types r-const))
(define r-fresh (with check-types-types r-fresh))
(define r-frozen (with check-types-types r-frozen))
(define r-global (with check-types-types r-global))
(define r-globals (with check-types-types r-globals))
(define r-heap (with check-types-types r-heap))
(define r-var (with check-types-types r-var))
(define sz-finite (with check-types-types sz-finite))
(define sz-lin (with check-types-types sz-lin))
;; What it uses of the modules it is given.
(define k-int-cmp (with check-types k-int-cmp))

;; Booleans in order, false first.
(define k-bool-cmp (subr (read @globals) (bool bool) int)
  (lambda (f g) (k-int-cmp (if f 1 0) (if g 1 0))))
(define k-region-rank (subr pure (k-region) int)
  (lambda (r)
    (tagcase r
      (r-const (n) 0) (r-fresh (i n) 1) (r-var (v) 2) (r-frozen (p f) 3) (r-heap () 4)
      (r-global (g) 5) (r-globals () 6))))
;; Two names in order: the same symbol at once, else by their text.
(define k-name-cmp (subr pure (symbol symbol) int)
  (lambda (n m) (if (symbol=? n m) 0 (symbol-compare n m))))
(define k-region-cmp (subr (maxeff (read @globals) spin) (k-region k-region) int)
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
(define k-region=? (subr (maxeff (read @globals) spin) (k-region k-region) bool)
  (lambda (r s)
    (tagcase r
      (r-const (n) (tagcase s (r-const (m) (symbol=? n m)) (else y #f)))
      (r-fresh (i n) (tagcase s (r-fresh (j m) (= i j)) (else y #f)))
      (r-var (v) (tagcase s (r-var (w) (= v w)) (else y #f)))
      (r-frozen (p f) (tagcase s (r-frozen (q g) (and (= p q) (bool=? f g))) (else y #f)))
      (r-heap () (tagcase s (r-heap () #t) (else y #f)))
      (r-global (g) (tagcase s (r-global (h) (symbol=? g h)) (else y #f)))
      (r-globals () (tagcase s (r-globals () #t) (else y #f))))))

(define k-atom-rank (subr pure (k-atom) int)
  (lambda (a)
    (tagcase a
      (a-read (r) 0) (a-write (r) 1) (a-alloc (r) 2)
      (a-goto (r) 3) (a-comefrom (r) 4) (a-await (r) 5)
      (a-spin () 6) (a-var (v) 7) (a-app (v ds) 8))))
;; The atom's region; a variable's is none, shown as a binder -1.
(define k-atom-region (subr (read @globals) (k-atom) k-region)
  (lambda (a)
    (tagcase a
      (a-read (r) r) (a-write (r) r) (a-alloc (r) r)
      (a-goto (r) r) (a-comefrom (r) r) (a-await (r) r)
      (a-spin () (r-var -1)) (a-var (v) (r-var -1)) (a-app (v ds) (r-var -1)))))
(define k-has-region? (subr (read @globals) (k-atom) bool) (lambda (a) (< (k-atom-rank a) 6)))
;; The effect variable an atom is, or -1.
(define k-atom-var (subr pure (k-atom) int)
  (lambda (a) (tagcase a (a-var (v) v) (else y -1))))
;; What orders two atoms of one rank with no region: a variable's number,
;; or an effect application's.
(define k-atom-key (subr pure (k-atom) int)
  (lambda (a) (tagcase a (a-var (v) v) (a-app (v ds) v) (else y -1))))
;; A convention as a number: one of FX-26's own, or its binder.
(define k-conv-code (subr pure (k-conv) int)
  (lambda (c) (tagcase c (cv-cellular () -1) (cv-native () -2) (cv-fx () -3) (cv-var (v) v))))
;; What an effect application was given; none for any other atom.
(define k-atom-args (subr pure (k-atom) (listof k-desc acyclic))
  (lambda (a) (tagcase a (a-app (v ds) ds) (else y nil))))
;; Descriptions given an effect function, ranked by kind.
(define k-earg-rank (subr pure (k-desc) int)
  (lambda (d) (tagcase d (dr (r) 0) (de (e) 1) (dz (z) 2) (dc (c) 3) (else y 4))))
(define k-terms-cmp (subr (maxeff (read @globals) spin) (k-terms k-terms) int)
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
(define k-size-cmp (subr (maxeff (read @globals) spin) (k-size k-size) int)
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
(define k-region-ord (subr pure (k-region) int)
  (lambda (r)
    (tagcase r
      (r-const (n) 0)
      (r-fresh (i n) (+ 4503599627370496 i))
      (r-var (v) (+ 9007199254740992 (+ v 1099511627776)))
      (r-frozen (p f) (+ 13510798882111488 (+ (* 2 (+ p 1099511627776)) (if f 1 0))))
      (r-heap () 18014398509481984)
      (r-global (g) 22517998136852480)
      (r-globals () 27021597764222976))))
(define k-atom-ord (subr pure (k-atom) int)
  (lambda (a)
    (tagcase a
      (a-read (r) (k-region-ord r))
      (a-write (r) (+ 72057594037927936 (k-region-ord r)))
      (a-alloc (r) (+ 144115188075855872 (k-region-ord r)))
      (a-goto (r) (+ 216172782113783808 (k-region-ord r)))
      (a-comefrom (r) (+ 288230376151711744 (k-region-ord r)))
      (a-await (r) (+ 360287970189639680 (k-region-ord r)))
      (a-spin () 432345564227567616)
      (a-var (v) (+ 504403158265495552 (+ v 1099511627776)))
      (a-app (v ds) (+ 576460752303423488 (+ v 1099511627776))))))
;; Two names by their stored hashes; by their text only if those are equal.
(define k-name-hash-cmp (subr pure (symbol symbol) int)
  (lambda (n m)
    (if (symbol=? n m)
        0
        (let ((h (symbol-name-hash n)) (g (symbol-name-hash m)))
          (cond ((< h g) -1) ((< g h) 1) (else (symbol-compare n m)))))))
;; Two regions whose `k-region-ord` is the same: names by `k-name-hash-cmp`.
(define k-region-tie (subr pure (k-region k-region) int)
  (lambda (r s)
    (tagcase r
      (r-const (n) (tagcase s (r-const (m) (k-name-hash-cmp n m)) (else y 0)))
      (r-global (g) (tagcase s (r-global (h) (k-name-hash-cmp g h)) (else y 0)))
      (else y 0))))
;; Atoms in order: by `k-atom-ord`, one comparison of integers; a tie, by the
;; names of their regions, or an effect application's by what it was given.
(define-rec
  (k-atom-cmp (subr (maxeff (read @globals) spin) (k-atom k-atom) int)
    (lambda (a b)
      (let ((x (k-atom-ord a)) (y (k-atom-ord b)))
        (cond ((< x y) -1)
              ((< y x) 1)
              (else
               (tagcase a
                 (a-app (v ds) (k-eargs-cmp ds (k-atom-args b)))
                 (else z (k-region-tie (k-atom-region a) (k-atom-region b)))))))))
  (k-eargs-cmp (subr (maxeff (read @globals) spin) (k-descs k-descs) int)
    (lambda (xs ys)
      (cond ((null? xs) (if (null? ys) 0 -1))
            ((null? ys) 1)
            (else
             (let ((c (k-earg-cmp (car xs) (car ys))))
               (if (= c 0) (k-eargs-cmp (cdr xs) (cdr ys)) c))))))
  (k-earg-cmp (subr (maxeff (read @globals) spin) (k-desc k-desc) int)
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
  (k-effs-cmp (subr (maxeff (read @globals) spin) (k-eff k-eff) int)
    (lambda (e f)
      (cond ((null? e) (if (null? f) 0 -1))
            ((null? f) 1)
            (else
             (let ((c (k-atom-cmp (car e) (car f))))
               (if (= c 0) (k-effs-cmp (cdr e) (cdr f)) c)))))))
(define k-atom-with (subr (read @globals) (k-atom k-region) k-atom)
  (lambda (a r)
    (tagcase a
      (a-read (x) (a-read r)) (a-write (x) (a-write r)) (a-alloc (x) (a-alloc r))
      (a-goto (x) (a-goto r)) (a-comefrom (x) (a-comefrom r)) (a-await (x) (a-await r))
      (a-spin () a) (a-var (v) a) (a-app (v ds) a))))
;; Whether `a` comes before `b`, and whether they are one atom.
(define k-atom<? (subr (maxeff (read @globals) spin) (k-atom k-atom) bool)
  (lambda (a b) (< (k-atom-cmp a b) 0)))
(define k-atom=? (subr (maxeff (read @globals) spin) (k-atom k-atom) bool)
  (lambda (a b) (= (k-atom-cmp a b) 0)))

(define k-insert (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-atom k-eff) k-eff)
  (lambda (a e)
    (if (null? e)
        (cons a nil)
        (let ((c (k-atom-cmp a (car e))))
          (cond ((< c 0) (cons a e)) ((= c 0) e) (else (cons (car e) (k-insert a (cdr e)))))))))
(define k-union-each (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-eff k-eff) k-eff)
  (lambda (x y) (if (null? x) y (k-union-each (cdr x) (k-insert (car x) y)))))
(define k-sorted? (subr (maxeff kreads spin) (k-eff) bool)
  (lambda (e)
    (or (null? e) (null? (cdr e)) (and (k-atom<? (car e) (car (cdr e))) (k-sorted? (cdr e))))))
(define k-merge (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-eff k-eff) k-eff)
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
(define k-union (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-eff k-eff) k-eff)
  (lambda (x y) (if (k-sorted? x) (k-merge x y) (k-union-each x y))))
(define k-contains? (subr (maxeff kreads spin) (k-eff k-atom) bool)
  (lambda (e a) (cond ((null? e) #f) ((k-atom=? (car e) a) #t) (else (k-contains? (cdr e) a)))))
;; Whether `a` is in `e`, or, reading or writing one global, `e` does so to
;; `@globals`.
(define k-covered? (subr (maxeff (read @globals) (read @t) spin) (k-eff k-atom) bool)
  (lambda (e a)
    (or (k-contains? e a)
        (tagcase a
          (a-read (r) (tagcase r (r-global (g) (k-contains? e (a-read (r-globals)))) (else y #f)))
          (a-write (r) (tagcase r (r-global (g) (k-contains? e (a-write (r-globals)))) (else y #f)))
          (else y #f)))))
(define k-within-each? (subr (maxeff (read @globals) (read @t) spin) (k-eff k-eff) bool)
  (lambda (x y) (or (null? x) (and (k-covered? y (car x)) (k-within-each? (cdr x) y)))))
;; `k-within?` of sorted effects, `rg` and `wg` whether `y` reads and writes
;; `@globals`, which cover reading and writing any one global.
(define k-within-sorted? (subr (maxeff (read @globals) (read @t) spin) (k-eff k-eff bool bool) bool)
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
(define k-within? (subr (maxeff (read @globals) (read @t) spin) (k-eff k-eff) bool)
  (lambda (x y)
    (if (and (k-sorted? x) (k-sorted? y))
        (let ((rg (k-contains? y (a-read (r-globals)))) (wg (k-contains? y (a-write (r-globals)))))
          (k-within-sorted? x y rg wg))
        (k-within-each? x y))))
(define k-eff=? (subr (maxeff kreads spin) (k-eff k-eff) bool)
  (lambda (x y) (and (k-within? x y) (k-within? y x))))
(define k-one (subr (alloc @t) (k-atom) k-eff) (lambda (a) (cons a nil)))
(define k-allocates? (subr (maxeff (read @globals) (read @t)) (k-eff) bool)
  (lambda (e) (cond ((null? e) #f) ((= (k-atom-rank (car e)) 2) #t) (else (k-allocates? (cdr e))))))
;; The module, the lambda given its modules, and the loads, closed.
)))
