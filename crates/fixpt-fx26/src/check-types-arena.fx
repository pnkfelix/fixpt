;;; The checker, in FX-26: its arena of type nodes, and what interns them:
;;; each node's hash and equality of parts, and a cycle's canonical form, so
;;; that one type is one node. Apart from `check-types.fx` since 2026-10-31
;;; (`TODO.md` §188), which makes it of the tables it is given and gives on
;;; all it defines.
;;; A file of one expression (`load-input`, `TODO.md` §68).


;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
;; Its types (`check-types-types.fx`), loaded before the module so that they are not
;; among its values; the module names what it uses of them.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (eager-reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (table-types (load-module "fx26:table-types.fx"))
       (check-modorder-types (load-module "fx26:check-modorder-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((tables (select table-types tables-sig)))
    (module
(import check-types-types r-const r-fresh r-var r-frozen r-heap r-global r-globals a-read a-write
        a-alloc a-goto a-comefrom a-await a-spin a-io a-init a-send a-receive a-nondet a-stage a-var
        a-app tm-param tm-length tm-lit pr-shape pr-acyclic pr-nat pr-length pr-rel cv-cellular
        cv-native cv-fx cv-var sz-finite sz-lin dr de dt dz dc df ty-base ty-void ty-var ty-subr
        ty-poly ty-ref ty-pair ty-tag ty-comp ty-markkey ty-product ty-sum ty-array ty-icell
        ty-place ty-bloblet ty-link ty-named ty-nlist ty-nat ty-module ty-select ty-param ty-lam
        ty-app ty-nil ty-union ty-allof ty-false
        ds-gen ds-size ds-var ds-rec ds-abbrev ds-region ds-eff
        ds-conv ds-fun x-var x-const x-lambda x-app x-plambda x-letregion x-rlambda x-proj x-if
        x-letrec x-let x-begin x-prompt x-the x-convention x-bloblet x-product x-extract x-sum
        x-tagcase x-module x-with k-ok k-err k-done st-car st-cdr st-field (type k-region k-atom
        k-eff k-vsub k-ids k-term k-prop k-props k-binders k-parts k-names k-strings k-conv k-terms
        k-size k-desc k-descs k-ty k-map k-ds kx kxs k-item k-items k-te k-result k-narrows
        k-pendings k-cert-len k-arrow-kind k-bounded k-nesting k-named k-settleds k-gen k-hyps
        k-lemma k-regions k-step k-steps k-path-fact k-path-facts) (effect kstate checks kreads
        kbuilds))
;; The types it uses of the files before it.
(define-type chars (select eager-reader-types chars))
(define-type table (select table-types table))
(define-type k-places (select check-modorder-types k-places))
;; What it uses of the modules it is given.
(import tables make-table symbol-hash table-ref table-set! table-has? table-count)

(define k-tys (ref (arrayof k-ty @t) @t) (new (make-array 512 (ty-void))))
(define k-ntys (ref int @t) (new 0))

;; Copy `from`, from its `i`th element on, into the bigger array `to`.
(define k-copy-array
  (poly ((t type)) (subr (maxeff kreads (write @t) spin) ((arrayof t @t) (arrayof t @t) int) unit))
  (plambda ((t type))
    (lambda ((from (arrayof t @t)) (to (arrayof t @t)) (i int))
      (if (= i (array-length from))
          #u
          (begin (array-set! to i (array-ref from i)) (k-copy-array from to (+ i 1)))))))

;;; ------------------------------------------------------------ interning
;; Each type node made, but a link and the nodes whose meaning is not
;; their parts, is looked up by its parts, each followed through its links,
;; first: one made with the same parts is given again (`k-ty-new`), so that
;; a type built twice, as each module a maker makes builds its types, is
;; one id, and comparing it with itself is `(= a b)`. Only a cache: entries
;; may go at any time, and do past a budget (the user's, 2026-10-28). The
;; printer names a type by its shape, not its id (`k-fits?`), and `->*`'s
;; mark is on a node of its own (`k-ty-fresh`).
(define k-mix (subr pure (int int) int)
  (lambda (h x) (modulo (+ (* h 31) x) 1073741789)))
;; A node's hash, from its kind and parts.
(define k-ty-hash (subr pure (k-ty) int)
  (lambda (t)
    (letrec ((ids (subr pure (int k-ids) int)
               (lambda (h xs) (if (null? xs) h (ids (k-mix h (car xs)) (cdr xs)))))
             (region (subr pure (int k-region) int)
               (lambda (h r)
                 (tagcase r
                   (r-const (n) (k-mix (k-mix h 1) (symbol-hash n)))
                   (r-fresh (i n) (k-mix (k-mix h 2) i))
                   (r-var (v) (k-mix (k-mix h 3) v))
                   (r-frozen (p f) (k-mix (k-mix (k-mix h 4) p) (if f 1 0)))
                   (r-heap () (k-mix h 5))
                   (r-global (g) (k-mix (k-mix h 6) (symbol-hash g)))
                   (r-globals () (k-mix h 7)))))
             (eff (subr pure (int k-eff) int)
               (lambda (h e) (if (null? e) h (eff (k-mix h 17) (cdr e)))))
             (parts (subr pure (int k-parts) int)
               (lambda (h ps)
                 (if (null? ps)
                     h
                     (parts (k-mix (k-mix h (symbol-hash (extract (car ps) 1)))
                                   (extract (car ps) 2))
                            (cdr ps))))))
      (tagcase t
        (ty-base (s) (k-mix 1 (symbol-hash s)))
        (ty-var (v) (k-mix 2 v))
        (ty-subr (e ps r cv spc) (eff (ids (k-mix 3 r) ps) e))
        (ty-poly (bs x) (k-mix 4 x))
        (ty-ref (x r) (region (k-mix 5 x) r))
        (ty-pair (x y r nl) (region (k-mix (k-mix 6 x) y) r))
        (ty-product (ps) (parts 10 ps))
        (ty-sum (ps) (parts 11 ps))
        (ty-array (x z r) (region (k-mix 12 x) r))
        (ty-named (g ds) (k-mix 17 g))
        (ty-app (g ds) (k-mix 28 g))
        (ty-nlist (x z r) (region (k-mix 18 x) r))
        (ty-union (ms) (ids 26 ms))
        (ty-allof (ms) (ids 29 ms))
        (ty-module (abs ds vs) (parts (parts (parts 27 abs) ds) vs))
        (else y 0)))))
;; Whether two nodes are made of the same parts, each id the same.
(define k-ty-same? (subr pure (k-ty k-ty) bool)
  (lambda (a b)
    (letrec ((ids (subr pure (k-ids k-ids) bool)
               (lambda (xs ys)
                 (cond ((null? xs) (null? ys))
                       ((null? ys) #f)
                       (else (and (= (car xs) (car ys)) (ids (cdr xs) (cdr ys)))))))
             (region (subr pure (k-region k-region) bool)
               (lambda (r s)
                 (tagcase r
                   (r-const (n) (tagcase s (r-const (m) (symbol=? n m)) (else y #f)))
                   (r-fresh (i n) (tagcase s (r-fresh (j m) (= i j)) (else y #f)))
                   (r-var (v) (tagcase s (r-var (w) (= v w)) (else y #f)))
                   (r-frozen (p f)
                     (tagcase s (r-frozen (q g) (and (= p q) (bool=? f g))) (else y #f)))
                   (r-heap () (tagcase s (r-heap () #t) (else y #f)))
                   (r-global (g) (tagcase s (r-global (h) (symbol=? g h)) (else y #f)))
                   (r-globals () (tagcase s (r-globals () #t) (else y #f))))))
             (size (subr pure (k-size k-size) bool)
               (lambda (m n)
                 (tagcase m
                   (sz-finite () (tagcase n (sz-finite () #t) (else y #f)))
                   (sz-lin (k ts)
                     (tagcase n (sz-lin (j us) (and (= k j) (terms ts us))) (else y #f))))))
             (terms (subr pure (k-terms k-terms) bool)
               (lambda (ts us)
                 (cond ((null? ts) (null? us))
                       ((null? us) #f)
                       (else (and (= (car (car ts)) (car (car us)))
                                  (= (cdr (car ts)) (cdr (car us)))
                                  (terms (cdr ts) (cdr us)))))))
             (conv (subr pure (k-conv k-conv) bool)
               (lambda (c d)
                 (tagcase c
                   (cv-cellular () (tagcase d (cv-cellular () #t) (else y #f)))
                   (cv-native () (tagcase d (cv-native () #t) (else y #f)))
                   (cv-fx () (tagcase d (cv-fx () #t) (else y #f)))
                   (cv-var (v) (tagcase d (cv-var (w) (= v w)) (else y #f))))))
             (descs (subr pure (k-descs k-descs) bool)
               (lambda (xs ys)
                 (cond ((null? xs) (null? ys))
                       ((null? ys) #f)
                       (else (and (desc (car xs) (car ys)) (descs (cdr xs) (cdr ys)))))))
             (desc (subr pure (k-desc k-desc) bool)
               (lambda (x y)
                 (tagcase x
                   (dr (r) (tagcase y (dr (s) (region r s)) (else z #f)))
                   (de (e) (tagcase y (de (f) (eff e f)) (else z #f)))
                   (dt (t) (tagcase y (dt (u) (= t u)) (else z #f)))
                   (dz (m) (tagcase y (dz (n) (size m n)) (else z #f)))
                   (dc (c) (tagcase y (dc (d) (conv c d)) (else z #f)))
                   (df (f) (tagcase y (df (g) (= f g)) (else z #f))))))
             ;; In order: a cache need not find two orders one.
             (eff (subr pure (k-eff k-eff) bool)
               (lambda (e f)
                 (cond ((null? e) (null? f))
                       ((null? f) #f)
                       (else (and (atom (car e) (car f)) (eff (cdr e) (cdr f)))))))
             (atom (subr pure (k-atom k-atom) bool)
               (lambda (x y)
                 (tagcase x
                   (a-read (r) (tagcase y (a-read (s) (region r s)) (else z #f)))
                   (a-write (r) (tagcase y (a-write (s) (region r s)) (else z #f)))
                   (a-alloc (r) (tagcase y (a-alloc (s) (region r s)) (else z #f)))
                   (a-goto (r) (tagcase y (a-goto (s) (region r s)) (else z #f)))
                   (a-comefrom (r) (tagcase y (a-comefrom (s) (region r s)) (else z #f)))
                   (a-await (r) (tagcase y (a-await (s) (region r s)) (else z #f)))
                   (a-init (r) (tagcase y (a-init (s) (region r s)) (else z #f)))
                   (a-send (r) (tagcase y (a-send (s) (region r s)) (else z #f)))
                   (a-receive (r) (tagcase y (a-receive (s) (region r s)) (else z #f)))
                   (a-spin () (tagcase y (a-spin () #t) (else z #f)))
                   (a-io (k) (tagcase y (a-io (j) (= k j)) (else z #f)))
                   (a-nondet () (tagcase y (a-nondet () #t) (else z #f)))
                   (a-stage () (tagcase y (a-stage () #t) (else z #f)))
                   (a-var (v) (tagcase y (a-var (w) (= v w)) (else z #f)))
                   (a-app (f ds)
                     (tagcase y (a-app (g es) (and (= f g) (descs ds es))) (else z #f))))))
             (parts (subr pure (k-parts k-parts) bool)
               (lambda (ps qs)
                 (cond ((null? ps) (null? qs))
                       ((null? qs) #f)
                       (else (and (symbol=? (extract (car ps) 1) (extract (car qs) 1))
                                  (= (extract (car ps) 2) (extract (car qs) 2))
                                  (parts (cdr ps) (cdr qs)))))))
             (binders (subr pure (k-binders k-binders) bool)
               (lambda (bs cs)
                 (cond ((null? bs) (null? cs))
                       ((null? cs) #f)
                       (else (and (= (extract (car bs) 1) (extract (car cs) 1))
                                  (= (extract (car bs) 2) (extract (car cs) 2))
                                  (binders (cdr bs) (cdr cs))))))))
      (tagcase a
        (ty-base (s) (tagcase b (ty-base (u) (symbol=? s u)) (else z #f)))
        (ty-var (v) (tagcase b (ty-var (w) (= v w)) (else z #f)))
        (ty-subr (e ps r cv spc)
          (tagcase b
            (ty-subr (f qs q dv tpc)
              (and (null? spc) (null? tpc) (= r q) (ids ps qs) (conv cv dv) (eff e f)))
            (else z #f)))
        (ty-poly (bs x) (tagcase b (ty-poly (cs y) (and (= x y) (binders bs cs))) (else z #f)))
        (ty-ref (x r) (tagcase b (ty-ref (y s) (and (= x y) (region r s))) (else z #f)))
        (ty-pair (x y r nl)
          (tagcase b
            (ty-pair (u v s nm) (and (= x u) (= y v) (bool=? nl nm) (region r s)))
            (else z #f)))
        (ty-product (ps) (tagcase b (ty-product (qs) (parts ps qs)) (else z #f)))
        (ty-sum (ps) (tagcase b (ty-sum (qs) (parts ps qs)) (else z #f)))
        (ty-array (x m r)
          (tagcase b (ty-array (y n s) (and (= x y) (size m n) (region r s))) (else z #f)))
        (ty-named (g ds) (tagcase b (ty-named (h es) (and (= g h) (descs ds es))) (else z #f)))
        (ty-app (g ds) (tagcase b (ty-app (h es) (and (= g h) (descs ds es))) (else z #f)))
        (ty-nlist (x m r)
          (tagcase b (ty-nlist (y n s) (and (= x y) (size m n) (region r s))) (else z #f)))
        (ty-union (ms) (tagcase b (ty-union (ns) (ids ms ns)) (else z #f)))
        (ty-allof (ms) (tagcase b (ty-allof (ns) (ids ms ns)) (else z #f)))
        (ty-module (abs ds vs)
          (tagcase b
            (ty-module (abs2 ds2 vs2) (and (parts abs abs2) (parts ds ds2) (parts vs vs2)))
            (else z #f)))
        (else z #f)))))
;; Whether node `t` is one interning keeps: those `k-ty-same?` compares.
(define k-internable? (subr pure (k-ty) bool)
  (lambda (t)
    (tagcase t
      (ty-base (s) #t) (ty-var (v) #t) (ty-subr (e ps r cv spc) (null? spc)) (ty-poly (bs x) #t)
      (ty-ref (x r) #t) (ty-pair (x y r nl) #t) (ty-product (ps) #t) (ty-sum (ps) #t)
      (ty-array (x m r) #t) (ty-named (g ds) #t) (ty-nlist (x m r) #t) (ty-union (ms) #t)
      (ty-allof (ms) #t)
      (ty-module (abs ds vs) #t)
      (else y #f))))
;; A cycle's canonical form (`k-cz-cyclic`): its nodes from one, in the order
;; first met, a part in the cycle written as `k-cyc-at` plus its number.
(define-type k-cyc-key (listof k-ty acyclic))
(define k-cyc-at int 1099511627776)
(define k-cyc-hash (subr pure (k-cyc-key) int)
  (lambda (ks) (if (null? ks) 7 (k-mix (k-ty-hash (car ks)) (k-cyc-hash (cdr ks))))))
(define k-cyc-same? (subr pure (k-cyc-key k-cyc-key) bool)
  (lambda (a b)
    (cond ((null? a) (null? b))
          ((null? b) #f)
          (else (and (k-ty-same? (car a) (car b)) (k-cyc-same? (cdr a) (cdr b))))))))))
