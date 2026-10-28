;;; The checker, in FX-26 (PLAN.md §11, step 10).
;;;
;;; The Rust checker's rules (`check.rs`, `infer.rs`) and its reading of
;;; descriptions (`parse.rs`, `top.rs`), over the parser's trees, rule for
;;; rule and message for message, so the two can be compared: for each
;;; top-level form, what it defines or what type and effect it has; or the
;;; first error, and where it is.
;;;
;;; Types live in an arena, as in Rust: a type is an index, and a recursive
;;; type is a cycle of indexes through forwarding links. Effects are sets of
;;; atoms kept sorted, so `(maxeff e (maxeff e pure))` and `e` are one list;
;;; the order is this file's own, and printing follows it.
;;;
;;; The parser keeps descriptions as the syntax they were written in. A
;;; first pass, `k-resolve`, reads them into the arena, in the order the Rust
;;; parser does (a `lambda`'s parameter types before its body, a `letrec`'s
;;; type before its initialiser), so the first error is the same one.
;;;
;;; Compiled with the reader and the parser, as one program. Its store is
;;; @t and its failures abort to a prompt in @z.

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
        a-alloc a-goto a-comefrom a-await a-spin a-io a-init a-send a-receive a-nondet a-var a-app
        tm-param tm-length tm-lit pr-shape pr-acyclic pr-nat pr-length pr-rel cv-cellular cv-native
        cv-fx cv-var sz-finite sz-lin dr de dt dz dc df ty-base ty-void ty-var ty-subr ty-poly
        ty-ref ty-pair ty-tag ty-comp ty-markkey ty-product ty-sum ty-array ty-icell ty-place
        ty-bloblet ty-link ty-named ty-nlist ty-nat ty-module ty-select ty-param ty-lam ty-app
        ty-nil ty-union ty-false ds-gen ds-size ds-var ds-rec ds-abbrev ds-region ds-eff
        ds-conv ds-fun x-var x-const x-lambda x-app x-plambda x-letregion x-rlambda x-proj x-if
        x-letrec x-let x-begin x-prompt x-the x-convention x-bloblet x-product x-extract x-sum
        x-tagcase x-module x-with k-ok k-err k-done st-car st-cdr st-field
        (type k-region k-atom k-eff k-vsub k-ids k-term k-prop k-props k-binders k-parts k-names
              k-strings k-conv k-terms k-size k-desc k-descs k-ty k-map k-ds kx kxs k-item k-items
              k-te k-result k-narrows k-pendings k-cert-len k-arrow-kind k-bounded k-nesting k-named
              k-settleds
              k-gen k-hyps k-lemma k-regions k-step k-steps k-path-fact k-path-facts)
        (effect kstate checks kreads kbuilds))
;; The types it uses of the files before it.
(define-type chars (select eager-reader-types chars))
(define-type table (select table-types table))
(define-type k-places (select check-modorder-types k-places))
;; What it uses of the modules it is given.
(import tables make-table symbol-hash table-ref table-set! table-has? table-count)

(define k-te (subr pure (int k-eff) k-te) (lambda (t e) (product (1 t) (2 e))))

(define k-tag (prompt-tag k-result k-result (maxeff spin (read @s) kstate) @z)
  (make-continuation-prompt-tag))
(define k-fail (subr checks (string int int) void)
  (lambda (m a b) (abort-current-continuation k-tag (k-err m a b))))

;;; ---------------------------------------------------------------- strings

(define k-cat3 (subr pure (string string string) string)
  (lambda (a b c) (string-append a b c)))
(define k-cat4 (subr (read @globals) (string string string string) string)
  (lambda (a b c d) (string-append a (k-cat3 b c d))))
(define k-cat5 (subr (read @globals) (string string string string string) string)
  (lambda (a b c d e) (string-append a (k-cat4 b c d e))))
(define k-quote (subr (read @globals) (string) string) (lambda (n) (k-cat3 "`" n "`")))

;; `xs` joined, `sep` between each two: their characters gathered, last to
;; first, into one list in an arena of its own, made a string once; so a long
;; list costs its length, not its length squared, as appending each to the
;; rest did (a module type's components, printed: `docs/performance.md`).
(define k-join (subr (maxeff (read @globals) (read @t)) ((listof string acyclic) string) string)
  (lambda (xs sep)
    (letrena r
      (letrec ((chars (subr (alloc r) (string int (listof char r)) (listof char r))
                 (lambda (s i acc)
                   (if (< i 0) acc (chars s (- i 1) (rcons r (string-ref s i) acc)))))
               (onto (subr (maxeff (alloc r) (read @t)) (string (listof char r)) (listof char r))
                 (lambda (s acc) (chars s (- (string-length s) 1) acc)))
               (all (subr (maxeff (alloc r) (read @t)) (k-strings (listof char r)) (listof char r))
                 (lambda (xs acc)
                   (cond ((null? xs) acc)
                         ((null? (cdr xs)) (onto (car xs) acc))
                         (else (onto (car xs) (onto sep (all (cdr xs) acc))))))))
        (list->string (all xs nil))))))

;; Where `sub` first starts in `s` from `at`, or -1.
(define k-find-sub (subr (maxeff (read @globals) spin) (string string int) int)
  (lambda (s sub at) (string-search s sub at)))

(define k-str-cmp (subr (maxeff (read @globals) spin) (string string int) int)
  (lambda (a b i) (string-compare a b)))
(define k-int-cmp (subr pure (int int) int)
  (lambda (x y) (cond ((< x y) -1) ((> x y) 1) (else 0))))

;;; ------------------------------------------------------------ lists

;; Over finite lists, which every list here is: so they end.
(define k-length
  (poly ((t type)) (subr (read @globals) ((listof t acyclic)) int))
  (plambda ((t type))
    (lambda ((xs (listof t acyclic))) (if (null? xs) 0 (+ 1 (k-length (cdr xs)))))))
(define k-nth
  (poly ((t type)) (subr (read @globals) ((listof t acyclic) int) t))
  (plambda ((t type))
    (lambda ((xs (listof t acyclic)) (i int)) (if (= i 0) (car xs) (k-nth (cdr xs) (- i 1))))))
(define k-has-name? (subr (maxeff (read @globals) (read @t)) (k-names symbol) bool)
  (lambda (xs s) (cond ((null? xs) #f) ((symbol=? (car xs) s) #t) (else (k-has-name? (cdr xs) s)))))
;; The I/O effects' kinds (`TODO.md` §84), by number, as the Rust
;; checker's `IoKind`; a name's number, -1 if none.
(define k-io-kind-name (subr pure (int) string)
  (lambda (k)
    (case k ((0) "stdin") ((1) "stdout") ((2) "stderr") ((3) "fs-read") ((4) "fs-write")
            ((5) "clock") ((6) "args") ((7) "exit") ((8) "terminal") ((9) "native") ((10) "sys")
            (else "process"))))
(define k-io-kind-code (subr pure (string) int)
  (lambda (n)
    (case n (("stdin") 0) (("stdout") 1) (("stderr") 2) (("fs-read") 3) (("fs-write") 4)
            (("clock") 5) (("args") 6) (("exit") 7) (("terminal") 8) (("native") 9)
            (("sys") 10) (("process") 11)
            (else -1))))
(define k-io-kinds-shown string
  (string-append "`stdin`, `stdout`, `stderr`, `fs-read`, `fs-write`, `clock`, `args`, `exit`, "
                 "`terminal`, `native`, `sys`, `process`"))
(define k-has-id? (subr (maxeff (read @globals) (read @t)) (k-ids int) bool)
  (lambda (xs s) (cond ((null? xs) #f) ((= (car xs) s) #t) (else (k-has-id? (cdr xs) s)))))

;;; ------------------------------------------------------------ the arena

;; Whether `t` was read from `->*`.
(define k-arrow-star-ty? (subr (maxeff (read @globals) (read @t)) (int) bool)
  (lambda (t) (k-has-id? (get k-arrow-star-tys) t)))
;; `to`, made from `from` (its `select`s resolved, say), read from `->*` if
;; `from` was: then as a node of its own, since the mark is on its id.
(define k-arrow-star-as (subr (maxeff kstate spin) (int int) int)
  (lambda (from to)
    (if (and (not (= from to)) (k-arrow-star-ty? from))
        (let ((own (k-ty-fresh to)))
          (begin (set k-arrow-star-tys (cons own (get k-arrow-star-tys))) own))
        to)))
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
          (else (and (k-ty-same? (car a) (car b)) (k-cyc-same? (cdr a) (cdr b)))))))
;; Each cycle interned, by its canonical form from each of its nodes.
(define k-cyclic (ref (table k-cyc-key int @t) @t) (new (make-table k-cyc-hash k-cyc-same?)))
(define k-interned (ref (table k-ty int @t) @t) (new (make-table k-ty-hash k-ty-same?)))
;; How many times the arena was begun again (`k-intern-reset`): what a memo of
;; nodes kept elsewhere is let go at (`k-proven`).
(define k-arena-gen (ref int @t) (new 0))
;; Each description function applied, by `(ty-app f ds)`, its parts as they
;; resolve: what it reduced to, made once (`k-apply-fun`; a `.fasl`'s
;; families are applied where each was written out).
(define k-applied (ref (table k-ty k-desc @t) @t) (new (make-table k-ty-hash k-ty-same?)))
;; Entries past which the table is let go and begun again.
(define k-intern-budget int 400000)
(define k-intern-reset (subr kstate () unit)
  (lambda ()
    (begin (set k-interned (make-table k-ty-hash k-ty-same?))
           (set k-cyclic (make-table k-cyc-hash k-cyc-same?))
           (set k-applied (make-table k-ty-hash k-ty-same?))
           (set k-arena-gen (+ (get k-arena-gen) 1)))))
(define k-applied-has? (subr (maxeff (read @globals) (read @t)) (k-ty) bool)
  (lambda (key) (table-has? (get k-applied) key)))
(define k-applied-get (subr (maxeff (read @globals) (read @t)) (k-ty) k-desc)
  (lambda (key) (table-ref (get k-applied) key (de nil))))
(define k-applied-put! (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t)) (k-ty k-desc)
                              unit)
  (lambda (key d) (table-set! (get k-applied) key d)))
;; `stringof`'s number among the generative types (`check::STRINGOF`).
(define k-stringof int 14)
;; Whether `ds` is `const` or `acyclic`, the heap's frozen data, alone.
(define k-heap-frozen? (subr pure (k-descs) bool)
  (lambda (ds)
    (and (not (null? ds)) (null? (cdr ds))
         (tagcase (car ds)
           (dr (r) (tagcase r (r-frozen (p f) (= p -1)) (else y #f)))
           (else y #f)))))
;; `string` where `t` is `(stringof const)`: the one type (`Arena::ty`).
(define k-string-norm (subr pure (k-ty) k-ty)
  (lambda (t)
    (tagcase t
      (ty-named (g ds) (if (and (= g k-stringof) (k-heap-frozen? ds)) (ty-base 'string) t))
      (else y t))))
;; `t`, `string`, as the `(stringof const)` it is where `other` is a
;; `stringof`, to match them region by region (`string_as_named`).
(define k-string-as-named (subr pure (k-ty k-ty) k-ty)
  (lambda (t other)
    (tagcase t
      (ty-base (s)
        (if (and (symbol=? s 'string)
                 (tagcase other (ty-named (g ds) (= g k-stringof)) (else y #f)))
            (ty-named k-stringof (list (dr (r-frozen -1 #f))))
            t))
      (else y t))))
;; Node `t0`, made: the id of one of the same parts, if interning has one;
;; its parts each followed through its links first.
(define k-ty-new (subr (maxeff kstate spin) (k-ty) int)
  (lambda (t0)
    (let ((t (k-resolve-parts (k-string-norm t0))))
      (if (k-internable? t)
          (let ((had (table-ref (get k-interned) t -1)))
            (if (>= had 0)
                had
                (let ((n (k-ty-push t)))
                  (begin
                    (if (> (table-count (get k-interned)) k-intern-budget) (k-intern-reset) #u)
                    (table-set! (get k-interned) t n)
                    n))))
          (k-ty-push t)))))
;; Node `n`, each type part followed through its links.
(define k-resolve-parts (subr (maxeff kstate spin) (k-ty) k-ty)
  (lambda (n)
    (letrec ((ids (subr (maxeff kstate spin) (k-ids) k-ids)
               (lambda (xs) (if (null? xs) nil (cons (k-resolve (car xs)) (ids (cdr xs))))))
             (parts (subr (maxeff kstate spin) (k-parts) k-parts)
               (lambda (ps)
                 (if (null? ps)
                     nil
                     (cons (product (1 (extract (car ps) 1)) (2 (k-resolve (extract (car ps) 2))))
                           (parts (cdr ps)))))))
      (tagcase n
        (ty-subr (e ps r cv spc) (ty-subr e (ids ps) (k-resolve r) cv spc))
        (ty-poly (bs x) (ty-poly bs (k-resolve x)))
        (ty-ref (x r) (ty-ref (k-resolve x) r))
        (ty-pair (x y r nl) (ty-pair (k-resolve x) (k-resolve y) r nl))
        (ty-product (ps) (ty-product (parts ps)))
        (ty-sum (ps) (ty-sum (parts ps)))
        (ty-array (x m r) (ty-array (k-resolve x) m r))
        (ty-nlist (x m r) (ty-nlist (k-resolve x) m r))
        (ty-union (ms) (ty-union (ids ms)))
        (ty-module (abs ds vs) (ty-module abs (parts ds) (parts vs)))
        (else y n)))))
;; Type `t`'s node again, as one of its own, which interning never gives:
;; for a type whose id is marked (`k-arrow-star-tys`).
(define k-ty-fresh (subr (maxeff kstate spin) (int) int)
  (lambda (t) (k-ty-push (k-get t))))
;; Node `t`, made anew.
(define k-ty-push (subr (maxeff kstate spin) (k-ty) int)
  (lambda (t)
    (let ((n (get k-ntys)))
      (begin
        (if (= n (array-length (get k-tys)))
            (let ((bigger (the (arrayof k-ty @t) (make-array (* 2 n) (ty-void)))))
              (begin (k-copy-array (get k-tys) bigger 0) (set k-tys bigger)))
            #u)
        (array-set! (get k-tys) n t)
        (set k-ntys (+ n 1))
        n))))

(define k-raw (subr kreads (int) k-ty) (lambda (id) (array-ref (get k-tys) id)))
;; Follow forwarding links to the type itself.
(define k-resolve (subr (maxeff kreads spin) (int) int)
  (lambda (id)
    (tagcase (k-raw id)
      (ty-link (to) (if (null? to) id (k-resolve (car to))))
      (else x id))))
(define k-get (subr (maxeff kreads spin) (int) k-ty) (lambda (id) (k-raw (k-resolve id))))
;; How many links have been made from the types below `k-links-below`, those
;; of the tree of names kept (`k-atree-now`): what one of them resolves to
;; changes only with one. A type made after it is in no tree kept.
(define k-links (ref int @t) (new 0))
(define k-links-below (ref int @t) (new 0))
(define k-set-link (subr kstate (int int) unit)
  (lambda (slot to)
    (begin (if (< slot (get k-links-below)) (set k-links (+ (get k-links) 1)) #u)
           (array-set! (get k-tys) slot (ty-link (cons to nil))))))
(define k-slot (subr (maxeff kstate spin) () int) (lambda () (k-ty-new (ty-link nil))))

;;; ------------------------------------------- cycles interned by structure
;;; A substitution copies a recursive type as a cycle of nodes of its own,
;;; which interning by parts cannot share (`TODO.md` §141, item 2). After
;;; one, the nodes it made are taken group by strongly connected group,
;;; those below first (Tarjan): a group of no cycle interned by its parts,
;;; now theirs; a cycle minimized (Moore's refinement) and looked up by its
;;; canonical form from each node, so that equal recursive types are one
;;; node, and so are the types made of them. A node made again is linked to
;;; the one it is the same as. Older nodes are left as they are.

;; A node's type parts, of a kind interning keeps.
(define k-ty-kids (->* (k-ty) k-ids)
  (lambda (n)
    (letrec ((parts (->* (k-parts k-ids) k-ids)
               (lambda (ps acc)
                 (if (null? ps) acc (cons (extract (car ps) 2) (parts (cdr ps) acc)))))
             (descs (->* (k-descs) k-ids)
               (lambda (ds)
                 (if (null? ds)
                     nil
                     (tagcase (car ds)
                       (dt (x) (cons x (descs (cdr ds))))
                       (df (x) (cons x (descs (cdr ds))))
                       (else y (descs (cdr ds))))))))
      (tagcase n
        (ty-subr (e ps r cv spc) (cons r ps))
        (ty-poly (bs x) (list x))
        (ty-ref (x r) (list x))
        (ty-pair (x y r nl) (list x y))
        (ty-product (ps) (parts ps nil))
        (ty-sum (ps) (parts ps nil))
        (ty-array (x m r) (list x))
        (ty-named (g ds) (descs ds))
        (ty-nlist (x m r) (list x))
        (ty-union (ms) ms)
        (ty-module (abs ds vs) (parts ds (parts vs nil)))
        (else y nil)))))
;; Node `n`, each of those parts `x` as `(f x)`.
(define k-ty-map-kids (->* (k-ty (subr (maxeff kstate spin) (int) int)) k-ty)
  (lambda (n f)
    (letrec ((ids (->* (k-ids) k-ids)
               (lambda (xs) (if (null? xs) nil (cons (f (car xs)) (ids (cdr xs))))))
             (parts (->* (k-parts) k-parts)
               (lambda (ps)
                 (if (null? ps)
                     nil
                     (cons (product (1 (extract (car ps) 1)) (2 (f (extract (car ps) 2))))
                           (parts (cdr ps))))))
             (descs (->* (k-descs) k-descs)
               (lambda (ds)
                 (if (null? ds)
                     nil
                     (cons (tagcase (car ds) (dt (x) (dt (f x))) (df (x) (df (f x))) (else d d))
                           (descs (cdr ds)))))))
      (tagcase n
        (ty-subr (e ps r cv spc) (ty-subr e (ids ps) (f r) cv spc))
        (ty-poly (bs x) (ty-poly bs (f x)))
        (ty-ref (x r) (ty-ref (f x) r))
        (ty-pair (x y r nl) (ty-pair (f x) (f y) r nl))
        (ty-product (ps) (ty-product (parts ps)))
        (ty-sum (ps) (ty-sum (parts ps)))
        (ty-array (x m r) (ty-array (f x) m r))
        (ty-named (g ds) (ty-named g (descs ds)))
        (ty-nlist (x m r) (ty-nlist (f x) m r))
        (ty-union (ms) (ty-union (ids ms)))
        (ty-module (abs ds vs) (ty-module abs (parts ds) (parts vs)))
        (else y n)))))

;; The walk's state: the nodes from `k-cz-base` up to `k-cz-end` are those
;; made; by node, its number in the walk, the least number it reaches (each
;; -1 not yet), and its group (-1 while on the stack).
(define k-cz-base (ref int @t) (new 0))
(define k-cz-end (ref int @t) (new 0))
(define k-cz-idx (ref (arrayof int @t) @t) (new (make-array 0 0)))
(define k-cz-low (ref (arrayof int @t) @t) (new (make-array 0 0)))
(define k-cz-scc (ref (arrayof int @t) @t) (new (make-array 0 0)))
(define k-cz-count (ref int @t) (new 0))
(define k-cz-groups (ref int @t) (new 0))
(define k-cz-stack (ref k-ids @t) (new nil))
(define k-cz-made? (->* (int) bool)
  (lambda (x) (and (>= x (get k-cz-base)) (< x (get k-cz-end)))))
(define k-cz-at (->* ((ref (arrayof int @t) @t) int) int)
  (lambda (a x) (array-ref (get a) (- x (get k-cz-base)))))
(define k-cz-set! (->* ((ref (arrayof int @t) @t) int int) unit)
  (lambda (a x v) (array-set! (get a) (- x (get k-cz-base)) v)))
;; Whether `x` is a node of group `g`.
(define k-cz-in? (->* (int int) bool)
  (lambda (x g) (and (k-cz-made? x) (= (k-cz-at k-cz-scc x) g))))
;; The stack's nodes down to `v`, a group: each given its number.
(define k-cz-pop (->* (int int k-ids) k-ids)
  (lambda (v g acc)
    (let ((x (car (get k-cz-stack))))
      (begin
        (set k-cz-stack (cdr (get k-cz-stack)))
        (k-cz-set! k-cz-scc x g)
        (if (= x v) (cons x acc) (k-cz-pop v g (cons x acc)))))))
(define k-cz-all-internable? (->* (k-ids) bool)
  (lambda (ms)
    (or (null? ms) (and (k-internable? (k-raw (car ms))) (k-cz-all-internable? (cdr ms))))))
(define k-cz-any-in? (->* (k-ids int) bool)
  (lambda (ks g)
    (and (not (null? ks)) (or (k-cz-in? (k-resolve (car ks)) g) (k-cz-any-in? (cdr ks) g)))))
;; Each node of group `g` (in `nodes`) numbered by its parts, those in the
;; group by their classes in `cls` (all one, the first time), into `next`:
;; how many numbers.
(define k-cz-number
  (->* ((arrayof int @t) (arrayof int @t) (arrayof int @t) int bool) int)
  (lambda (nodes cls next g first)
    (let ((seen (the (table k-ty int @t) (make-table k-ty-hash k-ty-same?)))
          (f (lambda ((x0 int))
               (let ((x (k-resolve x0)))
                 (cond ((not (k-cz-in? x g)) x)
                       (first k-cyc-at)
                       (else (+ k-cyc-at (array-ref cls (k-cz-at k-cz-idx x)))))))))
      (letrec ((each (->* (int int) int)
                 (lambda (i n)
                   (if (>= i (array-length nodes))
                       n
                       (let* ((key (k-ty-map-kids (k-raw (array-ref nodes i)) f))
                              (had (table-ref seen key -1)))
                         (if (>= had 0)
                             (begin (array-set! next i had) (each (+ i 1) n))
                             (begin (table-set! seen key n)
                                    (array-set! next i n)
                                    (each (+ i 1) (+ n 1)))))))))
        (each 0 0)))))
;; Classes refined until they are as many as before, `n`: how many.
(define k-cz-refine (->* ((arrayof int @t) (arrayof int @t) int int) int)
  (lambda (nodes cls g n)
    (let* ((next (the (arrayof int @t) (make-array (array-length nodes) 0)))
           (m (k-cz-number nodes cls next g #f)))
      (begin (k-copy-array next cls 0)
             (if (= m n) n (k-cz-refine nodes cls g m))))))
;; The classes from class `d` in the order first met, onto `order` (last
;; first), each numbered in `num` (its last slot the count).
(define-rec
  (k-cz-dfs
    (->* ((arrayof int @t) (arrayof int @t) (arrayof int @t) (arrayof int @t) (ref k-ids @t) int
          int)
         unit)
    (lambda (nodes cls rep num order d g)
      (let ((c (- (array-length num) 1)))
        (begin
          (array-set! num d (array-ref num c))
          (array-set! num c (+ (array-ref num c) 1))
          (set order (cons d (get order)))
          (k-cz-dfs-kids nodes cls rep num order
                         (k-ty-kids (k-raw (array-ref nodes (array-ref rep d)))) g)))))
  (k-cz-dfs-kids
    (->* ((arrayof int @t) (arrayof int @t) (arrayof int @t) (arrayof int @t) (ref k-ids @t)
          k-ids int)
         unit)
    (lambda (nodes cls rep num order ks g)
      (if (null? ks)
          #u
          (let ((x (k-resolve (car ks))))
            (begin
              (if (k-cz-in? x g)
                  (let ((e (array-ref cls (k-cz-at k-cz-idx x))))
                    (if (< (array-ref num e) 0) (k-cz-dfs nodes cls rep num order e g) #u))
                  #u)
              (k-cz-dfs-kids nodes cls rep num order (cdr ks) g)))))))
;; The canonical form of classes `ds` (last first) onto `acc`: each its
;; first node, its parts in the group by number.
(define k-cz-emit
  (->* ((arrayof int @t) (arrayof int @t) (arrayof int @t) (arrayof int @t) k-ids int k-cyc-key)
       k-cyc-key)
  (lambda (nodes cls rep num ds g acc)
    (if (null? ds)
        acc
        (let ((f (lambda ((x0 int))
                   (let ((x (k-resolve x0)))
                     (if (k-cz-in? x g)
                         (+ k-cyc-at (array-ref num (array-ref cls (k-cz-at k-cz-idx x))))
                         x)))))
          (k-cz-emit nodes cls rep num (cdr ds) g
                     (cons (k-ty-map-kids (k-raw (array-ref nodes (array-ref rep (car ds)))) f)
                           acc))))))
(define k-cz-place (->* (k-ids int (arrayof int @t)) unit)
  (lambda (ms i nodes)
    (if (null? ms)
        #u
        (begin (array-set! nodes i (car ms))
               (k-cz-set! k-cz-idx (car ms) i)
               (k-cz-place (cdr ms) (+ i 1) nodes)))))
(define k-cz-firsts (->* ((arrayof int @t) (arrayof int @t) int) unit)
  (lambda (cls rep i)
    (if (>= i (array-length cls))
        #u
        (begin (if (< (array-ref rep (array-ref cls i)) 0) (array-set! rep (array-ref cls i) i) #u)
               (k-cz-firsts cls rep (+ i 1))))))
;; Each class from `d` on: the node it is, found by its form, or its first
;; node, noted by it.
(define k-cz-targets
  (->* ((arrayof int @t) (arrayof int @t) (arrayof int @t) (arrayof int @t) int int) unit)
  (lambda (nodes cls rep target d g)
    (if (>= d (array-length rep))
        #u
        (let* ((num (the (arrayof int @t) (make-array (+ (array-length rep) 1) -1)))
               (order (the (ref k-ids @t) (new nil))))
          (begin
            (array-set! num (array-length rep) 0)
            (k-cz-dfs nodes cls rep num order d g)
            (let* ((key (k-cz-emit nodes cls rep num (get order) g nil))
                   (found (table-ref (get k-cyclic) key -1))
                   (first (array-ref nodes (array-ref rep d))))
              (if (>= found 0)
                  (array-set! target d found)
                  (begin (table-set! (get k-cyclic) key first) (array-set! target d first))))
            (k-cz-targets nodes cls rep target (+ d 1) g))))))
(define k-cz-link (->* ((arrayof int @t) (arrayof int @t) (arrayof int @t) int) unit)
  (lambda (nodes cls target i)
    (if (>= i (array-length nodes))
        #u
        (let ((to (array-ref target (array-ref cls i))) (x (array-ref nodes i)))
          (begin (if (= to x) #u (k-set-link x to))
                 (k-cz-link nodes cls target (+ i 1)))))))
;; Cycle `ms`, group `g`: minimized, each class the node its form names.
(define k-cz-cyclic (->* (k-ids int) unit)
  (lambda (ms g)
    (let* ((s (k-length ms))
           (nodes (the (arrayof int @t) (make-array s 0)))
           (cls (the (arrayof int @t) (make-array s 0))))
      (begin
        (k-cz-place ms 0 nodes)
        (let* ((c (k-cz-refine nodes cls g (k-cz-number nodes cls cls g #t)))
               (rep (the (arrayof int @t) (make-array c -1)))
               (target (the (arrayof int @t) (make-array c -1))))
          (begin (k-cz-firsts cls rep 0)
                 (k-cz-targets nodes cls rep target 0 g)
                 (k-cz-link nodes cls target 0)))))))
;; A group done: of one node and no cycle, interned by its parts; a cycle,
;; by its form; else left.
(define k-cz-group (->* (int) unit)
  (lambda (v)
    (let* ((g (get k-cz-groups))
           (ms (begin (set k-cz-groups (+ g 1)) (k-cz-pop v g nil))))
      (cond ((not (k-cz-all-internable? ms)) #u)
            ((and (null? (cdr ms)) (not (k-cz-any-in? (k-ty-kids (k-raw v)) g)))
             (let ((id (k-ty-new (k-raw v)))) (if (= id v) #u (k-set-link v id))))
            (else (k-cz-cyclic ms g))))))
(define-rec
  (k-cz-visit (->* (int) unit)
    (lambda (v)
      (let ((n (get k-cz-count)))
        (begin
          (k-cz-set! k-cz-idx v n)
          (k-cz-set! k-cz-low v n)
          (set k-cz-count (+ n 1))
          (set k-cz-stack (cons v (get k-cz-stack)))
          (k-cz-kids v (k-ty-kids (k-raw v)))
          (if (= (k-cz-at k-cz-low v) n) (k-cz-group v) #u)))))
  (k-cz-kids (->* (int k-ids) unit)
    (lambda (v ks)
      (if (null? ks)
          #u
          (let ((w (k-resolve (car ks))))
            (begin
              (if (k-cz-made? w)
                  (cond ((< (k-cz-at k-cz-idx w) 0)
                         (begin (k-cz-visit w)
                                (if (< (k-cz-at k-cz-low w) (k-cz-at k-cz-low v))
                                    (k-cz-set! k-cz-low v (k-cz-at k-cz-low w))
                                    #u)))
                        ((and (< (k-cz-at k-cz-scc w) 0)
                              (< (k-cz-at k-cz-idx w) (k-cz-at k-cz-low v)))
                         (k-cz-set! k-cz-low v (k-cz-at k-cz-idx w)))
                        (else #u))
                  #u)
              (k-cz-kids v (cdr ks))))))))
;; Each of `rs` not yet met, walked.
(define k-cz-visit-each (->* (k-ids) unit)
  (lambda (rs)
    (if (null? rs)
        #u
        (let ((r (k-resolve (car rs))))
          (begin (if (and (k-cz-made? r) (< (k-cz-at k-cz-idx r) 0)) (k-cz-visit r) #u)
                 (k-cz-visit-each (cdr rs)))))))
;; The types `roots` a substitution made, its nodes from `base` on:
;; interned, in one walk, so that what they share is interned once.
(define k-intern-made-all (->* (int k-ids) unit)
  (lambda (base roots)
    (let ((end (get k-ntys)))
      (begin
        (set k-cz-base base)
        (set k-cz-end end)
        (set k-cz-idx (make-array (- end base) -1))
        (set k-cz-low (make-array (- end base) -1))
        (set k-cz-scc (make-array (- end base) -1))
        (set k-cz-count 0)
        (set k-cz-stack nil)
        (k-cz-visit-each roots)))))
;; The type `root` a substitution made, its nodes from `base` on: interned.
(define k-intern-made (->* (int int) int)
  (lambda (base root) (begin (k-intern-made-all base (list root)) (k-resolve root))))

;; Which types a walk has seen: a type is seen in walk `e` when its mark
;; is `e`, so each walk takes a new epoch and nothing is cleared.
(define k-marks (ref (arrayof int @t) @t) (new (make-array 512 0)))
(define k-epoch (ref int @t) (new 0))
(define k-new-epoch (subr kstate () int)
  (lambda () (begin (set k-epoch (+ (get k-epoch) 1)) (get k-epoch))))
;; Whether walk `e` has seen `t` already; if not, it has now.
(define k-visit? (subr (maxeff kstate spin) (int int) bool)
  (lambda (t e)
    (begin
      (if (>= t (array-length (get k-marks)))
          (let ((bigger (the (arrayof int @t) (make-array (* 2 (array-length (get k-tys))) 0))))
            (begin (k-copy-array (get k-marks) bigger 0) (set k-marks bigger)))
          #u)
      (if (= (array-ref (get k-marks) t) e)
          #t
          (begin (array-set! (get k-marks) t e) #f)))))

;; Description variables, newest first, for their names.
(define k-dvars (ref k-names @t) (new nil))
(define k-ndvars (ref int @t) (new 0))
(define k-new-dvar (subr kstate (symbol) int)
  (lambda (name)
    (let ((n (get k-ndvars)))
      (begin (set k-dvars (cons name (get k-dvars))) (set k-ndvars (+ n 1)) n))))
;; The description variables bound as places (kind 3), which are regions too.
(define k-places (ref k-ids @t) (new nil))
;; Which description variables are of kind `flat` (`TODO.md` §77).
(define k-flats (ref k-ids @t) (new nil))
(define k-datas (ref k-ids @t) (new nil))
;; The variables `acyclic?` has just found acyclic, in the branch where it
;; did: each by name and by which binding it is (how deep its name's stack).
(define k-certified (ref (listof (pairof symbol int @t) acyclic) @t) (new nil))
(define k-narrowed (ref k-narrows @t) (new nil))
;; Whether `k-unify` is inside a pair's contents (the Rust checker's
;; `unify_exact`).
(define k-unify-exact (ref bool @t) (new #f))
(define k-pending-unions (ref k-pendings @t) (new nil))
;; The sizes given to `nat` variables of no known size, newest first
;; (`k-name-nat`).
(define k-skolems (ref k-ids @t) (new nil))
;; Of those, the lengths given to arrays that run to the end of the suffix
;; (`Checker::to_end_sizes`): each means just what `finite` does there.
(define k-to-end-sizes (ref k-ids @t) (new nil))
;; The same for `nat?`: the variables it has just found no less than 0.
(define k-certified-nats (ref (listof (pairof symbol int @t) acyclic) @t) (new nil))
(define k-certified-lengths (ref (listof k-cert-len acyclic) @t) (new nil))
(define k-arrows (ref (listof k-arrow-kind acyclic) @t) (new nil))
(define k-narrows (ref int @t) (new 0))
(define k-ids=? (subr (read @globals) (k-ids k-ids) bool)
  (lambda (xs ys)
    (cond ((null? xs) (null? ys))
          ((null? ys) #f)
          (else (and (= (car xs) (car ys)) (k-ids=? (cdr xs) (cdr ys)))))))
;; The kind of the arrow `ps` to `r` among `as`, `n` of them, newest first;
;; or -1.
(define k-arrow-find (subr kreads ((listof k-arrow-kind acyclic) k-ids int int) int)
  (lambda (as ps r n)
    (cond ((null? as) -1)
          ((and (= (cdr (car as)) r) (k-ids=? (car (car as)) ps)) (+ 100 (- n 1)))
          (else (k-arrow-find (cdr as) ps r (- n 1))))))
;; The arrow kind `(=> (ps …) r)`, interned.
(define k-arrow (subr (maxeff kstate spin) (k-ids int) int)
  (lambda (ps r)
    (let ((found (k-arrow-find (get k-arrows) ps r (get k-narrows))))
      (if (>= found 0)
          found
          (let ((n (get k-narrows)))
            (begin
              (set k-arrows (cons (cons ps r) (get k-arrows)))
              (set k-narrows (+ n 1))
              (+ 100 n)))))))
;; An arrow kind's parameters' kinds and result's, none or one: none for a
;; base kind, or none known (-1).
(define k-arrow-parts (subr kreads (int) (listof k-arrow-kind acyclic))
  (lambda (k)
    (if (< k 100)
        nil
        (cons (k-nth (get k-arrows) (- (- (get k-narrows) 1) (- k 100))) nil))))
(define k-arrow-kind? (subr pure (int) bool) (lambda (k) (>= k 100)))
;; The kind an arrow kind gives, or -1 for any other.
(define k-arrow-result (subr kreads (int) int)
  (lambda (k) (let ((a (k-arrow-parts k))) (if (null? a) -1 (cdr (car a))))))
;; The kinds an arrow kind takes, or none for any other.
(define k-arrow-params (subr kreads (int) k-ids)
  (lambda (k) (let ((a (k-arrow-parts k))) (if (null? a) nil (car (car a))))))
;; Binders' kinds.
(define k-binder-kinds (subr (read @globals) (k-binders) k-ids)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 2) (k-binder-kinds (cdr bs))))))
;; Each description variable of an arrow kind, or of kind `sendable`, with
;; its kind (`check-kinds.fx`).
(define k-arrow-vars (ref (listof (pairof int int @t) acyclic) @t) (new nil))
;; The description-function variables that are a module's abstract type
;; constructors, whose representations no one outside can see: what is
;; given to one is kept, cautiously, everywhere (`k-knot-in`).
(define k-abstract-funs (ref k-ids @t) (new nil))
(define k-new-dvar-of (subr kstate (symbol int) int)
  (lambda (name kind)
    (let ((v (k-new-dvar name)))
      (begin (if (= kind 3) (set k-places (cons v (get k-places))) #u)
             (if (= kind 4) (set k-datas (cons v (get k-datas))) #u)
             (if (= kind 7) (set k-flats (cons v (get k-flats))) #u)
             (if (or (= kind 8) (>= kind 100))
                 (set k-arrow-vars (cons (cons v kind) (get k-arrow-vars)))
                 #u)
             v))))
;; Which description variables are of kind `data`.
(define k-data-var? (subr (maxeff (read @globals) (read @t)) (int) bool)
  (lambda (v) (k-has-id? (get k-datas) v)))
(define k-place-var? (subr (maxeff (read @globals) (read @t)) (int) bool)
  (lambda (v) (k-has-id? (get k-places) v)))
(define k-flat-var? (subr (maxeff (read @globals) (read @t)) (int) bool)
  (lambda (v) (k-has-id? (get k-flats) v)))
;; Each description variable of an arrow kind, with its kind
;; (`k-new-dvar-of` notes them).
(define k-dvar-kind (subr kreads (int) int)
  (lambda (v)
    (letrec ((find (subr kreads ((listof (pairof int int @t) acyclic)) int)
                     (lambda (xs)
                       (cond ((null? xs) -1)
                             ((= (car (car xs)) v) (cdr (car xs)))
                             (else (find (cdr xs)))))))
      (let ((a (find (get k-arrow-vars))))
        (cond ((>= a 0) a) ((k-place-var? v) 3) ((k-data-var? v) 4) ((k-flat-var? v) 7)
              (else 2))))))
(define k-bounds (ref k-bounded @t) (new nil))
(define k-outers (ref k-nesting @t) (new nil))
;; Region variables that alias no other region in their scope: binders
;; marked `distinct`, and `letregion`'s fresh regions (`Arena::set_distinct`;
;; `docs/research/region-anti-aliasing.md`, (C)).
(define k-distincts (ref k-ids @t) (new nil))
(define k-distinct-var? (subr (maxeff (read @globals) (read @t)) (int) bool)
  (lambda (v) (k-has-id? (get k-distincts) v)))
(define k-set-distinct (subr kstate (int) unit)
  (lambda (v) (set k-distincts (cons v (get k-distincts)))))
;; The region and place variables bound around what is being read, by
;; expressions (not types), innermost first.
(define k-lifetimes (ref k-ids @t) (new nil))
;; The regions `letfreeze`s are freezing, and those of them anything has
;; written: data never written is finite.
(define k-freezing (ref k-ids @t) (new nil))
(define k-written (ref k-ids @t) (new nil))
(define k-recursive (ref k-named @t) (new nil))
(define k-std (ref k-named @t) (new nil))
;; The same, a table: each standard name's binding, newest (`k-bind-std`).
(define k-std-table (ref (table symbol int @t) @t) (new (make-table symbol-hash symbol=?)))
;; The standard binding of `s`, -1 if none.
(define k-std-type (subr (maxeff (read @globals) (read @t)) (symbol) int)
  (lambda (s) (table-ref (get k-std-table) s -1)))
;; Whether binding `t` of `s` is the standard one.
(define k-std-binding? (subr (maxeff (read @globals) (read @t)) (symbol int) bool)
  (lambda (s t) (and (>= t 0) (= (k-std-type s) t))))
(define k-gens (ref (listof k-gen acyclic) @t) (new nil))
(define k-ngens (ref int @t) (new 0))
(define k-gen-of (subr kreads (int) k-gen)
  (lambda (g) (k-nth (get k-gens) (- (- (get k-ngens) 1) g))))
;; The generative types whose insides the definition being checked may see;
;; the definitions still to come that may see inside one; and the bindings
;; of their conversions, which are the identity.
(define k-transparent (ref k-ids @t) (new nil))
(define k-inside (ref (listof (pairof symbol int @t) acyclic) @t) (new nil))
(define k-conversions (ref k-named @t) (new nil))
(define k-lemmas (ref (listof k-lemma acyclic) @t) (new nil))
(define k-pending-lemma (ref (listof k-lemma acyclic) @t) (new nil))
;; Whether the next type read may be `(->* (param …) result)`, under any
;; `poly`s: a definition's signature, its effect found (`check-program.fx`).
(define k-arrow-star (ref bool @t) (new #f))
;; The types read from `->*`: a `letrec` or `define-rec` binding at one has
;; its effect found (`check-letrec.fx`, `k-arrow-star-found`).
(define k-arrow-star-tys (ref k-ids @t) (new nil))
;; `lambda`s settled at the types `->*` found, by type and where each is
;; (`check-letrec.fx`, `k-arrow-star-settle`).
(define k-arrow-star-settled (ref k-settleds @t) (new nil))
(define k-binder-has? (subr kreads (k-binders int) bool)
  (lambda (bs v) (and (not (null? bs)) (or (= (extract (car bs) 1) v) (k-binder-has? (cdr bs) v)))))
;; Whether one of generative types `gs` has `v` among its parameters.
(define k-gens-bind? (subr kreads ((listof k-gen acyclic) int) bool)
  (lambda (gs v)
    (and (not (null? gs)) (or (k-binder-has? (extract (car gs) 2) v) (k-gens-bind? (cdr gs) v)))))
;; Whether `v` is a generative type's parameter, and `r` one or frozen into one.
(define k-gen-param? (subr kreads (int) bool)
  (lambda (v) (k-gens-bind? (get k-gens) v)))
;; The types among descriptions, and the regions.
(define k-desc-types (subr (maxeff (read @globals) (alloc @t)) (k-descs) k-ids)
  (lambda (ds)
    (if (null? ds)
        nil
        (let ((rest (k-desc-types (cdr ds))))
          (tagcase (car ds) (dt (x) (the k-ids (cons x rest))) (else y rest))))))
(define k-path-narrowed (ref k-path-facts @t) (new nil))
;; How many closures' bodies are being checked.
(define k-closure-depth (ref int @t) (new 0))
(define k-desc-regions (subr (maxeff (read @globals) (alloc @t)) (k-descs) k-regions)
  (lambda (ds)
    (if (null? ds)
        nil
        (let ((rest (k-desc-regions (cdr ds))))
          (tagcase (car ds) (dr (r) (the k-regions (cons r rest))) (else y rest))))))
;; The description variable a region is, or is frozen into; -1 if none.
(define k-region-var (subr pure (k-region) int)
  (lambda (r) (tagcase r (r-var (v) v) (r-frozen (p f) p) (else x -1))))
(define k-gen-region? (subr kreads (k-region) bool)
  (lambda (r) (let ((v (k-region-var r))) (and (>= v 0) (k-gen-param? v)))))
;; Why each member of a recursive group that may not end may not.
(define k-spin-why (ref (listof (productof (1 symbol) (2 int) (3 string)) acyclic) @t) (new nil))
(define k-named-has? (subr kreads (k-named symbol int) bool)
  (lambda (ns n t)
    (and (not (null? ns))
         (or (and (symbol=? (car (car ns)) n) (= (cdr (car ns)) t)) (k-named-has? (cdr ns) n t)))))
;; The bound given region variable `v` among `bs`: none or one.
(define k-bound-in (subr (maxeff kreads (alloc @t)) (k-bounded int) k-regions)
  (lambda (bs v)
    (cond ((null? bs) nil)
          ((= (car (car bs)) v) (the k-regions (cons (cdr (car bs)) nil)))
          (else (k-bound-in (cdr bs) v)))))
(define k-bound-of (subr (maxeff kreads (alloc @t)) (int) k-regions)
  (lambda (v) (k-bound-in (get k-bounds) v)))
;; The variables bound around `v`'s binder, among `os`.
(define k-outer-in (subr kreads (k-nesting int) k-ids)
  (lambda (os v)
    (cond ((null? os) nil) ((= (car (car os)) v) (cdr (car os))) (else (k-outer-in (cdr os) v)))))
(define k-outer-of (subr kreads (int) k-ids)
  (lambda (v) (k-outer-in (get k-outers) v)))
(define k-set-outer (subr kstate (int k-ids) unit)
  (lambda (v outer) (set k-outers (cons (cons v outer) (get k-outers)))))
(define k-dvar-name (subr (maxeff (read @globals) (read @t)) (int) symbol)
  (lambda (v) (k-nth (get k-dvars) (- (- (get k-ndvars) 1) v)))))))
