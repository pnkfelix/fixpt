;;; The checker, in FX-26: substitution, of types for type variables and of
;;; regions and effects for theirs (`k-subst` and its group). Before the
;;; types' reader, which applies type functions with it. After
;;; `check-syntax.fx`; part of the checker, `check-types.fx` first.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
;; Its types (`check-subst-types.fx`), loaded before the module so that they are not
;; among its values; the module names what it uses of them.
(let* ((check-subst-types (load-module "fx26:check-subst-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-holds-types (load-module "fx26:check-holds-types.fx"))
       (check-read-types (load-module "fx26:check-read-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (table-types (load-module "fx26:table-types.fx"))
       (reader-types (load-module "fx26:reader-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-holds (select check-holds-types check-holds-sig))
           (check-read (select check-read-types check-read-sig))
           (check-print (select check-print-types check-print-sig))
           (check-env (select check-env-types check-env-sig))
           (tables (select table-types tables-sig))
           (parser (select reader-types parser-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module
(hide (include check-subst-types) (include check-types-types))
;; The types it uses of the files before it.
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-holds) (include check-print-parts) (include check-env)
      (include tables) (include parser))
(import check-effects k-atom-region k-atom-with k-one k-union)
(import check-read k-keep-at k-subst-keep)

(define k-gen-map (->* (k-binders k-descs) k-map)
  (lambda (bs ds)
    (if (null? bs)
        nil
        (the k-map (cons (cons (extract (car bs) 1) (car ds)) (k-gen-map (cdr bs) (cdr ds)))))))
(define k-subst-conv (->* (k-conv k-map) k-conv)
  (lambda (c m)
    (tagcase c
      (cv-var (v)
        (let ((f (k-map-find m v)))
          (if (null? f) c (tagcase (cdr (car f)) (dc (x) x) (else y c)))))
      (else y c))))
(define k-subst-region (->* (k-region k-map) k-region)
  (lambda (r m)
    (tagcase r
      (r-var (v)
        (let ((f (k-map-find m v)))
          (if (null? f) r (tagcase (cdr (car f)) (dr (x) x) (else y r)))))
      ;; Frozen data's place too.
      (r-frozen (p fin)
        (let ((f (if (< p 0) (the k-map nil) (k-map-find m p))))
          (if (null? f)
              r
              (tagcase (cdr (car f))
                (dr (x)
                  (tagcase x (r-var (q) (r-frozen q fin)) (r-heap () (r-frozen -1 fin)) (else z r)))
                (else y r)))))
      (else y r))))
;; Atom `a`, not a variable, substituted into: none if it reads, allocates
;; or awaits at data frozen into the heap, which is pure (`k-frozen`), so
;; that a region variable instantiated at `acyclic` or `const` leaves none.
(define k-subst-atom (->* (k-atom k-map) k-eff)
  (lambda (a m)
    (let* ((r (k-subst-region (k-atom-region a) m))
           (heap-frozen (tagcase r (r-frozen (p f) (< p 0)) (else y #f)))
           (pure-there (tagcase a (a-read (x) #t) (a-alloc (x) #t) (a-await (x) #t) (else y #f))))
      (if (and heap-frozen pure-there) nil (k-one (k-atom-with a r))))))
(define k-subst-effect (->* (k-eff k-map) k-eff)
  (lambda (e m)
    (if (null? e)
        nil
        (let* ((a (car e))
               (rest (k-subst-effect (cdr e) m))
               (piece (tagcase a
                        (a-var (v)
                          (let ((f (k-map-find m v)))
                            (if (null? f)
                                (k-one a)
                                (tagcase (cdr (car f)) (de (x) x) (else y (k-one a))))))
                        (a-app (v ds) (k-subst-eff-app v (k-subst-eargs ds m) m))
                        (else y (k-subst-atom a m)))))
          (k-union piece rest)))))
;; What an effect function is given, substituted into.
(define k-subst-eargs (->* (k-descs k-map) k-descs)
  (lambda (ds m)
    (if (null? ds)
        nil
        (let* ((d (tagcase (car ds)
                    (dr (r) (dr (k-subst-region r m)))
                    (de (e) (de (k-subst-effect e m)))
                    (dz (z) (dz (k-subst-size z m)))
                    (dc (c) (dc (k-subst-conv c m)))
                    (else y (car ds))))
               (rest (k-subst-eargs (cdr ds) m)))
          (the k-descs (cons d rest))))))
;; Effect function `v` applied to `ds`, given what `v` is substituted by:
;; reduced, if it is a `dlambda` now (`check-kinds.fx`).
(define k-subst-eff-app (->* (int k-descs k-map) k-eff)
  (lambda (v ds m)
    (let ((f (k-map-find m v)))
      (if (null? f)
          (k-one (a-app v ds))
          (tagcase (cdr (car f))
            (df (g)
              (tagcase (k-get g)
                (ty-var (w) (k-one (a-app w ds)))
                (ty-lam (bs body)
                  (tagcase body
                    (de (e)
                      (if (= (k-length bs) (k-length ds))
                          (k-subst-effect e (k-gen-map bs ds))
                          (k-one (a-app v ds))))
                    (else z (k-one (a-app v ds)))))
                (else z (k-one (a-app v ds)))))
            (else y (k-one (a-app v ds))))))))
(define k-int-hash (->* (int) int) (lambda (t) t))
(define* k-new-smemo (subr (alloc @t) () k-smemo)
  (lambda () (make-table k-int-hash (lambda (a b) (= a b)))))
;; What an application reduced gives as a type: a type, or else the
;; application `t` as it was.
(define k-applied-type (->* (k-desc int) int)
  (lambda (d t) (tagcase d (dt (x) x) (else y t))))
(define k-memo-find (->* (k-pairs int) int)
  (lambda (ms t)
    (cond ((null? ms) -1)
          ((= (car (car ms)) t) (cdr (car ms)))
          (else (k-memo-find (cdr ms) t)))))
;; Each type a `define-type` named that mentions no variable
;; (`k-closed-in?`): substitution leaves it itself, so that it keeps its name
;; in what is shown. As the Rust checker's `closed_named`, a set: a type's
;; id kept (1), as substitution asks of every type it meets.
(define k-closed-named (ref k-smemo @t) (new (k-new-smemo)))
;; None noted yet, for a new program.
(define k-forget-closed-named (->* () unit)
  (lambda () (set k-closed-named (k-new-smemo))))
;; Whether `t` is data that mentions no variable: built of base types, `nil`,
;; `false`, unions, sums, products, pairs, references and arrays, at regions
;; that are constants, as far as it goes (`seen`, a cycle met again). As the
;; Rust checker's `closed_data`.
(define k-closed-region? (->* (k-region) bool)
  (lambda (r) (tagcase r (r-var (v) #f) (r-frozen (p f) (< p 0)) (else y #t))))
(define k-closed-in? (->* (int k-ids) bool)
  (lambda (t0 seen)
    (let ((t (k-resolve t0)))
      (or (k-has-id? seen t)
          (let ((s (the k-ids (cons t seen))))
            (tagcase (k-get t)
              (ty-base (n) #t) (ty-void () #t) (ty-nil () #t) (ty-false () #t)
              (ty-union (ms) (k-all-closed? ms s))
              (ty-sum (ps) (k-parts-closed? ps s))
              (ty-product (ps) (k-parts-closed? ps s))
              (ty-pair (a d r nl) (and (k-closed-region? r) (k-closed-in? a s) (k-closed-in? d s)))
              (ty-ref (a r) (and (k-closed-region? r) (k-closed-in? a s)))
              (ty-array (a nz r) (and (k-closed-region? r) (k-closed-in? a s)))
              (else y #f)))))))
(define k-all-closed? (->* (k-ids k-ids) bool)
  (lambda (ts seen)
    (or (null? ts) (and (k-closed-in? (car ts) seen) (k-all-closed? (cdr ts) seen)))))
(define k-parts-closed? (->* (k-parts k-ids) bool)
  (lambda (ps seen)
    (or (null? ps)
        (and (k-closed-in? (extract (car ps) 2) seen) (k-parts-closed? (cdr ps) seen)))))
;; Each slot of `fs`, declared ahead and filled, noted if it is closed.
(define k-note-closed-filled
  (->* ((listof (productof (1 int) (2 int) (3 int)) acyclic)) unit)
  (lambda (fs)
    (if (null? fs)
        #u
        (begin (k-note-closed (extract (car fs) 1)) (k-note-closed-filled (cdr fs))))))
;; `slot`, a type a `define-type` named, noted if it is closed.
(define k-note-closed (->* (int) int)
  (lambda (slot)
    (begin
      (if (k-closed-in? slot nil)
          (table-set! (get k-closed-named) (k-resolve slot) 1)
          #u)
      slot)))

;;; ------------------------------------------- what a substitution can change
;;; Each type's free substitutables (the user's, `TODO.md` §178): the
;;; description variables in it, by binder, bound inside it or not (a
;;; substitution acts on those too: binders are not renamed), and whether
;;; it holds a `select`, a parameter's `select` or an application, which
;;; it acts on otherwise. A type of none its map names it gives back
;;; itself, unwalked, a cycle or not; it was copied whole (a module's type
;;; at each use of the file that makes it: Heist's request). Kept by type,
;;; once known, only of a type that holds none of the four flagged: an
;;; unbound link may come to hold more, and a `select`, a parameter's or an
;;; application is made, where it is resolved, a link to what it is
;;; (`check-modules.fx`), which may hold variables; every other type is
;;; only ever made a link to a type of the same parts (interning). Of one
;;; in a cycle, kept at the cycle's entry.
(define k-fv-select int 1)
(define k-fv-param int 2)
(define k-fv-app int 4)
(define k-fv-unbound int 8)
;; Deeper than any walk goes: a type met that is kept already.
(define k-fv-deep int 1000000000)
(define k-fv-flags (ref (arrayof int @t) @t) (new (make-array 512 -1)))
(define k-fv-vars (ref (arrayof k-ids @t) @t) (new (make-array 512 nil)))
(define k-fv-depth (ref (arrayof int @t) @t) (new (make-array 512 0)))
(define k-fv-copy-ints (->* ((arrayof int @t) (arrayof int @t) int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i)) (k-fv-copy-ints from to (+ i 1))))))
(define k-fv-copy-ids (->* ((arrayof k-ids @t) (arrayof k-ids @t) int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i)) (k-fv-copy-ids from to (+ i 1))))))
;; Room in the tables for type `t`.
(define k-fv-room (->* (int) unit)
  (lambda (t)
    (if (< t (array-length (get k-fv-flags)))
        #u
        (let* ((n (* 2 (if (> t (array-length (get k-tys))) t (array-length (get k-tys)))))
               (flags (the (arrayof int @t) (make-array n -1)))
               (vars (the (arrayof k-ids @t) (make-array n nil)))
               (depth (the (arrayof int @t) (make-array n 0))))
          (begin (k-fv-copy-ints (get k-fv-flags) flags 0) (set k-fv-flags flags)
                 (k-fv-copy-ids (get k-fv-vars) vars 0) (set k-fv-vars vars)
                 (k-fv-copy-ints (get k-fv-depth) depth 0) (set k-fv-depth depth))))))
;; None forgotten for a new program's types (`k-reset`), as the regions'
;; memo is.
(define k-fv-forget (->* () unit)
  (lambda ()
    (begin (set k-fv-flags (make-array 512 -1)) (set k-fv-vars (make-array 512 nil))
           (set k-fv-depth (make-array 512 0)))))
;; Two sorted lists of variables, as one.
(define k-ids-union (->* (k-ids k-ids) k-ids)
  (lambda (a b)
    (cond ((null? a) b)
          ((null? b) a)
          ((< (car a) (car b)) (the k-ids (cons (car a) (k-ids-union (cdr a) b))))
          ((> (car a) (car b)) (the k-ids (cons (car b) (k-ids-union a (cdr b)))))
          (else (the k-ids (cons (car a) (k-ids-union (cdr a) (cdr b))))))))
(define k-ids-one (->* (int) k-ids) (lambda (v) (the k-ids (cons v nil))))
(define k-fv-region (->* (k-region) k-ids)
  (lambda (r)
    (tagcase r
      (r-var (v) (k-ids-one v))
      (r-frozen (p f) (if (< p 0) (the k-ids nil) (k-ids-one p)))
      (else y (the k-ids nil)))))
(define k-fv-conv (->* (k-conv) k-ids)
  (lambda (c) (tagcase c (cv-var (v) (k-ids-one v)) (else y (the k-ids nil)))))
(define k-fv-terms (->* (k-terms) k-ids)
  (lambda (ts) (if (null? ts) nil (k-ids-union (k-ids-one (car (car ts))) (k-fv-terms (cdr ts))))))
(define k-fv-size (->* (k-size) k-ids)
  (lambda (z) (tagcase z (sz-lin (k ts) (k-fv-terms ts)) (else y (the k-ids nil)))))
;; An effect's: as `k-subst-effect` substitutes it, an application's
;; arguments as `k-subst-eargs` does (a type given is not).
(define-rec
  (k-fv-eff (->* (k-eff) k-ids)
    (lambda (e) (if (null? e) nil (k-ids-union (k-fv-atom (car e)) (k-fv-eff (cdr e))))))
  (k-fv-atom (->* (k-atom) k-ids)
    (lambda (a)
      (tagcase a
        (a-var (v) (k-ids-one v))
        (a-app (v ds) (k-ids-union (k-ids-one v) (k-fv-eargs ds)))
        (else y (k-fv-region (k-atom-region a))))))
  (k-fv-eargs (->* (k-descs) k-ids)
    (lambda (ds)
      (if (null? ds)
          nil
          (k-ids-union (tagcase (car ds)
                         (dr (r) (k-fv-region r)) (de (e) (k-fv-eff e)) (dz (z) (k-fv-size z))
                         (dc (c) (k-fv-conv c)) (else y (the k-ids nil)))
                       (k-fv-eargs (cdr ds)))))))
;; Two walks' results, as one.
(define k-fv-join (->* (k-fv k-fv) k-fv)
  (lambda (a b)
    (product (1 (k-ids-union (extract a 1) (extract b 1)))
             (2 (bitwise-ior (extract a 2) (extract b 2)))
             (3 (if (< (extract a 3) (extract b 3)) (extract a 3) (extract b 3))))))
(define k-fv-leaf (->* (k-ids int) k-fv)
  (lambda (vs flags) (product (1 vs) (2 flags) (3 k-fv-deep))))
(define-rec
  ;; Type `t`'s, walked at depth `d` (from 1).
  (k-fv-walk (->* (int int) k-fv)
    (lambda (t0 d)
      (let ((t (k-resolve t0)))
        (begin
          (k-fv-room t)
          (cond ((>= (array-ref (get k-fv-flags) t) 0)
                 (k-fv-leaf (array-ref (get k-fv-vars) t) (array-ref (get k-fv-flags) t)))
                ((> (array-ref (get k-fv-depth) t) 0)
                 (product (1 (the k-ids nil)) (2 0) (3 (array-ref (get k-fv-depth) t))))
                (else
                 (begin
                   (array-set! (get k-fv-depth) t d)
                   (let ((r (k-fv-node t d)))
                     (begin
                       (array-set! (get k-fv-depth) t 0)
                       ;; Complete if nothing it met is still being walked
                       ;; above it; kept only if nothing flagged is in it.
                       (if (and (>= (extract r 3) d) (= 0 (extract r 2)))
                           (begin (array-set! (get k-fv-flags) t (extract r 2))
                                  (array-set! (get k-fv-vars) t (extract r 1)))
                           #u)
                       r)))))))))
  (k-fv-node (->* (int int) k-fv)
    (lambda (t d)
      (letrec ((ty (subr (maxeff kstate spin) (int) k-fv) (lambda (x) (k-fv-walk x (+ d 1))))
               (tys (subr (maxeff kstate spin) (k-ids) k-fv) (lambda (xs) (k-fv-walks xs (+ d 1))))
               (leaf (subr kreads (k-ids) k-fv) (lambda (vs) (k-fv-leaf vs 0)))
               (reg (subr kreads (k-region) k-fv) (lambda (r) (k-fv-leaf (k-fv-region r) 0)))
               (eff (subr kreads (k-eff) k-fv) (lambda (e) (k-fv-leaf (k-fv-eff e) 0))))
        (tagcase (k-get t)
          (ty-var (v) (leaf (k-ids-one v)))
          (ty-link (x) (k-fv-leaf nil k-fv-unbound))
          (ty-select (m n) (k-fv-leaf nil k-fv-select))
          (ty-param (k n) (k-fv-leaf nil k-fv-param))
          (ty-app (g ds)
            (k-fv-join (k-fv-leaf nil k-fv-app) (k-fv-join (ty g) (k-fv-descs ds (+ d 1)))))
          (ty-subr (e ps r cv spc)
            (k-fv-join (eff e) (k-fv-join (tys ps) (k-fv-join (ty r) (leaf (k-fv-conv cv))))))
          (ty-poly (bs body) (ty body))
          (ty-ref (a r) (k-fv-join (ty a) (reg r)))
          (ty-array (a nz r) (k-fv-join (ty a) (k-fv-join (leaf (k-fv-size nz)) (reg r))))
          (ty-icell (a r) (k-fv-join (ty a) (reg r)))
          (ty-place (r) (reg r))
          (ty-pair (a b r nl) (k-fv-join (ty a) (k-fv-join (ty b) (reg r))))
          (ty-tag (a h e r) (k-fv-join (ty a) (k-fv-join (ty h) (k-fv-join (eff e) (reg r)))))
          (ty-comp (b a e r once) (k-fv-join (ty b) (k-fv-join (ty a) (k-fv-join (eff e) (reg r)))))
          (ty-markkey (a r) (k-fv-join (ty a) (reg r)))
          (ty-product (ps) (k-fv-parts ps (+ d 1)))
          (ty-sum (ps) (k-fv-parts ps (+ d 1)))
          (ty-bloblet (fs z r) (k-fv-join (tys fs) (reg r)))
          (ty-union (ms) (tys ms))
          (ty-named (g ds) (k-fv-descs ds (+ d 1)))
          (ty-lam (bs body) (k-fv-descs (the k-descs (cons body nil)) (+ d 1)))
          (ty-nlist (e z r) (k-fv-join (ty e) (k-fv-join (leaf (k-fv-size z)) (reg r))))
          (ty-nat (z) (leaf (k-fv-size z)))
          (ty-module (abs ds vs)
            (k-fv-join (k-fv-parts abs (+ d 1))
                       (k-fv-join (k-fv-parts ds (+ d 1)) (k-fv-parts vs (+ d 1)))))
          (else y (leaf nil))))))
  (k-fv-walks (->* (k-ids int) k-fv)
    (lambda (ts d)
      (if (null? ts)
          (k-fv-leaf nil 0)
          (k-fv-join (k-fv-walk (car ts) d) (k-fv-walks (cdr ts) d)))))
  (k-fv-parts (->* (k-parts int) k-fv)
    (lambda (ps d)
      (if (null? ps)
          (k-fv-leaf nil 0)
          (k-fv-join (k-fv-walk (extract (car ps) 2) d) (k-fv-parts (cdr ps) d)))))
  (k-fv-descs (->* (k-descs int) k-fv)
    (lambda (ds d)
      (if (null? ds)
          (k-fv-leaf nil 0)
          (k-fv-join (tagcase (car ds)
                       (dt (x) (k-fv-walk x d)) (df (x) (k-fv-walk x d))
                       (dr (r) (k-fv-leaf (k-fv-region r) 0)) (de (e) (k-fv-leaf (k-fv-eff e) 0))
                       (dz (z) (k-fv-leaf (k-fv-size z) 0)) (dc (c) (k-fv-leaf (k-fv-conv c) 0)))
                     (k-fv-descs (cdr ds) d))))))
;; Whether a substitution by `m` (and the selects and parameters given now)
;; leaves `t` as it is.
(define k-subst-leaves? (->* (int k-map) bool)
  (lambda (t m)
    (let* ((f (k-fv-walk t 1)) (flags (extract f 2)))
      (and (= 0 (bitwise-and flags k-fv-app))
           (or (= 0 (bitwise-and flags k-fv-select)) (null? (get k-select-map)))
           (or (= 0 (bitwise-and flags k-fv-param)) (null? (get k-param-map)))
           (k-fv-untouched? (extract f 1) m)))))
(define k-fv-untouched? (->* (k-ids k-map) bool)
  (lambda (vs m)
    (or (null? vs) (and (null? (k-map-find m (car vs))) (k-fv-untouched? (cdr vs) m)))))
(define k-subst-memo (->* (int k-map k-smemo) int)
  (lambda (t m memo)
    (let* ((t (k-resolve t))
           (kept (or (and (>= (get k-subst-keep) 0) (= (k-keep-at t) (get k-subst-keep)))
                     (>= (table-ref (get k-closed-named) t -1) 0)))
           (done (cond (kept t)
                       ;; What it leaves, itself (`k-subst-leaves?`).
                       ((k-subst-leaves? t m) t)
                       (else (table-ref memo t -1)))))
      (if (>= done 0)
          done
          (tagcase (k-get t)
            (ty-base (s) t)
            (ty-void () t)
            (ty-link (x) t)
            (ty-var (v)
              (let ((f (k-map-find m v)))
                (if (null? f) t (tagcase (cdr (car f)) (dt (x) x) (df (x) x) (else y t)))))
            (ty-select (mod n) (k-select-of mod n t))
            (ty-param (k n) (k-param-sel-of k n t))
            ;; A function applied, given what it is substituted by:
            ;; reduced, if it is a `dlambda` now (`check-kinds.fx`).
            (ty-app (g ds)
              (let ((slot (k-slot)))
                (begin
                  (table-set! memo t slot)
                  (let* ((g2 (k-subst-memo g m memo)) (ds2 (k-subst-descs ds m memo)))
                    (begin (k-set-link slot (k-applied-type (k-apply-fun g2 ds2) t)) slot)))))
            (else y
              (let ((slot (k-slot)))
                (begin
                  (table-set! memo t slot)
                  (let ((id (k-ty-new (k-subst-node t m memo))))
                    (begin (k-set-link slot id) slot))))))))))
;; Node `t`, of a type other than a variable, with its parts substituted.
(define k-subst-node (->* (int k-map k-smemo) k-ty)
  (lambda (t m memo)
    (letrec ((sub (subr (maxeff kstate spin) (int) int)
                  (lambda (x) (k-subst-memo x m memo)))
             (subs (subr (maxeff kstate spin) (k-ids) k-ids)
                   (lambda (xs) (k-subst-list xs m memo)))
             (reg (subr kreads (k-region) k-region)
                  (lambda (r) (k-subst-region r m))))
      (tagcase (k-get t)
        (ty-subr (e ps r cv spc)
          (let* ((e2 (k-subst-effect e m)) (ps2 (subs ps)) (r2 (sub r)))
            (ty-subr e2 ps2 r2 (k-subst-conv cv m) spc)))
        (ty-poly (bs body) (ty-poly bs (sub body)))
        (ty-ref (a r) (ty-ref (sub a) (reg r)))
        (ty-array (a nz r) (ty-array (sub a) (k-subst-size nz m) (reg r)))
        (ty-icell (a r) (ty-icell (sub a) (reg r)))
        (ty-place (r) (ty-place (reg r)))
        (ty-pair (a b r nl) (let* ((a2 (sub a)) (b2 (sub b))) (ty-pair a2 b2 (reg r) nl)))
        (ty-tag (a h e r)
          (let* ((a2 (sub a)) (h2 (sub h))) (ty-tag a2 h2 (k-subst-effect e m) (reg r))))
        (ty-comp (b a e r once)
          (let* ((b2 (sub b)) (a2 (sub a))) (ty-comp b2 a2 (k-subst-effect e m) (reg r) once)))
        (ty-markkey (a r) (ty-markkey (sub a) (reg r)))
        (ty-product (ps) (ty-product (k-subst-parts ps m memo)))
        (ty-sum (ps) (ty-sum (k-subst-parts ps m memo)))
        (ty-bloblet (fs z r) (ty-bloblet (subs fs) z (reg r)))
        (ty-union (ms) (ty-union (subs ms)))
        (ty-named (g ds) (ty-named g (k-subst-descs ds m memo)))
        (ty-lam (bs body) (ty-lam bs (car (k-subst-descs (the k-descs (cons body nil)) m memo))))
        (ty-nlist (e z r) (ty-nlist (sub e) (k-subst-size z m) (reg r)))
        (ty-nat (z) (ty-nat (k-subst-size z m)))
        (ty-module (abs ds vs)
          (let* ((ds2 (k-subst-parts ds m memo)) (vs2 (k-subst-parts vs m memo)))
            (ty-module abs ds2 vs2)))
        (else z (k-get t))))))
(define k-subst-descs (->* (k-descs k-map k-smemo) k-descs)
  (lambda (ds m memo)
    (if (null? ds)
        nil
        (let* ((d (tagcase (car ds)
                    (dt (x) (dt (k-subst-memo x m memo)))
                    (dr (r) (dr (k-subst-region r m)))
                    (de (e) (de (k-subst-effect e m)))
                    (dz (z) (dz (k-subst-size z m)))
                    (dc (c) (dc (k-subst-conv c m)))
                    (df (x) (df (k-subst-memo x m memo)))))
               (rest (k-subst-descs (cdr ds) m memo)))
          (cons d rest)))))
(define k-subst-list (->* (k-ids k-map k-smemo) k-ids)
  (lambda (ts m memo)
    (if (null? ts)
        nil
        (let* ((x (k-subst-memo (car ts) m memo)) (rest (k-subst-list (cdr ts) m memo)))
          (cons x rest)))))
(define k-subst-parts (->* (k-parts k-map k-smemo) k-parts)
  (lambda (ps m memo)
    (if (null? ps)
        nil
        (let* ((x (k-subst-memo (extract (car ps) 2) m memo))
               (rest (k-subst-parts (cdr ps) m memo)))
          (cons (product (1 (extract (car ps) 1)) (2 x)) rest)))))
;; `t` with each binder in `m` replaced. Recursive types are copied as
;; cycles: each node gets its slot before its children are built.
;; A substitution of its own (a `dlambda` reduced inside another) keeps
;; nothing of another's.
(define k-subst (->* (int k-map) int)
  (lambda (t m)
    (let* ((keep (get k-subst-keep))
           (off (set k-subst-keep -1))
           (base (get k-ntys))
           (r (k-subst-memo t m (k-new-smemo))))
      (begin (set k-subst-keep keep) (k-intern-made base r)))))
;; Parts `ps`, each type with `m` for its binders: one substitution, so
;; that what the parts share is copied, and interned, once.
(define k-subst-all (->* (k-parts k-map) k-parts)
  (lambda (ps m)
    (let* ((keep (get k-subst-keep))
           (off (set k-subst-keep -1))
           (base (get k-ntys))
           (qs (k-subst-parts ps m (k-new-smemo))))
      (begin (set k-subst-keep keep)
             (k-intern-made-all base (k-part-tys qs))
             (k-resolve-each qs)))))
(define k-part-tys (->* (k-parts) k-ids)
  (lambda (ps) (if (null? ps) nil (cons (extract (car ps) 2) (k-part-tys (cdr ps))))))
(define k-resolve-each (->* (k-parts) k-parts)
  (lambda (ps)
    (if (null? ps)
        nil
        (cons (product (1 (extract (car ps) 1)) (2 (k-resolve (extract (car ps) 2))))
              (k-resolve-each (cdr ps))))))
;; Descriptions `ds`, each type or function as it resolves: for a key.
(define k-descs-resolved (->* (k-descs) k-descs)
  (lambda (ds)
    (if (null? ds)
        nil
        (cons (tagcase (car ds) (dt (t) (dt (k-resolve t))) (df (f) (df (k-resolve f))) (else d d))
              (k-descs-resolved (cdr ds))))))
;; The description of kind `k` that names binder `v`.
(define k-binder-desc (->* (int int) k-desc)
  (lambda (k v)
    (case k ((0 3) (dr (r-var v)))
            ((1) (de (k-one (a-var v))))
            ((5) (dz (k-size-var v)))
            ((6) (dc (cv-var v)))
            (else
             (cond ((>= k 100) (df (k-ty-new (ty-var v))))
                   (else (dt (k-ty-new (ty-var v)))))))))
(define-rec
    ;; Description `d` substituted into.
    (k-subst-desc (->* (k-desc k-map) k-desc)
      (lambda (d m)
        (car (k-subst-descs (the k-descs (cons d nil)) m (k-new-smemo)))))
    ;; Function `f` applied to `ds`: what a `dlambda` reduces to, or an
    ;; application that cannot be reduced. `ds` fit `f`'s kind, which the
    ;; caller has made sure of.
    (k-apply-fun (->* (int k-descs) k-desc)
      (lambda (f ds)
        (tagcase (k-get f)
          (ty-lam (bs body)
            (if (= (k-length bs) (k-length ds))
                (let ((key (ty-app (k-resolve f) (k-descs-resolved ds))))
                  (if (k-applied-has? key)
                      (k-applied-get key)
                      (let ((d (k-subst-desc body (k-gen-map bs ds))))
                        (begin (k-applied-put! key d) d))))
                (k-apply-stuck f ds)))
          (else y (k-apply-stuck f ds))))))
;; `f` applied to `ds`, which cannot be reduced: an effect, an atom of its
;; own; a function; or a type.
(define k-apply-stuck (->* (int k-descs) k-desc)
  (lambda (f ds)
    (let ((r (k-arrow-result (k-fun-kind f))))
      (cond ((= r 1)
             (tagcase (k-get f)
               (ty-var (v) (de (k-one (a-app v (k-eargs ds)))))
               (else y (de nil))))
            ((k-arrow-kind? r) (df (k-ty-new (ty-app f ds))))
            (else (dt (k-ty-new (ty-app f ds))))))))
;; What an effect function is given, of `ds`: no types.
(define k-eargs (->* (k-descs) k-descs)
  (lambda (ds)
    (cond ((null? ds) nil)
          ((tagcase (car ds) (dt (t) #t) (df (f) #t) (else y #f)) (k-eargs (cdr ds)))
          (else (the k-descs (cons (car ds) (k-eargs (cdr ds)))))))))))
