;;; The checker, in FX-26: first-class modules' rules
;;; (`docs/research/first-class-modules.md`, stage M2): `module` and `with`,
;;; module types compared, and what the termination check sees in them. The
;;; Rust checker's `modules.rs`, rule for rule; `check-modules.fx` reads and
;;; names. Part of the checker, `check-types.fx` first.

;;; ------------------------------------------------------------ module

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-module-rules-types (load-module "fx26:check-module-rules-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-synth-types (load-module "fx26:check-synth-types.fx"))
       (check-modorder-types (load-module "fx26:check-modorder-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-terminate-types (load-module "fx26:check-terminate-types.fx"))
       (check-subtype-types (load-module "fx26:check-subtype-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-errors-types (load-module "fx26:check-errors-types.fx"))
       (check-modules-types (load-module "fx26:check-modules-types.fx"))
       (check-read-types (load-module "fx26:check-read-types.fx"))
       (check-expect-types (load-module "fx26:check-expect-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-read-descs-types (load-module "fx26:check-read-descs-types.fx"))
       (check-read-helpers-types (load-module "fx26:check-read-helpers-types.fx"))
       (check-letrec-types (load-module "fx26:check-letrec-types.fx"))
       (table-types (load-module "fx26:table-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-env (select check-env-types check-env-sig))
           (check-print (select check-print-types check-print-sig))
           (check-errors (select check-errors-types check-errors-sig))
           (check-modules (select check-modules-types check-modules-sig))
           (check-read (select check-read-types check-read-sig))
           (check-modorder (select check-modorder-types check-modorder-sig))
           (check-expect (select check-expect-types check-expect-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-subtype (select check-subtype-types check-subtype-sig))
           (check-read-descs (select check-read-descs-types check-read-descs-sig))
           (check-terminate (select check-terminate-types check-terminate-sig))
           (check-letrec (select check-letrec-types check-letrec-sig))
           (tables (select table-types tables-sig))
           (check-read-helpers (select check-read-helpers-types check-read-helpers-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module
(hide (include check-module-rules-types) (include check-types-types) (include check-env-types)
      (include check-modorder-types) (include check-resolve-types) (include check-terminate-types)
      (include check-modules-types))
;; The types it uses of the files before it.
(define-type k-done (select check-synth-types k-done))
(define-type table (select table-types table))
;; The names a bucket has so far (`k-included`), each a type's or a
;; value's: by name, its type, for lookups in constant time.
(define-type k-saw (table symbol int @t))
(define-type k-saying (select check-subtype-types k-saying))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-env) (include check-print) (include check-errors)
      (include check-modules) (include check-modorder) (include check-expect)
      (include check-subtype) (include check-read-helpers) (include check-terminate)
      (include check-letrec) (include tables))
(define k-dvar-string (with check-print-parts k-dvar-string))
(define k-items (with check-read k-items))
(define k-one (with check-effects k-one))

;; `n`'s innermost binding, now of type `t`.
(define k-rebind-top (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (n t) (table-set! (get k-env) n (cons t (cdr (table-ref (get k-env) n nil))))))
;; Each of `bs` bound again at its type there.
(define k-rebind-all (subr (maxeff kstate spin) (k-letrec-bs) unit)
  (lambda (bs)
    (if (null? bs)
        #u
        (begin (k-rebind-top (extract (car bs) 1) (extract (car bs) 2)) (k-rebind-all (cdr bs))))))
;; Note of each recursive group of `gs` with a member typed `->*` whether it
;; needs `spin`, as a `define-rec`'s.
(define* k-note-star-groups (subr (maxeff checks spin) (k-groups) unit)
  (lambda (gs)
    (if (null? gs)
        #u
        (begin (if (and (not (null? (car gs))) (k-any-arrow-star? (car gs)))
                   (k-note-ending (car gs) (k-termination (car gs)))
                   #u)
               (k-note-star-groups (cdr gs))))))
;; A module's lambdas `bs`, bound, with edges `es`, and their recursive
;; groups: with members typed `->*`, every such member's effect found
;; before any lambda is checked, each recursive group with one noted as a
;; `define-rec`'s is (`k-arrow-star-found`, `synth` telling each `lambda`),
;; and they bound again at the types found; then the groups at those types.
(define* k-mod-star-groups
  (subr (maxeff checks spin) (k-edges k-letrec-bs k-lambda-synth) k-mod-found)
  (lambda (es bs synth)
    (let ((gs (k-mod-groups es bs bs)))
      (if (not (k-any-arrow-star? bs))
          (product (1 bs) (2 gs))
          (let* ((rsaved (get k-recursive))
                 (noted (k-note-star-groups gs))
                 (found (k-arrow-star-found synth bs))
                 (back (set k-recursive rsaved))
                 (rebound (k-rebind-all found)))
            (product (1 found) (2 (k-mod-groups es found found))))))))
;; `f`'s value, or, if it fails, the error `say` makes of its message.
(define k-saying (subr (maxeff (read @globals) checks spin) (k-thunk k-say) k-te)
  (lambda (f say)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb) (k-fail (say m) ea eb))
        (k-ok (xs) (k-fail "k-ok inside" 0 0))))))
;; What `define*` says when `name`, found to be a `tf`, does not check at
;; it, as `m` says: the program's error, since only that check sees a call
;; of `name` as recursion.
(define k-star-mistake (subr (maxeff kreads (alloc @t) spin) (string symbol int string) string)
  (lambda (how name tf m)
    (k-cat5 (k-cat3 how " found `" (symbol->string name)) "` to be a " (k-show-ty tf)
            ": " m)))

(define k-made-of (subr (alloc @t) (k-parts k-parts k-parts k-eff) k-made)
  (lambda (abs ds vs e) (product (1 abs) (2 ds) (3 vs) (4 e))))
;; Each of `items` that `early` names (`k-early-modules`), made by `f`, in
;; order, onto `made`: checked before the typed lambdas are bound.
(define k-mod-early
  (subr (maxeff checks spin)
        (k-items k-names (subr (maxeff checks spin) (k-item k-made) k-made) k-made)
        k-made)
  (lambda (items early f made)
    (cond ((null? items) made)
          ((and (= (extract (car items) 1) 2) (k-has-name? early (car (extract (car items) 2))))
           (let ((m (f (car items) made)))
             (begin (k-note-fixed (car (extract (car items) 2)))
                    (k-mod-early (cdr items) early f m))))
          (else (k-mod-early (cdr items) early f made)))))
;; Of parts `ps`, each a module, and its values' names (`k-mod-hazards`).
(define k-parts-modules (subr (maxeff kreads (alloc @t) spin) (k-parts) k-hazard-list)
  (lambda (ps)
    (if (null? ps)
        nil
        (let ((rest (k-parts-modules (cdr ps))))
          (tagcase (k-get (k-resolve (extract (car ps) 2)))
            (ty-module (abs ds vs)
              (the k-hazard-list (cons (product (1 (extract (car ps) 1)) (2 (k-comp-names vs)))
                                       rest)))
            (else y rest))))))
;; Lambda `l`'s type `t`, resolved: a `define*`'s the type it is checked at
;; first, reading any global, or an error at its lambda if not a `subr`.
(define k-mod-first-type (subr (maxeff checks spin) (k-mlam int) int)
  (lambda (l t)
    (if (extract l 6)
        (let ((w (k-with-latent t (k-one (a-read (r-globals))))))
          (if (< w 0)
              (begin (k-fail-at "`define*` finds what a procedure reads: its type is a `subr`"
                                (extract l 3))
                     w)
              w))
        t)))
;; The bindings of lambdas `ls`, each type resolved at `a`..`b` in turn.
(define k-mod-bindings (subr (maxeff checks spin) (k-mlams int int) k-mod-bound)
  (lambda (ls a b)
    (if (null? ls)
        (product (1 (the k-letrec-bs nil)) (2 (the k-ids nil)))
        (let* ((t (k-resolve-selects (extract (car ls) 2) a b))
               (w (k-mod-first-type (car ls) t))
               (rest (k-mod-bindings (cdr ls) a b)))
          (product (1 (the k-letrec-bs (cons (product (1 (extract (car ls) 1)) (2 w)
                                                       (3 (extract (car ls) 3)))
                                              (extract rest 1))))
                   (2 (the k-ids (cons t (extract rest 2)))))))))
;; Each of `bs` bound, known, a definition's type named as a value's is.
(define k-mod-bind (subr (maxeff kstate spin) (k-letrec-bs k-mlams) unit)
  (lambda (bs ls)
    (if (null? bs)
        #u
        (let ((n (extract (car bs) 1)) (t (extract (car bs) 2)))
          (begin (k-bind n (if (extract (car ls) 5) t (k-name-nat n t)))
                 (k-note-known n 0)
                 (k-mod-bind (cdr bs) (cdr ls)))))))
(define k-ends-of (subr (read @globals) (k-ends symbol) k-ends)
  (lambda (ws n)
    (cond ((null? ws) nil)
          ((symbol=? (extract (car ws) 1) n) ws)
          (else (k-ends-of (cdr ws) n)))))
;; `ws` with why `group` may not end, found once for the group (the same
;; for each of its members).
(define k-ends-with (subr (maxeff kstate spin) (k-ends k-letrec-bs) k-ends)
  (lambda (ws group)
    (if (or (null? group) (not (null? (k-ends-of ws (extract (car group) 1)))))
        ws
        (the k-ends (cons (product (1 (extract (car group) 1)) (2 (k-termination group))) ws)))))
;; Why `group`, found in `ws`, may not end.
(define k-group-end (subr (read @globals) (k-ends k-letrec-bs) string)
  (lambda (ws group) (extract (car (k-ends-of ws (extract (car group) 1))) 2)))
;; A member of `group` other than `n`, in a list; none if there is none.
(define k-other-member (subr (read @globals) (k-letrec-bs symbol) k-letrec-bs)
  (lambda (group n)
    (cond ((null? group) nil)
          ((symbol=? (extract (car group) 1) n) (k-other-member (cdr group) n))
          (else group))))
;; The type `bs` gives `n`.
(define k-bs-type (subr (read @globals) (k-letrec-bs symbol) int)
  (lambda (bs n)
    (if (symbol=? (extract (car bs) 1) n) (extract (car bs) 2) (k-bs-type (cdr bs) n))))
;; Names `ns`, each at its type in `bs`, onto `out`.
(define k-bs-parts (subr (maxeff (read @globals) (alloc @t)) (k-names k-letrec-bs k-parts) k-parts)
  (lambda (ns bs out)
    (if (null? ns)
        out
        (let ((t (k-bs-type bs (car ns)))) (k-bs-parts (cdr ns) bs (k-part-onto (car ns) t out))))))
;; The module's values, in written order, onto `out` (newest first): a
;; lambda's at its type in `bs`, another's as made, in `vs`.
(define k-mod-vals (subr kbuilds (k-items k-parts k-letrec-bs k-parts) k-parts)
  (lambda (items vs bs out)
    (if (null? items)
        out
        (let* ((it (car items)) (k (extract it 1)) (ns (extract it 2))
               (more (cond ((k-lambda-item? it) (k-bs-parts ns bs out))
                           ((= k 2) (k-part-onto (car ns) (k-part-of vs (car ns)) out))
                           ((= k 3) (k-bs-parts ns bs out))
                           (else out))))
          (k-mod-vals (cdr items) vs bs more)))))
;; Each value's type, `vs`, mentions none of `inner`, the sizes and abstract
;; types named inside the module; or an error at `a`..`b`.
(define k-vals-known (subr (maxeff checks spin) (k-parts k-ids int int) unit)
  (lambda (vs inner a b)
    (if (null? vs)
        #u
        (let ((v (k-first-mentioned (extract (car vs) 2) inner)))
          (if (< v 0)
              (k-vals-known (cdr vs) inner a b)
              (k-fail (k-cat5 "`" (symbol->string (extract (car vs) 1)) "`'s type mentions `"
                              (k-dvar-string v) "`, which is not known outside the module")
                      a b))))))

;;; ------------------------------------------------------------ extend

;; Whether a module is an `(extend e0 e1)` as the parser makes it (`TODO.md`
;; §69): of just `%extend-0` and `%extend-1`.
(define k-extend-item? (subr (read @globals) (k-item symbol) bool)
  (lambda (it n) (and (= (extract it 1) 2) (symbol=? (car (extract it 2)) n))))
(define k-extend-items? (subr (read @globals) (k-items) bool)
  (lambda (items)
    (and (not (null? items)) (not (null? (cdr items))) (null? (cdr (cdr items)))
         (k-extend-item? (car items) '%extend-0) (k-extend-item? (car (cdr items)) '%extend-1))))
;; One side of an `extend`, of type `t`, its own abstract types `own` and
;; `m` for all the sides' (`k-taken-abs`): a module, a bound one's abstract
;; types its descriptions, aliases.
(define k-extend-side (subr (maxeff checks spin) (int k-parts k-map) int)
  (lambda (t own m)
    (tagcase (k-get t)
      (ty-module (abs ds vs)
        (k-ty-new (ty-module own (k-subst-each (append (k-abs-aliases abs) ds) m)
                             (k-subst-each vs m))))
      (else z t))))
;; The abstract types of `t`, an `extend`'s `which` side, that are its own
;; there, fresh (`k-abs-own`); an error if it is not a module.
(define k-taken-abs (subr (maxeff checks spin) (int string int int) k-renamed)
  (lambda (t which a b)
    (tagcase (k-get t)
      (ty-module (abs ds vs) (k-abs-own abs))
      (else z (k-fail (k-cat5 "`extend` extends a module by a module, and its " which " is a "
                              (k-show-ty t) "")
                      a b)))))
;; Where the part named `n` is in `ps`, from `i`; -1 if none is.
(define k-ext-index (subr (read @globals) (k-parts symbol int) int)
  (lambda (ps n i)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) n) i)
          (else (k-ext-index (cdr ps) n (+ i 1))))))
;; Each of `p0`, or `p1`'s of its name if `p1` has one; then `p1`'s others.
(define k-ext-firsts (subr (maxeff (read @globals) (alloc @t)) (k-parts k-parts) k-parts)
  (lambda (p0 p1)
    (if (null? p0)
        nil
        (let ((k (k-ext-index p1 (extract (car p0) 1) 0)))
          (the k-parts (cons (if (< k 0) (car p0) (k-nth p1 k)) (k-ext-firsts (cdr p0) p1)))))))
(define k-ext-rest (subr (maxeff (read @globals) (alloc @t)) (k-parts k-parts) k-parts)
  (lambda (p1 p0)
    (cond ((null? p1) nil)
          ((>= (k-ext-index p0 (extract (car p1) 1) 0) 0) (k-ext-rest (cdr p1) p0))
          (else (the k-parts (cons (car p1) (k-ext-rest (cdr p1) p0)))))))
;; The same, as paths: `p0`'s from value 0, `p1`'s from value 1; `j`, `k`
;; where each is.
(define k-ext-firsts-at (subr (maxeff (read @globals) (alloc @t)) (k-parts k-parts int) k-picks)
  (lambda (p0 p1 j)
    (if (null? p0)
        nil
        (let ((k (k-ext-index p1 (extract (car p0) 1) 0)))
          (cons (if (< k 0) (pick-path 0 j) (pick-path 1 k))
                (k-ext-firsts-at (cdr p0) p1 (+ j 1)))))))
(define k-ext-rest-at (subr (maxeff (read @globals) (alloc @t)) (k-parts k-parts int) k-picks)
  (lambda (p1 p0 k)
    (cond ((null? p1) nil)
          ((>= (k-ext-index p0 (extract (car p1) 1) 0) 0) (k-ext-rest-at (cdr p1) p0 (+ k 1)))
          (else (cons (pick-path 1 k) (k-ext-rest-at (cdr p1) p0 (+ k 1)))))))
;; `(extend e0 e1)` at `a`..`b`, the `which`th there, its values `vs` the
;; two modules: one of the
;; values of both, `e1`'s where both have a name, `e0`'s in its order first
;; and then `e1`'s others; its types likewise. Made of theirs, by path
;; (`pick-path`, noted in `k-reshapes`). A side's own abstract types
;; the new module's, `e1`'s replacing `e0`'s of their names, refused if what
;; is kept mentions one (`k-replaced-check`). As Rust's `Checker::extended`.
(define k-extended (subr (maxeff checks spin) (k-parts int int int) int)
  (lambda (vs a b which)
    (let* ((x0 (extract (car vs) 2)) (x1 (extract (car (cdr vs)) 2))
           (r0 (k-taken-abs x0 "first" a b)) (r1 (k-taken-abs x1 "second" a b))
           (m (append (extract r0 2) (extract r1 2)))
           (t0 (k-extend-side x0 (extract r0 1) m))
           (t1 (k-extend-side x1 (extract r1 1) m)))
      (tagcase (k-get t0)
        (ty-module (a0 d0 v0)
          (tagcase (k-get t1)
            (ty-module (a1 d1 v1)
              (let* ((at (append (k-ext-firsts-at v0 v1 0) (k-ext-rest-at v1 v0 0)))
                     (d0 (k-parts-not-in d0 a1 #f))
                     (ds (append (k-ext-firsts d0 d1) (k-ext-rest d1 d0)))
                     (out (append (k-ext-firsts v0 v1) (k-ext-rest v1 v0)))
                     (gone (k-parts-not-in a0 (append a1 d1) #t)))
                (begin (set k-reshapes (cons (product (1 (product (1 a) (2 b) (3 which))) (2 at))
                                             (get k-reshapes)))
                       (k-replaced-check (append out ds) gone a b)
                       (k-ty-new (ty-module (append (k-parts-not-in a0 (append a1 d1) #f) a1)
                                            ds out)))))
            (else z t1)))
        (else z t0)))))
;; Those of `ps` whose names are not in `qs` (if `in?`, those that are).
(define k-parts-not-in (subr (maxeff (read @globals) (alloc @t)) (k-parts k-parts bool) k-parts)
  (lambda (ps qs in?)
    (cond ((null? ps) nil)
          ((let ((found (>= (k-ext-index qs (extract (car ps) 1) 0) 0))) (if in? found (not found)))
           (the k-parts (cons (car ps) (k-parts-not-in (cdr ps) qs in?))))
          (else (k-parts-not-in (cdr ps) qs in?)))))
;; An error at `a`..`b` if one of `ps` mentions one of abstract types `gone`,
;; `e0`'s that `e1`'s replace.
(define k-replaced-check (subr (maxeff checks spin) (k-parts k-parts int int) unit)
  (lambda (ps gone a b)
    (if (null? ps)
        #u
        (let ((h (k-first-mentioning (extract (car ps) 2) gone)))
          (if (null? h)
              (k-replaced-check (cdr ps) gone a b)
              (let ((h (symbol->string (extract (car h) 1))))
                (k-fail (k-cat5 "`" (symbol->string (extract (car ps) 1))
                                "`'s type mentions the first module's `"
                                h (k-cat3 "`, which the second's `" h "` replaces"))
                        a b)))))))
;; The first of abstract types `abs` that `t` mentions, and those after it.
(define k-first-mentioning (subr (maxeff kstate spin) (int k-parts) k-parts)
  (lambda (t abs)
    (cond ((null? abs) nil)
          ((k-mentions-var? t (extract (car abs) 2)) abs)
          (else (k-first-mentioning t (cdr abs))))))

;;; ------------------------------------------------------------ include

;; What a module's includes give (`TODO.md` §69), newest first: types,
;; values, and where each value is, by path; the abstract types that are the
;; module's own (`k-abs-own`), and the map to them.
(define-type k-incs (productof (1 k-parts) (2 k-parts) (3 k-picks) (4 k-parts) (5 k-map)))
;; `acc` with types `d`, values `v` and paths `p`.
(define k-incs-of (subr (alloc @t) (k-parts k-parts k-picks k-incs) k-incs)
  (lambda (d v p acc) (product (1 d) (2 v) (3 p) (4 (extract acc 4)) (5 (extract acc 5)))))
;; Whether a module is an `include`s' bucket, as the parser makes one: of
;; values `%include-0`, … only.
(define k-bucket-items? (subr (read @globals) (k-items) bool)
  (lambda (items)
    (letrec ((all (subr (read @globals) (k-items) bool)
                (lambda (its)
                  (or (null? its)
                      (let ((s (symbol->string (car (extract (car its) 2)))))
                        (and (= (extract (car its) 1) 2)
                             (or (k-prefix? "%include-" s) (k-prefix? "%hinclude-" s))
                             (all (cdr its))))))))
      (and (not (null? items)) (all items)))))
;; Whether `s` begins with `p`.
(define k-prefix? (subr (read @globals) (string string) bool)
  (lambda (p s)
    (and (>= (string-length s) (string-length p))
         (string=? (substring s 0 (string-length p)) p))))
;; Of abstract types `abs`, a bound module's (`k-rename-abs`'s `m..t`), each
;; a description of its variable: aliases, so that its values and `m`'s stay
;; one another's (`TODO.md` §69).
(define k-abs-aliases (subr (maxeff kstate spin) (k-parts) k-parts)
  (lambda (abs)
    (cond ((null? abs) nil)
          ((k-module-var? (extract (car abs) 2))
           (let ((t (k-ty-new (ty-var (extract (car abs) 2)))))
             (cons (product (1 (extract (car abs) 1)) (2 t)) (k-abs-aliases (cdr abs)))))
          (else (k-abs-aliases (cdr abs))))))
;; Of abstract types `abs`, those not a bound module's, of a module made
;; where it is taken in (`include`, `extend`): the new module's own, each a
;; fresh variable, and the map to them from the old, as its own
;; `define-generative`s are; two calls of one functor share a type, and
;; their types are not one another's. As Rust's `Checker::abs_taken`.
(define k-abs-own (subr (maxeff kstate spin) (k-parts) k-renamed)
  (lambda (abs)
    (cond ((null? abs) (product (1 (the k-parts nil)) (2 (the k-map nil))))
          ((k-module-var? (extract (car abs) 2)) (k-abs-own (cdr abs)))
          (else
           (let* ((a (extract (car abs) 1))
                  (k (k-dvar-kind (extract (car abs) 2)))
                  (w (k-new-dvar-of a k))
                  (noted (if (= k 2) #u (set k-abstract-funs (cons w (get k-abstract-funs)))))
                  (to (if (= k 2) (dt (k-ty-new (ty-var w))) (df (k-ty-new (ty-var w)))))
                  (rest (k-abs-own (cdr abs))))
             (product (1 (the k-parts (cons (product (1 a) (2 w)) (extract rest 1))))
                      (2 (the k-map (cons (cons (extract (car abs) 2) to) (extract rest 2))))))))))
(define k-twice (subr checks (symbol int int) void)
  (lambda (n a b) (k-fail (k-cat3 "`" (symbol->string n) "` is defined twice in this module") a b)))
;; Module type `t`, an `include`'s, or an error.
(define k-inc-module (subr (maxeff checks spin) (int int int) int)
  (lambda (t a b)
    (tagcase (k-get t)
      (ty-module (abs ds vs) t)
      (else z (k-fail (k-cat3 "`include` includes a module, and this is a " (k-show-ty t) "")
                      a b)))))
;; Abstract types `ns`, an included module's own now, onto `acc`'s, none
;; named there, nor in `own-abs` or `own-ds`, the module's own, nor in
;; `acc`'s types.
(define k-inc-abs (subr (maxeff checks spin) (k-parts k-incs k-parts k-parts int int) k-incs)
  (lambda (ns acc own-abs own-ds a b)
    (cond ((null? ns) acc)
          ((k-named-in? (extract (car ns) 1) (extract acc 4) own-abs (extract acc 1) own-ds)
           (k-twice (extract (car ns) 1) a b))
          (else (k-inc-abs (cdr ns)
                           (product (1 (extract acc 1)) (2 (extract acc 2)) (3 (extract acc 3))
                                    (4 (cons (car ns) (extract acc 4))) (5 (extract acc 5)))
                           own-abs own-ds a b)))))
;; Whether one of `p`, `q`, `r` and `s` names `n`.
(define k-named-in? (subr (read @globals) (symbol k-parts k-parts k-parts k-parts) bool)
  (lambda (n p q r s)
    (or (>= (k-ext-index p n 0) 0) (>= (k-ext-index q n 0) 0)
        (>= (k-ext-index r n 0) 0) (>= (k-ext-index s n 0) 0))))
;; `ds` onto `acc`'s types, none named there or in `own` but as the same
;; type (a types file's re-export: one name), nor an abstract type of
;; `own-abs`, the module's own, or of `acc`'s.
(define k-inc-descs
  (subr (maxeff checks spin) (k-parts k-incs k-parts k-saw int int) k-incs)
  (lambda (ds acc own-abs seen a b)
    (if (null? ds)
        acc
        (let* ((n (extract (car ds) 1)) (t (extract (car ds) 2))
               (prior (table-ref seen n -1))
               (same (and (>= prior 0)
                          (or (= (k-resolve prior) (k-resolve t))
                              (and (k-subtype prior t) (k-subtype t prior))))))
          (cond ((and (not (k-prefix? "%hidden" (symbol->string n)))
                      (or (and (>= prior 0) (not same))
                          (k-named-in? n own-abs (extract acc 4) nil nil)))
                 (k-twice n a b))
                (same (k-inc-descs (cdr ds) acc own-abs seen a b))
                (else (begin
                        (k-see seen n t)
                        (k-inc-descs (cdr ds)
                                     (k-incs-of (cons (car ds) (extract acc 1)) (extract acc 2)
                                                (extract acc 3) acc)
                                     own-abs seen a b))))))))
;; `n`, of type `t`, onto `seen`, unless there already.
(define k-see
  (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t)) (k-saw symbol int) unit)
  (lambda (seen n t) (if (table-has? seen n) #u (table-set! seen n t))))
;; Each of `ps` onto `seen`.
(define k-see-all
  (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t)) (k-saw k-parts) k-saw)
  (lambda (seen ps)
    (if (null? ps)
        seen
        (begin (k-see seen (extract (car ps) 1) (extract (car ps) 2))
               (k-see-all seen (cdr ps))))))
;; `vs`, from value `j` of the module that is value `k`, onto `acc`'s
;; values, none named there or in `own`.
(define k-inc-vals (subr (maxeff checks spin) (k-parts int int k-incs k-saw int int) k-incs)
  (lambda (vs k j acc seen a b)
    (cond ((null? vs) acc)
          ((table-has? seen (extract (car vs) 1)) (k-twice (extract (car vs) 1) a b))
          (else (begin
                  (table-set! seen (extract (car vs) 1) 0)
                  (k-inc-vals (cdr vs) k (+ j 1)
                              (k-incs-of (extract acc 1) (cons (car vs) (extract acc 2))
                                         (cons (pick-path k j) (extract acc 3)) acc)
                              seen a b))))))
;; Each of the modules `from`, the `k`th on, onto `acc`: its values from
;; value `at`, if not -1, else `k`; its abstract types a bound module's,
;; aliases, or the module's own (`k-abs-own`).
(define k-inc-all
  (subr (maxeff checks spin) (k-parts int int k-incs k-parts k-parts k-saw k-saw int int) k-incs)
  (lambda (from k at acc own-abs own-ds dseen vseen a b)
    (if (null? from)
        acc
        (tagcase (k-get (k-inc-module (extract (car from) 2) a b))
          (ty-module (ab ds vs)
            (let* ((o (k-abs-own ab))
                   (acc (k-inc-abs (extract o 1)
                                   (product (1 (extract acc 1)) (2 (extract acc 2))
                                            (3 (extract acc 3)) (4 (extract acc 4))
                                            (5 (append (extract acc 5) (extract o 2))))
                                   own-abs own-ds a b))
                   (ds (append (k-abs-aliases ab) ds))
                   (r (k-inc-vals vs (if (< at 0) k at) 0 (k-inc-descs ds acc own-abs dseen a b)
                                  vseen a b)))
              (k-inc-all (cdr from) (+ k 1) at
                         ;; A hidden `include`'s (`%hinclude-k`): each name marked
                         ;; hidden, for the module's type to leave out (`k-hiding`).
                         (if (k-prefix? "%hinclude-" (symbol->string (extract (car from) 1)))
                             (k-incs-of (k-hidden-marks
                                         "%hiddenv:" vs dseen
                                         (k-hidden-marks "%hidden:" ds dseen
                                                         (k-hidden-marks "%hidden:" (extract o 1)
                                                                         dseen (extract r 1))))
                                        (extract r 2) (extract r 3) r)
                             r)
                         own-abs own-ds dseen vseen a b)))
          (else z acc)))))
;; A `prefix`ed type for each of `ps`, onto `acc` (newest first): a type's
;; `%hidden:name`, a value's `%hiddenv:name`.
(define k-hidden-marks
  (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t)) (string k-parts k-saw k-parts)
        k-parts)
  (lambda (prefix ps seen acc)
    (if (null? ps)
        acc
        (let ((n (k-hidden-name prefix (extract (car ps) 1))))
          (begin (k-see seen n k-unit)
                 (k-hidden-marks prefix (cdr ps) seen
                                 (cons (product (1 n) (2 k-unit)) acc)))))))
(define k-hidden-name (subr (read @globals) (string symbol) symbol)
  (lambda (prefix n) (string->symbol (string-append prefix (symbol->string n)))))
;; The positions of a module's own values `own`, past `%include`'s, at `k`.
(define k-own-at (subr (maxeff (read @globals) (alloc @t)) (k-parts int int) k-picks)
  (lambda (own k i)
    (if (or (null? own) (< k 0))
        nil
        (cons (pick-value (if (< i k) i (+ i 1))) (k-own-at (cdr own) k (+ i 1))))))
;; `vs` but the `k`th, from `i`.
(define k-parts-but (subr (maxeff (read @globals) (alloc @t)) (k-parts int int) k-parts)
  (lambda (vs k i)
    (cond ((null? vs) nil)
          ((= i k) (cdr vs))
          (else (the k-parts (cons (car vs) (k-parts-but (cdr vs) k (+ i 1))))))))
;; The modules `from` included, their values and types with `abs`, `ds` and
;; `own`, the module's own: one bucket, a name given twice refused. Made of
;; theirs by path, from value `at` if it is a module's own `%include` (its
;; values then after it), else from each of `from`. As Rust's
;; `Checker::included`.
(define k-included
  (subr (maxeff checks spin) (k-parts k-parts k-parts k-parts int int int int) int)
  (lambda (from abs ds own at a b which)
    (let* ((dseen (k-see-all (make-table symbol-hash symbol=?) ds))
           (vseen (k-see-all (make-table symbol-hash symbol=?) own))
           (r (k-inc-all from 0 at (product (1 nil) (2 nil) (3 nil) (4 nil) (5 nil)) abs ds dseen
                         vseen a b))
           (m (extract r 5)))
      (begin
        (set k-reshapes (cons (product (1 (product (1 a) (2 b) (3 which)))
                                       (2 (append (reverse (extract r 3)) (k-own-at own at 0))))
                              (get k-reshapes)))
        ;; The included modules' own abstract types, then the module's.
        (k-ty-new (ty-module (append (reverse (extract r 4)) abs)
                             (k-subst-some (append (reverse (extract r 1)) ds) m)
                             (k-subst-some (append (reverse (extract r 2)) own) m)))))))
;; `ps` with `m` substituted, if it says anything.
(define k-subst-some (subr (maxeff kstate spin) (k-parts k-map) k-parts)
  (lambda (ps m) (if (null? m) ps (k-subst-each ps m))))

;;; ------------------------------------------------------------ hide

;; The names `(hide item …)` hid (`TODO.md` §69): each a `prefix`ed type
;; marks (types `%hidden:`, values `%hiddenv:`), in order.
(define k-hidden-in (subr (maxeff (read @globals) (alloc @t)) (k-parts string) k-names)
  (lambda (ds prefix)
    (cond ((null? ds) nil)
          ((k-prefix? prefix (symbol->string (extract (car ds) 1)))
           (cons (string->symbol (substring (symbol->string (extract (car ds) 1))
                                            (string-length prefix)
                                            (string-length (symbol->string (extract (car ds) 1)))))
                 (k-hidden-in (cdr ds) prefix)))
          (else (k-hidden-in (cdr ds) prefix)))))
;; Whether `n` is not among the names `hs` hides (a table: a module's
;; hidden includes hide thousands).
(define k-shown? (subr (maxeff (read @globals) (read @t)) (k-saw symbol) bool)
  (lambda (hs n) (not (table-has? hs n))))
;; `ns` as a table.
(define k-saw-of (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t)) (k-names) k-saw)
  (lambda (ns) (k-saw-all (make-table symbol-hash symbol=?) ns)))
(define k-saw-all
  (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t)) (k-saw k-names) k-saw)
  (lambda (t ns) (if (null? ns) t (begin (table-set! t (car ns) 0) (k-saw-all t (cdr ns))))))
;; `ps` but those hidden, and the markers.
(define k-parts-shown (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-parts k-saw) k-parts)
  (lambda (ps hs)
    (cond ((null? ps) nil)
          ((or (not (k-shown? hs (extract (car ps) 1)))
               (k-prefix? "%hidden" (symbol->string (extract (car ps) 1))))
           (k-parts-shown (cdr ps) hs))
          (else (the k-parts (cons (car ps) (k-parts-shown (cdr ps) hs)))))))
;; The positions `at` of the values of `vs` shown.
(define k-at-shown
  (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-parts k-picks k-saw) k-picks)
  (lambda (vs at hs)
    (cond ((null? vs) nil)
          ((k-shown? hs (extract (car vs) 1)) (cons (car at) (k-at-shown (cdr vs) (cdr at) hs)))
          (else (k-at-shown (cdr vs) (cdr at) hs)))))
;; Values `0`, … `n - 1` onto `acc`, from `n - 1` down.
(define k-upto (subr (maxeff (read @globals) (alloc @t)) (int k-picks) k-picks)
  (lambda (n acc) (if (<= n 0) acc (k-upto (- n 1) (cons (pick-value (- n 1)) acc)))))
;; Whether `at` is values `i`, … in order, to `n`.
(define k-identity? (subr (read @globals) (k-picks int int) bool)
  (lambda (at i n)
    (if (null? at)
        (= i n)
        (and (tagcase (car at) (pick-value (k) (= k i)) (else y #f))
             (k-identity? (cdr at) (+ i 1) n)))))
;; The first of `ps`, the parts shown, whose type mentions one of `gone`,
;; the abstract types hidden: refused (the user's, 2026-10-09).
(define k-hidden-escape (subr (maxeff checks spin) (k-parts k-parts int int) unit)
  (lambda (ps gone a b)
    (if (null? ps)
        #u
        (let ((v (k-first-mentioned (extract (car ps) 2) (k-part-ids gone))))
          (if (< v 0)
              (k-hidden-escape (cdr ps) gone a b)
              (k-fail (k-cat5 "`" (symbol->string (extract (car ps) 1)) "`'s type mentions `"
                              (symbol->string (k-part-named gone v))
                              "`, which is hidden in this module")
                      a b))))))
(define k-part-ids (subr (maxeff (read @globals) (alloc @t)) (k-parts) k-ids)
  (lambda (ps) (if (null? ps) nil (cons (extract (car ps) 2) (k-part-ids (cdr ps))))))
(define k-part-named (subr (read @globals) (k-parts int) symbol)
  (lambda (ps v)
    (cond ((null? ps) '?) ((= (extract (car ps) 2) v) (extract (car ps) 1))
          (else (k-part-named (cdr ps) v)))))
;; The abstract types of `abs` hidden (`gone?`) or not.
(define k-abs-split
  (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-parts k-saw bool) k-parts)
  (lambda (abs hs gone?)
    (cond ((null? abs) nil)
          ((eq? gone? (k-shown? hs (extract (car abs) 1))) (k-abs-split (cdr abs) hs gone?))
          (else (the k-parts (cons (car abs) (k-abs-split (cdr abs) hs gone?)))))))
;; Module type `t`, at `a`..`b`, the `which`th there, without what `(hide
;; item …)` hid: each name
;; a `%hidden:name` type marks, the markers too; made of the values left
;; by position (a reshape, on any it has). As Rust's `Checker::hiding`.
(define k-hiding (subr (maxeff checks spin) (int int int int) int)
  (lambda (t a b which)
    (tagcase (k-get t)
      (ty-module (abs ds vs)
        (let ((hs0 (k-hidden-in ds "%hidden:")) (hv0 (k-hidden-in ds "%hiddenv:")))
          (if (and (null? hs0) (null? hv0))
              t
              (let* ((hs (k-saw-of hs0)) (hv (k-saw-of hv0))
                     (rs (get k-reshapes))
                     (mine (and (not (null? rs)) (k-at-is? (extract (car rs) 1) a b which)))
                     (at (if mine (extract (car rs) 2) (k-upto (k-length vs) nil)))
                     (out (k-parts-shown vs hv))
                     (shown (k-parts-shown ds hs))
                     (gone (k-abs-split abs hs #t))
                     (checked (k-hidden-escape (append out shown) gone a b))
                     (path (k-at-shown vs at hv)))
                (begin
                  (if (k-identity? path 0 (k-length vs))
                      #u
                      (set k-reshapes (cons (product (1 (product (1 a) (2 b) (3 which))) (2 path))
                                            (if mine (cdr rs) rs))))
                  (k-ty-new (ty-module (k-abs-split abs hs #f) shown out)))))))
      (else z t))))

;; A module's type, the module `at`, of its abstract types, descriptions
;; and
;; values: an `extend`'s, of the two it holds (`k-extended`); an
;; `include`s', of the modules included; a module's that includes some, of
;; those and its own. As Rust's `Checker::module_type`.
(define k-module-type (subr (maxeff checks spin) (k-items k-parts k-parts k-parts k-at) int)
  (lambda (items abs ds vs at)
    (let ((k (k-ext-index vs '%include 0)) (a (extract at 1)) (b (extract at 2))
          (which (extract at 3)))
      (cond ((k-extend-items? items) (k-extended vs a b which))
            ((k-bucket-items? items) (k-included vs nil nil nil -1 a b which))
            ((>= k 0)
             (k-hiding (k-included (list (k-nth vs k)) abs ds (k-parts-but vs k 0) k a b which)
                       a b which))
            (else (k-hiding (k-ty-new (ty-module abs ds vs)) a b which))))))

;;; ------------------------------------------------------------ with

;; The names of parts `ps`.
(define k-comp-names (subr (maxeff (read @globals) (alloc @t)) (k-parts) k-names)
  (lambda (ps) (if (null? ps) nil (cons (extract (car ps) 1) (k-comp-names (cdr ps))))))
;; Each of `ps` bound, the first first.
(define k-bind-parts (subr (maxeff kstate spin) (k-parts) unit)
  (lambda (ps)
    (if (null? ps)
        #u
        (begin (k-bind (extract (car ps) 1) (extract (car ps) 2)) (k-bind-parts (cdr ps)))))))))
