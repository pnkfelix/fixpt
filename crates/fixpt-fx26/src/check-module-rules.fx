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
(define-type k-say (select check-module-rules-types k-say))
(define-type k-made (select check-module-rules-types k-made))
(define-type k-mod-bound (select check-module-rules-types k-mod-bound))
(define-type k-ends (select check-module-rules-types k-ends))
(define-type k-eff-ty (select check-module-rules-types k-eff-ty))
(define-type k-mod-checked (select check-module-rules-types k-mod-checked))
;; The types it uses of the files before it.
(define a-read (with check-types-types a-read))
(define-effect checks (select check-types-types checks))
(define-type k-eff (select check-types-types k-eff))
(define k-err (with check-types-types k-err))
(define-type k-ids (select check-types-types k-ids))
(define-type k-item (select check-types-types k-item))
(define-type k-names (select check-types-types k-names))
(define k-ok (with check-types-types k-ok))
(define-type k-parts (select check-types-types k-parts))
(define-type k-te (select check-types-types k-te))
(define-effect kbuilds (select check-types-types kbuilds))
(define-effect kreads (select check-types-types kreads))
(define-effect kstate (select check-types-types kstate))
(define r-globals (with check-types-types r-globals))
(define ty-module (with check-types-types ty-module))
(define k-done (with check-types-types k-done))
(define-type k-items (select check-types-types k-items))
(define-type k-hazard-list (select check-env-types k-hazard-list))
(define-type k-done (select check-synth-types k-done))
(define-type k-mlam (select check-modorder-types k-mlam))
(define-type k-mlams (select check-modorder-types k-mlams))
(define-type k-letrec-bs (select check-resolve-types k-letrec-bs))
(define-type k-thunk (select check-terminate-types k-thunk))
(define-type k-saying (select check-subtype-types k-saying))
;; What it uses of the modules it is given.
(define k-cat3 (with check-types k-cat3))
(define k-cat5 (with check-types k-cat5))
(define k-fail (with check-types k-fail))
(define k-get (with check-types k-get))
(define k-has-name? (with check-types k-has-name?))
(define k-resolve (with check-types k-resolve))
(define k-tag (with check-types k-tag))
(define k-te (with check-types k-te))
(define k-bind (with check-env k-bind))
(define k-env (with check-env k-env))
(define k-note-fixed (with check-env k-note-fixed))
(define k-note-known (with check-env k-note-known))
(define k-dvar-string (with check-print-parts k-dvar-string))
(define k-show-ty (with check-print k-show-ty))
(define k-fail-at (with check-errors k-fail-at))
(define k-first-mentioned (with check-modules k-first-mentioned))
(define k-resolve-selects (with check-modules k-resolve-selects))
(define k-items (with check-read k-items))
(define k-lambda-item? (with check-modorder k-lambda-item?))
(define k-name-nat (with check-expect k-name-nat))
(define k-one (with check-effects k-one))
(define k-part-of (with check-subtype k-part-of))
(define k-part-onto (with check-read-helpers k-part-onto))
(define k-termination (with check-terminate k-termination))
(define k-with-latent (with check-letrec k-with-latent))
(define table-ref (with tables table-ref))
(define table-set! (with tables table-set!))
(define k-ty-new (with check-types k-ty-new))
(define k-nth (with check-types k-nth))
(define k-reshapes (with check-env k-reshapes))

;; `n`'s innermost binding, now of type `t`.
(define k-rebind-top (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (n t) (table-set! (get k-env) n (cons t (cdr (table-ref (get k-env) n nil))))))
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
(define k-star-mistake (subr (maxeff kreads (alloc @t) spin) (symbol int string) string)
  (lambda (name tf m)
    (k-cat5 (k-cat3 "`define*` found `" (symbol->string name) "` to be a ") (k-show-ty tf)
            ": " m "")))

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
;; Value `j` of the module that is value `k`, as a reshape's position (Rust
;; `reshape_path`): a path, from 2^40 on.
(define k-reshape-path (subr pure (int int) int)
  (lambda (k j) (+ 1099511627776 (+ (* k 1048576) j))))
;; One side of an `extend`, of type `t`: a module with no abstract types of
;; its own, or an error.
(define k-extend-side (subr (maxeff checks spin) (int string int int) int)
  (lambda (t which a b)
    (tagcase (k-get t)
      (ty-module (abs ds vs)
        (if (null? abs)
            t
            (k-fail (k-cat3 "`extend` of a module with abstract types"
                            " of its own is not supported" " yet")
                    a b)))
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
(define k-ext-firsts-at (subr (maxeff (read @globals) (alloc @t)) (k-parts k-parts int) k-ids)
  (lambda (p0 p1 j)
    (if (null? p0)
        nil
        (let ((k (k-ext-index p1 (extract (car p0) 1) 0)))
          (cons (if (< k 0) (k-reshape-path 0 j) (k-reshape-path 1 k))
                (k-ext-firsts-at (cdr p0) p1 (+ j 1)))))))
(define k-ext-rest-at (subr (maxeff (read @globals) (alloc @t)) (k-parts k-parts int) k-ids)
  (lambda (p1 p0 k)
    (cond ((null? p1) nil)
          ((>= (k-ext-index p0 (extract (car p1) 1) 0) 0) (k-ext-rest-at (cdr p1) p0 (+ k 1)))
          (else (cons (k-reshape-path 1 k) (k-ext-rest-at (cdr p1) p0 (+ k 1)))))))
;; `(extend e0 e1)` at `a`..`b`, its values `vs` the two modules: one of the
;; values of both, `e1`'s where both have a name, `e0`'s in its order first
;; and then `e1`'s others; its types likewise. Made of theirs, by path
;; (`k-reshape-path`, noted in `k-reshapes`). As Rust's `Checker::extended`.
(define k-extended (subr (maxeff checks spin) (k-parts int int) int)
  (lambda (vs a b)
    (let ((t0 (k-extend-side (extract (car vs) 2) "first" a b))
          (t1 (k-extend-side (extract (car (cdr vs)) 2) "second" a b)))
      (tagcase (k-get t0)
        (ty-module (a0 d0 v0)
          (tagcase (k-get t1)
            (ty-module (a1 d1 v1)
              (let ((at (append (k-ext-firsts-at v0 v1 0) (k-ext-rest-at v1 v0 0))))
                (begin (set k-reshapes (cons (product (1 a) (2 b) (3 at)) (get k-reshapes)))
                       (k-ty-new (ty-module nil (append (k-ext-firsts d0 d1) (k-ext-rest d1 d0))
                                            (append (k-ext-firsts v0 v1) (k-ext-rest v1 v0)))))))
            (else z t1)))
        (else z t0)))))

;; A module's type, at `a`..`b`, of its abstract types, descriptions and
;; values: an `extend`'s, of the two it holds (`k-extended`).
(define k-module-type (subr (maxeff checks spin) (k-items k-parts k-parts k-parts int int) int)
  (lambda (items abs ds vs a b)
    (if (k-extend-items? items) (k-extended vs a b) (k-ty-new (ty-module abs ds vs)))))

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
