;;; The checker, in FX-26: first-class modules' descriptions
;;; (`docs/research/first-class-modules.md`, stage M2): reading `moduleof`
;;; and `select`, and a `module`'s items; a module's type bound to a name,
;;; its abstract types named for that binding; `select`s resolved; what
;;; may not leave a binding's scope. The Rust checker's `modules.rs`, as it
;;; reads and resolves. Part of the checker, `check-types.fx` first.
;;;
;;; A module's type is an existential package: its abstract types are
;;; binders of its `moduleof`. A variable of that type has them renamed for
;;; itself as it is bound (`k-name-module`), each a type equal only to
;;; itself, named `m..t`; `(select m t)` is that type. Its rules, `module`
;;; and `with`, are `check-module-rules.fx`'s.

;;; ------------------------------------------------------------ reading

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-modules-types (load-module "fx26:check-modules-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-read-types (load-module "fx26:check-read-types.fx"))
       (check-holds-types (load-module "fx26:check-holds-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-kinds-types (load-module "fx26:check-kinds-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-read-descs-types (load-module "fx26:check-read-descs-types.fx"))
       (check-read-helpers-types (load-module "fx26:check-read-helpers-types.fx"))
       (reader-types (load-module "fx26:reader-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-env (select check-env-types check-env-sig))
           (check-kinds (select check-kinds-types check-kinds-sig))
           (check-print (select check-print-types check-print-sig))
           (check-read (select check-read-types check-read-sig))
           (check-holds (select check-holds-types check-holds-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (check-read-descs (select check-read-descs-types check-read-descs-sig))
           (parser (select reader-types parser-sig))
           (check-read-helpers (select check-read-helpers-types check-read-helpers-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module
(define-type k-rec-read (select check-modules-types k-rec-read))
(define-type k-thunk-unit (select check-modules-types k-thunk-unit))
(define-type k-renamed (select check-modules-types k-renamed))
;; The types it uses of the files before it.
(define a-var (with check-types-types a-var))
(define-effect checks (select check-types-types checks))
(define de (with check-types-types de))
(define df (with check-types-types df))
(define ds-rec (with check-types-types ds-rec))
(define dt (with check-types-types dt))
(define-type k-descs (select check-types-types k-descs))
(define-type k-eff (select check-types-types k-eff))
(define-type k-ids (select check-types-types k-ids))
(define-type k-map (select check-types-types k-map))
(define-type k-names (select check-types-types k-names))
(define-type k-parts (select check-types-types k-parts))
(define-effect kbuilds (select check-types-types kbuilds))
(define-effect kreads (select check-types-types kreads))
(define-effect kstate (select check-types-types kstate))
(define ty-app (with check-types-types ty-app))
(define ty-comp (with check-types-types ty-comp))
(define ty-lam (with check-types-types ty-lam))
(define ty-module (with check-types-types ty-module))
(define ty-named (with check-types-types ty-named))
(define ty-param (with check-types-types ty-param))
(define ty-select (with check-types-types ty-select))
(define ty-subr (with check-types-types ty-subr))
(define ty-tag (with check-types-types ty-tag))
(define ty-var (with check-types-types ty-var))
(define-type k-bindings (select check-env-types k-bindings))
(define-type k-scope (select check-env-types k-scope))
(define-type k-selects (select check-env-types k-selects))
(define-type k-effect-sels (select check-read-types k-effect-sels))
(define-type k-seen (select check-holds-types k-seen))
(define-type k-letrec-bs (select check-resolve-types k-letrec-bs))
(define-effect kmakes (select check-subst-types kmakes))
(define-type syn (select parser-types syn))
;; What it uses of the modules it is given.
(define k-abstract-funs (with check-types k-abstract-funs))
(define k-arrow-kind? (with check-types k-arrow-kind?))
(define k-arrow-params (with check-types k-arrow-params))
(define k-arrow-result (with check-types k-arrow-result))
(define k-cat3 (with check-types k-cat3))
(define k-cat4 (with check-types k-cat4))
(define k-cat5 (with check-types k-cat5))
(define k-dvar-kind (with check-types k-dvar-kind))
(define k-fail (with check-types k-fail))
(define k-get (with check-types k-get))
(define k-has-id? (with check-types k-has-id?))
(define k-has-name? (with check-types k-has-name?))
(define k-length (with check-types k-length))
(define k-new-dvar-of (with check-types k-new-dvar-of))
(define k-new-epoch (with check-types k-new-epoch))
(define k-quote (with check-types k-quote))
(define k-resolve (with check-types k-resolve))
(define k-set-link (with check-types k-set-link))
(define k-skolems (with check-types k-skolems))
(define k-ty-new (with check-types k-ty-new))
(define k-visit? (with check-types k-visit?))
(define k-fixed? (with check-env k-fixed?))
(define k-global? (with check-env k-global?))
(define k-lookup (with check-env k-lookup))
(define k-module-vars (with check-env k-module-vars))
(define k-select-map (with check-env k-select-map))
(define k-desc-of-kind? (with check-kinds k-desc-of-kind?))
(define k-dvar-string (with check-print-parts k-dvar-string))
(define k-kind-text (with check-print-parts k-kind-text))
(define k-map-find (with check-print-parts k-map-find))
(define k-show-ty (with check-print k-show-ty))
(define k-effect-selects (with check-read k-effect-selects))
(define k-keep-at (with check-read k-keep-at))
(define k-keep-set! (with check-read k-keep-set!))
(define k-subst-keep (with check-read k-subst-keep))
(define k-fun-kind (with check-holds k-fun-kind))
(define k-new-seen (with check-holds k-new-seen))
(define k-seen? (with check-holds k-seen?))
(define k-new-smemo (with check-subst k-new-smemo))
(define k-subst (with check-subst k-subst))
(define k-subst-memo (with check-subst k-subst-memo))
(define k-selects-in (with check-read-descs k-selects-in))
(define k-ty-kids (with check-read-helpers k-ty-kids))
(define syn-end (with parser syn-end))
(define syn-start (with parser syn-start))

;;; ------------------------------------------------------------ walking types

;; Descriptions `ds`, the `i`th on, each of the kind of `ks` it is given for.
;; Function `f`, as an error says it: its type, quoted. Printed only for an
;; error, as printing a type is not cheap.
(define k-fun-shown (subr kbuilds (int) string) (lambda (f) (k-quote (k-show-ty f))))
(define k-check-app-args (subr (maxeff checks spin) (int k-descs k-ids int int int) unit)
  (lambda (f ds ks i a b)
    (cond ((null? ds) #u)
          ((not (k-desc-of-kind? (car ds) (car ks)))
           (k-fail (k-cat5 (k-fun-shown f) " takes a " (k-kind-text (car ks)) " as description "
                           (int->string i))
                   a b))
          (else (k-check-app-args f (cdr ds) (cdr ks) (+ i 1) a b)))))
;; Function `f` applied to `ds`, at `a`..`b`: given as many descriptions as
;; it takes, each of the kind it takes, and giving a type.
(define k-check-app (subr (maxeff checks spin) (int k-descs int int) unit)
  (lambda (f ds a b)
    (let ((k (k-fun-kind f)))
      (cond ((< k 0) #u)
            ((not (k-arrow-kind? k))
             (k-fail (string-append (k-fun-shown f) " is not a description function: it is applied")
                     a b))
            ((not (= (k-length (k-arrow-params k)) (k-length ds)))
             (k-fail (k-cat5 (k-fun-shown f) " takes " (int->string (k-length (k-arrow-params k)))
                             " description(s), and has " (int->string (k-length ds)))
                     a b))
            ((not (or (= (k-arrow-result k) 2) (= (k-arrow-result k) 4)))
             (k-fail (k-cat4 (k-fun-shown f) " gives a description of kind "
                             (k-kind-text (k-arrow-result k)) ", not a type")
                     a b))
            (else (k-check-app-args f ds (k-arrow-params k) 1 a b))))))
;; Each description function applied in `t` given what it takes, at
;; `a`..`b`: checked where a `select` has just said what the function is.
(define-rec
  (k-check-apps-from (subr (maxeff checks spin) (int k-seen int int) unit)
    (lambda (t seen a b)
      (let ((t (k-resolve t)))
        (if (k-seen? seen t)
            #u
            (begin
              (tagcase (k-get t) (ty-app (f ds) (k-check-app f ds a b)) (else y #u))
              (k-check-apps-each (k-ty-kids t) seen a b))))))
  (k-check-apps-each (subr (maxeff checks spin) (k-ids k-seen int int) unit)
    (lambda (ts seen a b)
      (if (null? ts)
          #u
          (begin (k-check-apps-from (car ts) seen a b) (k-check-apps-each (cdr ts) seen a b))))))
(define k-check-apps (subr (maxeff checks spin) (int int int) unit)
  (lambda (t a b) (k-check-apps-from t (k-new-seen) a b)))
;; Whether type variable `v` is somewhere in `t`, or in `ts`; `seen`, the
;; nodes walked.
(define-rec
  (k-mentions-from? (subr (maxeff kstate spin) (int int (ref k-ids @t)) bool)
    (lambda (t v seen)
      (let ((t (k-resolve t)))
        (if (k-has-id? (get seen) t)
            #f
            (begin
              (set seen (cons t (get seen)))
              (or (tagcase (k-get t) (ty-var (w) (= w v)) (else y #f))
                  (k-any-mentions? (k-ty-kids t) v seen)))))))
  (k-any-mentions? (subr (maxeff kstate spin) (k-ids int (ref k-ids @t)) bool)
    (lambda (ts v seen)
      (and (not (null? ts))
           (or (k-mentions-from? (car ts) v seen) (k-any-mentions? (cdr ts) v seen))))))
(define k-mentions-var? (subr (maxeff kstate spin) (int int) bool)
  (lambda (t v) (k-mentions-from? t v (the (ref k-ids @t) (new nil)))))
;; The first of `vs` that `t` mentions, or -1.
(define k-first-mentioned (subr (maxeff kstate spin) (int k-ids) int)
  (lambda (t vs)
    (cond ((null? vs) -1)
          ((k-mentions-var? t (car vs)) (car vs))
          (else (k-first-mentioned t (cdr vs))))))

;;; ------------------------------------------------------------ naming

;; Whether `v` was made for a module's abstract type as it was bound.
(define k-module-var? (subr kreads (int) bool)
  (lambda (v) (k-has-id? (get k-module-vars) v)))
(define k-rename-abs (subr (maxeff kstate spin) (string k-parts) k-renamed)
  (lambda (prefix abs)
    (if (null? abs)
        (product (1 (the k-parts nil)) (2 (the k-map nil)))
        (let* ((a (extract (car abs) 1))
               (k (k-dvar-kind (extract (car abs) 2)))
               (w (k-new-dvar-of (string->symbol (string-append prefix (symbol->string a))) k))
               (noted (begin (set k-skolems (cons w (get k-skolems)))
                             (set k-module-vars (cons w (get k-module-vars)))
                             (if (= k 2) #u (set k-abstract-funs (cons w (get k-abstract-funs))))))
               (to (if (= k 2) (dt (k-ty-new (ty-var w))) (df (k-ty-new (ty-var w)))))
               (rest (k-rename-abs prefix (cdr abs))))
          (product (1 (the k-parts (cons (product (1 a) (2 w)) (extract rest 1))))
                   (2 (the k-map (cons (cons (extract (car abs) 2) to) (extract rest 2)))))))))
;; Parts `ps`, each type with `m` for its binders.
(define k-subst-each (subr (maxeff kstate spin) (k-parts k-map) k-parts)
  (lambda (ps m)
    (if (null? ps)
        nil
        (let* ((t (k-subst (extract (car ps) 2) m)) (rest (k-subst-each (cdr ps) m)))
          (cons (product (1 (extract (car ps) 1)) (2 t)) rest)))))
;; A module's type, bound to `name`: its abstract types renamed for this
;; binding, each `name..t`, kept until the binding's scope ends. Any other
;; type as it is.
(define k-name-module (subr (maxeff kstate spin) (symbol int) int)
  (lambda (name t)
    (tagcase (k-get (k-resolve t))
      (ty-module (abs ds vs)
        (if (null? abs)
            t
            (let* ((r (k-rename-abs (string-append (symbol->string name) "..") abs))
                   (ds2 (k-subst-each ds (extract r 2)))
                   (vs2 (k-subst-each vs (extract r 2))))
              (k-ty-new (ty-module (extract r 1) ds2 vs2)))))
      (else y t))))
;; Of the sizes and abstract types `vs`, named in a scope that `t` leaves:
;; the sizes, to be forgotten. A module's abstract type cannot be: nothing
;; may leave its binding's scope still mentioning it.
(define k-sizes-of (subr (maxeff kreads (alloc @t)) (k-ids) k-ids)
  (lambda (vs)
    (cond ((null? vs) nil)
          ((k-module-var? (car vs)) (k-sizes-of (cdr vs)))
          (else (cons (car vs) (k-sizes-of (cdr vs)))))))
(define k-escaping (subr (maxeff kstate spin) (int k-ids) int)
  (lambda (t vs)
    (cond ((null? vs) -1)
          ((and (k-module-var? (car vs)) (k-mentions-var? t (car vs))) (car vs))
          (else (k-escaping t (cdr vs))))))
(define k-unescaped (subr (maxeff checks spin) (int k-ids int int) k-ids)
  (lambda (t vs a b)
    (let ((v (k-escaping t vs)))
      (if (< v 0)
          (k-sizes-of vs)
          (k-fail (k-cat5 "this is a " (k-show-ty t) ", and `" (k-dvar-string v)
                          (string-append "` is a module's abstract type, not known outside "
                                         "the scope where the module is named"))
                  a b)))))

;;; ------------------------------------------------------------ select

;; Each `(select m n)` node in `t`, onto `out` (newest first); the
;; nodes walked, `seen`.
;; `(select m n)`, as an error shows it.
(define k-select-shown (subr (read @globals) (symbol symbol) string)
  (lambda (m n) (k-cat5 "`(select " (symbol->string m) " " (symbol->string n) ")`")))
;; The type component `n` of parts `ps`, or -1.
(define k-comp-find (subr kreads (k-parts symbol) int)
  (lambda (ps n)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) n) (extract (car ps) 2))
          (else (k-comp-find (cdr ps) n)))))
;; What `(select m n)` is, `m` a module bound to a type of abstract types
;; `abs` and descriptions `ds`: its abstract type `n`, or its description;
;; an error at `a`..`b` if it has neither.
(define k-select-component (subr (maxeff checks spin) (symbol symbol k-parts k-parts int int) int)
  (lambda (m n abs ds a b)
    (let ((v (k-comp-find abs n)) (d (k-comp-find ds n)))
      (cond ((>= v 0) (k-ty-new (ty-var v)))
            ((>= d 0) d)
            (else (k-fail (k-cat5 (k-select-shown m n) ": `" (symbol->string m) "` has no type `"
                                  (string-append (symbol->string n) "`"))
                          a b))))))
;; What an error about `(select m n)` starts with; made only for an error.
(define k-select-prefix (subr (read @globals) (symbol symbol) string)
  (lambda (m n) (k-cat3 (k-select-shown m n) ": `" (symbol->string m))))
;; A global module's type, as `select` node `node` names it: that node from
;; now on, linked to `to`, so that whatever leads to it is not rebuilt, and
;; is shared, and shown by its name. Not a family, which is read as the
;; `select` it is; nor a local module's, which may differ by scope.
(define k-link-global-select (subr (maxeff kstate spin) (symbol int int) unit)
  (lambda (m node to)
    (if (and (or (k-global? m) (k-fixed? m))
             (tagcase (k-get to)
               (ty-lam (bs d) #f)
               (ty-var (v) (= (k-dvar-kind v) 2))
               (else y #t)))
        (k-set-link node to)
        #u)))
;; Module `m`'s component `n`, as select node `node` names it, linked.
(define k-link-alias (subr (maxeff kstate spin) (symbol symbol int) unit)
  (lambda (m n node)
    (let ((mt (k-lookup m)))
      (if (< mt 0)
          #u
          (tagcase (k-get mt)
            (ty-module (abs ds vs)
              (let ((v (k-comp-find abs n)) (d (k-comp-find ds n)))
                (cond ((>= v 0) (k-link-global-select m node (k-ty-new (ty-var v))))
                      ((>= d 0) (k-link-global-select m node d))
                      (else #u))))
            (else y #u))))))
;; Each `define-type` alias in `ds`, `(define-type t (select m t))`, of the
;; global module `m` just bound, linked now to what it names: the aliases are
;; declared ahead of `m`, and a type naming one shows by its name from the
;; first, not once some later resolution meets it. As the Rust checker's
;; `link_aliases`.
(define k-link-aliases (subr (maxeff kstate spin) (symbol k-scope) unit)
  (lambda (m ds)
    (if (null? ds)
        #u
        (begin
          (tagcase (cdr (car ds))
            (ds-rec (t)
              (tagcase (k-get t)
                (ty-select (x n) (if (symbol=? x m) (k-link-alias m n (k-resolve t)) #u))
                (else y #u)))
            (else z #u))
          (k-link-aliases m (cdr ds))))))
;; What each of `found` is where it is checked, at `a`..`b`.
(define k-selection (subr (maxeff checks spin) (k-selects int int) k-selects)
  (lambda (found a b)
    (if (null? found)
        nil
        (let* ((m (extract (car found) 1)) (n (extract (car found) 2))
               (mt (k-lookup m))
               (to (if (< mt 0)
                       (k-fail (string-append (k-select-prefix m n) "` is not bound here") a b)
                       (tagcase (k-get mt)
                         (ty-module (abs ds vs) (k-select-component m n abs ds a b))
                         (else y (k-fail (k-cat4 (k-select-prefix m n) "` is a " (k-show-ty mt)
                                                 ", not a module")
                                         a b)))))
               (linked (k-link-global-select m (extract (car found) 3) to))
               (rest (k-selection (cdr found) a b)))
          (cons (product (1 m) (2 n) (3 to)) rest)))))
;;; ------------------------------------------------------------ effects selected

;; The entry of `ss` for variable `v`, or none.
(define k-effect-sel-var (subr (maxeff (read @globals) (read @t)) (k-effect-sels int) k-effect-sels)
  (lambda (ss v)
    (cond ((null? ss) nil)
          ((= (extract (car ss) 3) v) ss)
          (else (k-effect-sel-var (cdr ss) v)))))
;; `e`'s effect variables that stand for `(select m e)`s, onto `out`, each
;; once.
(define k-esels-note (subr (maxeff kstate spin) (k-eff (ref k-effect-sels @t)) unit)
  (lambda (e out)
    (if (null? e)
        #u
        (begin
          (tagcase (car e)
            (a-var (v)
              (let ((sel (k-effect-sel-var (get k-effect-selects) v)))
                (if (or (null? sel) (not (null? (k-effect-sel-var (get out) v))))
                    #u
                    (set out (cons (car sel) (get out))))))
            (else y #u))
          (k-esels-note (cdr e) out)))))
;; The effects of descriptions `ds`, noted.
(define k-esels-descs (subr (maxeff kstate spin) (k-descs (ref k-effect-sels @t)) unit)
  (lambda (ds out)
    (if (null? ds)
        #u
        (begin (tagcase (car ds) (de (e) (k-esels-note e out)) (else x #u))
               (k-esels-descs (cdr ds) out)))))
;; Each effect `(select m e)` in `t`, onto `out`; the nodes walked, `seen`.
(define-rec
  (k-esels-from (subr (maxeff kstate spin) (int k-seen (ref k-effect-sels @t)) unit)
    (lambda (t seen out)
      (let ((t (k-resolve t)))
        (if (k-seen? seen t)
            #u
            (begin
              (tagcase (k-get t)
                (ty-subr (e ps r cv) (k-esels-note e out))
                (ty-tag (a h e r) (k-esels-note e out))
                (ty-comp (a h e r) (k-esels-note e out))
                (ty-lam (bs d) (k-esels-descs (the k-descs (list d)) out))
                (ty-app (f ds) (k-esels-descs ds out))
                (ty-named (g ds) (k-esels-descs ds out))
                (else y #u))
              (k-esels-each (k-ty-kids t) seen out))))))
  (k-esels-each (subr (maxeff kstate spin) (k-ids k-seen (ref k-effect-sels @t)) unit)
    (lambda (ts seen out)
      (if (null? ts)
          #u
          (begin (k-esels-from (car ts) seen out) (k-esels-each (cdr ts) seen out))))))
;; The effect `(select m e)`s in `t`, in the order met.
(define k-effect-selects-in (subr (maxeff kstate spin) (int) k-effect-sels)
  (lambda (t)
    (if (null? (get k-effect-selects))
        nil
        (let ((out (the (ref k-effect-sels @t) (new nil))))
          (begin (k-esels-from t (k-new-seen) out) (reverse (get out)))))))
;; The effect a module's description `d` is, in a list; none if not one.
(define k-desc-effect (subr (maxeff kreads spin) (int) (listof k-eff acyclic))
  (lambda (d)
    (tagcase (k-get d)
      (ty-lam (bs body)
        (if (null? bs)
            (tagcase body
              (de (e) (the (listof k-eff acyclic) (list e)))
              (else x (the (listof k-eff acyclic) nil)))
            (the (listof k-eff acyclic) nil)))
      (else y (the (listof k-eff acyclic) nil)))))
;; Module `m`'s effect `e`, as its type says, `m` bound here; or an error
;; at `a`..`b`.
(define k-selected-effect (subr (maxeff checks spin) (symbol symbol int int) k-eff)
  (lambda (m e a b)
    (let ((mt (k-lookup m)))
      (if (< mt 0)
          (begin (k-fail (string-append (k-select-prefix m e) "` is not bound here") a b)
                 (the k-eff nil))
          (tagcase (k-get mt)
            (ty-module (abs ds vs)
              (let* ((d (k-comp-find ds e))
                     (x (if (< d 0) (the (listof k-eff acyclic) nil) (k-desc-effect d))))
                (if (null? x)
                    (let ((msg (k-cat4 (k-select-prefix m e) "` has no effect `"
                                       (symbol->string e) "`")))
                      (begin (k-fail msg a b) (the k-eff nil)))
                    (car x))))
            (else y (begin (k-fail (k-cat4 (k-select-prefix m e) "` is a " (k-show-ty mt)
                                           ", not a module")
                                   a b)
                           (the k-eff nil))))))))
;; What each effect selected stands for, as a substitution.
(define k-effects-given (subr (maxeff checks spin) (k-effect-sels int int) k-map)
  (lambda (ss a b)
    (if (null? ss)
        nil
        (let* ((x (car ss)) (e (k-selected-effect (extract x 1) (extract x 2) a b))
               (rest (k-effects-given (cdr ss) a b)))
          (the k-map (cons (cons (extract x 3) (de e)) rest))))))
;; Whether `e` names a variable `given` replaces.
(define k-eff-given? (subr (maxeff kreads spin) (k-eff k-map) bool)
  (lambda (e given)
    (and (not (null? e))
         (or (tagcase (car e) (a-var (v) (not (null? (k-map-find given v)))) (else y #f))
             (k-eff-given? (cdr e) given)))))
(define k-descs-given? (subr (maxeff kreads spin) (k-descs k-map) bool)
  (lambda (ds given)
    (and (not (null? ds))
         (or (tagcase (car ds) (de (e) (k-eff-given? e given)) (else x #f))
             (k-descs-given? (cdr ds) given)))))
;; Whether node `n` is itself what a `select`'s resolution changes: a
;; `select`, a `(select $k t)`, or an effect naming a variable `given`
;; replaces.
(define k-select-seed? (subr (maxeff kreads spin) (int k-map) bool)
  (lambda (n given)
    (tagcase (k-get n)
      (ty-select (m s) #t)
      (ty-param (k s) #t)
      (ty-subr (e ps r cv) (k-eff-given? e given))
      (ty-tag (a h e r) (k-eff-given? e given))
      (ty-comp (a h e r) (k-eff-given? e given))
      (ty-lam (bs d) (k-descs-given? (the k-descs (list d)) given))
      (ty-app (f ds) (k-descs-given? ds given))
      (ty-named (g ds) (k-descs-given? ds given))
      (else y #f))))
;; The nodes reached from `t`, through `k-ty-kids`, onto `out`; `e` the walk.
(define-rec
  (k-nodes-from (subr (maxeff kstate spin) (int int (ref k-ids @t)) unit)
    (lambda (t e out)
      (let ((t (k-resolve t)))
        (if (k-visit? t e)
            #u
            (begin (set out (cons t (get out))) (k-nodes-each (k-ty-kids t) e out))))))
  (k-nodes-each (subr (maxeff kstate spin) (k-ids int (ref k-ids @t)) unit)
    (lambda (ts e out)
      (if (null? ts) #u (begin (k-nodes-from (car ts) e out) (k-nodes-each (cdr ts) e out))))))
;; Whether a child of `n` is marked `d`.
(define k-kid-marked? (subr (maxeff kstate spin) (k-ids int) bool)
  (lambda (ks d)
    (and (not (null? ks)) (or (= (k-keep-at (k-resolve (car ks))) d) (k-kid-marked? (cdr ks) d)))))
;; Each of `ns` not marked `d` with a child that is, marked `d`: whether any.
(define k-mark-parents (subr (maxeff kstate spin) (k-ids int bool) bool)
  (lambda (ns d changed)
    (cond ((null? ns) changed)
          ((and (not (= (k-keep-at (car ns)) d)) (k-kid-marked? (k-ty-kids (car ns)) d))
           (begin (k-keep-set! (car ns) d) (k-mark-parents (cdr ns) d #t)))
          (else (k-mark-parents (cdr ns) d changed)))))
(define k-mark-until-still (subr (maxeff kstate spin) (k-ids int) unit)
  (lambda (ns d) (if (k-mark-parents ns d #f) (k-mark-until-still ns d) #u)))
;; Each of `ns` that is itself what resolving changes (`k-select-seed?`),
;; marked `d`.
(define k-mark-seeds (subr (maxeff kstate spin) (k-ids k-map int) unit)
  (lambda (ns given d)
    (if (null? ns)
        #u
        (begin (if (k-select-seed? (car ns) given) (k-keep-set! (car ns) d) #u)
               (k-mark-seeds (cdr ns) given d)))))
(define k-mark-kept (subr (maxeff kstate spin) (k-ids int int) unit)
  (lambda (ns d k)
    (if (null? ns)
        #u
        (begin (if (= (k-keep-at (car ns)) d) #u (k-keep-set! (car ns) k))
               (k-mark-kept (cdr ns) d k)))))
;; The nodes of `t` from which no `select` is reached, marked kept: the
;; epoch they are marked with. As the Rust checker's `select_clean`.
(define k-select-clean (subr (maxeff kstate spin) (int k-map) int)
  (lambda (t given)
    (let* ((out (the (ref k-ids @t) (new nil)))
           (walked (k-nodes-from t (k-new-epoch) out))
           (ns (get out))
           (d (k-new-epoch))
           (seeded (k-mark-seeds ns given d))
           (spread (k-mark-until-still ns d))
           (k (k-new-epoch)))
      (begin (k-mark-kept ns d k) k))))
;; `t` with each `(select m n)` in it replaced by what it is: `m`'s
;; abstract type `n`, as `m` was bound, or its description `n`. An error
;; at `a`..`b` if one is not.
(define k-resolve-selects (subr (maxeff checks spin) (int int int) int)
  (lambda (t a b)
    (let ((found (k-selects-in t)) (efound (k-effect-selects-in t)))
      (if (and (null? found) (null? efound))
          t
          (let ((given (k-effects-given efound a b)) (outer (get k-select-map)))
            (begin
              (set k-select-map (k-selection found a b))
              ;; Only what leads to a `select` is rebuilt; the rest stays
              ;; itself.
              (let* ((outer-keep (get k-subst-keep))
                     (kept (set k-subst-keep (k-select-clean t given)))
                     (r (k-subst-memo t given (k-new-smemo))))
                (begin (set k-subst-keep outer-keep)
                       (set k-select-map outer)
                       (k-check-apps r a b)
                       r))))))))
;; The same for a type written as `s`, at `s`.
(define k-select-syn (subr (maxeff checks spin) (int syn) int)
  (lambda (t s) (k-resolve-selects t (syn-start s) (syn-end s))))
;; The same for the types a `letrec`'s bindings `bs` are declared, at the
;; `letrec`, `a`..`b`.
(define k-letrec-selected (subr (maxeff checks spin) (k-letrec-bs int int) k-letrec-bs)
  (lambda (bs a b)
    (if (null? bs)
        nil
        (let* ((x (car bs))
               (t (k-resolve-selects (extract x 2) a b))
               (rest (k-letrec-selected (cdr bs) a b)))
          (cons (product (1 (extract x 1)) (2 t) (3 (extract x 3))) rest)))))
;; The first `select` of `found` from one of `params`, or none.
(define k-select-from (subr kreads (k-selects k-names) k-selects)
  (lambda (found params)
    (cond ((null? found) nil)
          ((k-has-name? params (extract (car found) 1)) (cons (car found) nil))
          (else (k-select-from (cdr found) params)))))
;; `t` resolved, at `a`..`b`, where `params` are not yet bound, and so may
;; not be selected from: one that names the parameter it is the type of, or
;; a later one.
(define k-resolve-outside (subr (maxeff checks spin) (int k-names int int) int)
  (lambda (t params a b)
    (let ((dependent (k-select-from (k-selects-in t) params)))
      (if (null? dependent)
          (k-resolve-selects t a b)
          (let ((s (car dependent)))
            (k-fail (string-append
                     (k-select-shown (extract s 1) (extract s 2))
                     (string-append " names a parameter of the same `lambda`: "
                                    "a dependent type, not supported yet"))
                    a b))))))
(define k-binding-names (subr kmakes (k-bindings) k-names)
  (lambda (bs) (if (null? bs) nil (cons (car (car bs)) (k-binding-names (cdr bs)))))))))
