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
(hide (include check-modules-types) (include check-types-types) (include check-env-types)
      (include check-read-types) (include check-holds-types) (include check-resolve-types)
      (include check-subst-types) (include parser-types))
;; The types it uses of the files before it.
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-env) (include check-kinds) (include check-print-parts)
      (include check-print) (include check-holds) (include check-subst) (include check-read-descs)
      (include check-read-helpers) (include parser))
(import check-read k-effect-selects k-with-effect-fall k-union k-one k-keep-at k-keep-set!
        k-subst-keep)

;;; ------------------------------------------------------------ walking types

;; Descriptions `ds`, the `i`th on, each of the kind of `ks` it is given for.
;; Function `f`, as an error says it: its type, quoted. Printed only for an
;; error, as printing a type is not cheap.
(define k-fun-shown (->* (int) string) (lambda (f) (k-quote (k-show-ty f))))
(define k-check-app-args (->* (int k-descs k-ids int int int) unit)
  (lambda (f ds ks i a b)
    (cond ((null? ds) #u)
          ((not (k-desc-of-kind? (car ds) (car ks)))
           (k-fail (k-cat5 (k-fun-shown f) " takes a " (k-kind-text (car ks)) " as description "
                           (int->string i))
                   a b))
          (else (k-check-app-args f (cdr ds) (cdr ks) (+ i 1) a b)))))
;; Function `f` applied to `ds`, at `a`..`b`: given as many descriptions as
;; it takes, each of the kind it takes, and giving a type.
(define k-check-app (->* (int k-descs int int) unit)
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
  (k-check-apps-from (->* (int k-seen int int) unit)
    (lambda (t seen a b)
      (let ((t (k-resolve t)))
        (if (k-seen? seen t)
            #u
            (begin
              (tagcase (k-get t) (ty-app (f ds) (k-check-app f ds a b)) (else y #u))
              (k-check-apps-each (k-ty-kids t) seen a b))))))
  (k-check-apps-each (->* (k-ids k-seen int int) unit)
    (lambda (ts seen a b)
      (if (null? ts)
          #u
          (begin (k-check-apps-from (car ts) seen a b) (k-check-apps-each (cdr ts) seen a b))))))
(define k-check-apps (->* (int int int) unit)
  (lambda (t a b) (k-check-apps-from t (k-new-seen) a b)))
;; Whether type variable `v` is somewhere in `t`, or in `ts`; `seen`, the
;; nodes walked.
(define-rec
  (k-mentions-from? (->* (int int (ref k-ids @t)) bool)
    (lambda (t v seen)
      (let ((t (k-resolve t)))
        (if (k-has-id? (get seen) t)
            #f
            (begin
              (set seen (cons t (get seen)))
              (or (tagcase (k-get t) (ty-var (w) (= w v)) (else y #f))
                  (k-any-mentions? (k-ty-kids t) v seen)))))))
  (k-any-mentions? (->* (k-ids int (ref k-ids @t)) bool)
    (lambda (ts v seen)
      (and (not (null? ts))
           (or (k-mentions-from? (car ts) v seen) (k-any-mentions? (cdr ts) v seen))))))
(define k-mentions-var? (->* (int int) bool)
  (lambda (t v) (k-mentions-from? t v (the (ref k-ids @t) (new nil)))))
;; The first of `vs` that `t` mentions, or -1.
(define k-first-mentioned (->* (int k-ids) int)
  (lambda (t vs)
    (cond ((null? vs) -1)
          ((k-mentions-var? t (car vs)) (car vs))
          (else (k-first-mentioned t (cdr vs))))))

;;; ------------------------------------------------------------ naming

;; Whether `v` was made for a module's abstract type as it was bound.
(define k-module-var? (->* (int) bool)
  (lambda (v) (k-has-id? (get k-module-vars) v)))
(define k-rename-abs (->* (string k-parts) k-renamed)
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
(define k-subst-each (->* (k-parts k-map) k-parts)
  (lambda (ps m)
    (if (null? ps)
        nil
        (let* ((t (k-subst (extract (car ps) 2) m)) (rest (k-subst-each (cdr ps) m)))
          (cons (product (1 (extract (car ps) 1)) (2 t)) rest)))))
;; A module's type, bound to `name`: its abstract types renamed for this
;; binding, each `name..t`, kept until the binding's scope ends. Any other
;; type as it is; and a hidden item's (`%extend-0`, …), the module's own
;; making, whose module keeps the names it has (`TODO.md` §69).
(define k-name-module (->* (symbol int) int)
  (lambda (name t)
    (tagcase (k-get (k-resolve t))
      (ty-module (abs ds vs)
        (if (or (null? abs) (string=? (substring (symbol->string name) 0 1) "%"))
            t
            (let* ((r (k-rename-abs (string-append (symbol->string name) "..") abs))
                   (ds2 (k-subst-each ds (extract r 2)))
                   (vs2 (k-subst-each vs (extract r 2))))
              (k-ty-new (ty-module (extract r 1) ds2 vs2)))))
      (else y t))))
;; Of the sizes and abstract types `vs`, named in a scope that `t` leaves:
;; the sizes, to be forgotten. A module's abstract type cannot be: nothing
;; may leave its binding's scope still mentioning it.
(define k-sizes-of (->* (k-ids) k-ids)
  (lambda (vs)
    (cond ((null? vs) nil)
          ((k-module-var? (car vs)) (k-sizes-of (cdr vs)))
          (else (cons (car vs) (k-sizes-of (cdr vs)))))))
(define k-escaping (->* (int k-ids) int)
  (lambda (t vs)
    (cond ((null? vs) -1)
          ((and (k-module-var? (car vs)) (k-mentions-var? t (car vs))) (car vs))
          (else (k-escaping t (cdr vs))))))
(define k-unescaped (->* (int k-ids int int) k-ids)
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
;; A type name in a module with `include`s that nothing else defines
;; (`k-type-unknown`): said of the name, not of the hidden `%include`. As
;; the Rust checker's.
(define k-not-included (->* (symbol) string)
  (lambda (n)
    (string-append (k-quote (symbol->string n)) " is not a type, nor one a module included gives")))
;; The same for an effect name (`k-effect-unknown`).
(define k-not-included-effect (->* (symbol) string)
  (lambda (n)
    (string-append (k-quote (symbol->string n))
                   " is not an effect, nor one a module included gives")))
;; `(select m n)`, as an error shows it.
(define k-select-shown (->* (symbol symbol) string)
  (lambda (m n) (k-cat5 "`(select " (symbol->string m) " " (symbol->string n) ")`")))
;; The type component `n` of parts `ps`, or -1.
(define k-comp-find (->* (k-parts symbol) int)
  (lambda (ps n)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) n) (extract (car ps) 2))
          (else (k-comp-find (cdr ps) n)))))
;; What `(select m n)` is, `m` a module bound to a type of abstract types
;; `abs` and descriptions `ds`: its abstract type `n`, or its description;
;; an error at `a`..`b` if it has neither. -3 if it is a `with`'s applied,
;; `(n d …)`, that `m` does not give: the application is linked to what it
;; is outside (`k-with-applied`), and the `select` is not resolved.
(define k-select-component
  (->* (symbol symbol k-parts k-parts int int int) int)
  (lambda (m n abs ds node a b)
    (let ((v (k-comp-find abs n)) (d (k-comp-find ds n)) (outer (k-with-fallback node))
          (app (k-with-app-of node)))
      (cond ((>= v 0) (k-ty-new (ty-var v)))
            ((>= d 0) d)
            ((and (>= app 0) (>= outer 0))
             (begin (k-set-link app (k-resolve-selects outer a b)) -3))
            ((>= app 0)
             (k-fail (k-cat3 (k-quote (symbol->string n)) " is not a description function,"
                             " nor one a module opened by `with` gives")
                     a b))
            ;; A name read in a `with` body that `m` does not give: what it
            ;; is outside the `with` (`k-with-selected`).
            ((>= outer 0) (k-resolve-selects outer a b))
            ((= outer -1)
             (k-fail (string-append (k-quote (symbol->string n))
                                    " is not a type, nor one a module opened by `with` gives")
                     a b))
            ((symbol=? m '%include) (k-fail (k-not-included n) a b))
            (else (k-fail (k-cat5 (k-select-shown m n) ": `" (symbol->string m) "` has no type `"
                                  (string-append (symbol->string n) "`"))
                          a b))))))
;; What an error about `(select m n)` starts with; made only for an error.
(define k-select-prefix (->* (symbol symbol) string)
  (lambda (m n) (k-cat3 (k-select-shown m n) ": `" (symbol->string m))))
;; A global module's type, as `select` node `node` names it: that node from
;; now on, linked to `to`, so that whatever leads to it is not rebuilt, and
;; is shared, and shown by its name. Not a family, which is read as the
;; `select` it is; nor a local module's, which may differ by scope.
(define k-link-global-select (->* (symbol int int) unit)
  (lambda (m node to)
    (if (and (or (k-global? m) (k-fixed? m))
             (tagcase (k-get to)
               (ty-lam (bs d) #f)
               (ty-var (v) (= (k-dvar-kind v) 2))
               (else y #t)))
        (k-set-link node to)
        #u)))
;; Module `m`'s component `n`, as select node `node` names it, linked.
(define k-link-alias (->* (symbol symbol int) unit)
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
(define k-link-aliases (->* (symbol k-scope) unit)
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
(define k-selection (->* (k-selects int int) k-selects)
  (lambda (found a b)
    (if (null? found)
        nil
        (let* ((m (extract (car found) 1)) (n (extract (car found) 2))
               (mt (k-lookup m))
               (to (if (< mt 0)
                       (if (symbol=? m '%include)
                           (k-fail (k-not-included n) a b)
                           (k-fail (string-append (k-select-prefix m n) "` is not bound here") a b))
                       (tagcase (k-get mt)
                         (ty-module (abs ds vs)
                           (k-select-component m n abs ds (extract (car found) 3) a b))
                         (else y (k-fail (k-cat4 (k-select-prefix m n) "` is a " (k-show-ty mt)
                                                 ", not a module")
                                         a b)))))
               (linked (if (= to -3) #u (k-link-global-select m (extract (car found) 3) to)))
               (rest (k-selection (cdr found) a b)))
          (if (= to -3) rest (cons (product (1 m) (2 n) (3 to)) rest))))))
;;; ------------------------------------------------------------ effects selected

;; The entry of `ss` for variable `v`, or none.
(define k-effect-sel-var (->* (k-effect-sels int) k-effect-sels)
  (lambda (ss v)
    (cond ((null? ss) nil)
          ((= (extract (car ss) 3) v) ss)
          (else (k-effect-sel-var (cdr ss) v)))))
;; `e`'s effect variables that stand for `(select m e)`s, onto `out`, each
;; once.
(define k-esels-note (->* (k-eff (ref k-effect-sels @t)) unit)
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
(define k-esels-descs (->* (k-descs (ref k-effect-sels @t)) unit)
  (lambda (ds out)
    (if (null? ds)
        #u
        (begin (tagcase (car ds) (de (e) (k-esels-note e out)) (else x #u))
               (k-esels-descs (cdr ds) out)))))
;; Each effect `(select m e)` in `t`, onto `out`; the nodes walked, `seen`.
(define-rec
  (k-esels-from (->* (int k-seen (ref k-effect-sels @t)) unit)
    (lambda (t seen out)
      (let ((t (k-resolve t)))
        (if (k-seen? seen t)
            #u
            (begin
              (tagcase (k-get t)
                (ty-subr (e ps r cv spc) (k-esels-note e out))
                (ty-tag (a h e r) (k-esels-note e out))
                (ty-comp (a h e r once) (k-esels-note e out))
                (ty-lam (bs d) (k-esels-descs (the k-descs (list d)) out))
                (ty-app (f ds) (k-esels-descs ds out))
                (ty-named (g ds) (k-esels-descs ds out))
                (else y #u))
              (k-esels-each (k-ty-kids t) seen out))))))
  (k-esels-each (->* (k-ids k-seen (ref k-effect-sels @t)) unit)
    (lambda (ts seen out)
      (if (null? ts)
          #u
          (begin (k-esels-from (car ts) seen out) (k-esels-each (cdr ts) seen out))))))
;; The effect `(select m e)`s in `t`, in the order met.
(define k-effect-selects-in (->* (int) k-effect-sels)
  (lambda (t)
    (if (null? (get k-effect-selects))
        nil
        (let ((out (the (ref k-effect-sels @t) (new nil))))
          (begin (k-esels-from t (k-new-seen) out) (reverse (get out)))))))
;; The effect a module's description `d` is, in a list; none if not one.
(define k-desc-effect (->* (int) (listof k-eff acyclic))
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
(define k-selected-effect (->* (symbol symbol int int) k-eff)
  (lambda (m e a b)
    (let ((mt (k-lookup m)))
      (if (< mt 0)
          (begin (k-fail (if (symbol=? m '%include)
                             (k-not-included-effect e)
                             (string-append (k-select-prefix m e) "` is not bound here"))
                         a b)
                 (the k-eff nil))
          (tagcase (k-get mt)
            (ty-module (abs ds vs)
              (let* ((d (k-comp-find ds e))
                     (x (if (< d 0) (the (listof k-eff acyclic) nil) (k-desc-effect d))))
                (if (null? x)
                    (let ((msg (if (symbol=? m '%include)
                                   (k-not-included-effect e)
                                   (k-cat4 (k-select-prefix m e) "` has no effect `"
                                           (symbol->string e) "`"))))
                      (begin (k-fail msg a b) (the k-eff nil)))
                    (car x))))
            (else y (begin (k-fail (k-cat4 (k-select-prefix m e) "` is a " (k-show-ty mt)
                                           ", not a module")
                                   a b)
                           (the k-eff nil))))))))
;; What effect variable `v`, for `(select m e)`, is: `m`'s effect `e`; for a
;; `with` body's name that `m` does not give, what it is outside the `with`
;; (`k-with-effect-selected`), itself resolved. As Rust's `effect_selected`.
(define k-effect-selected (->* (int symbol symbol int int) k-eff)
  (lambda (v m e a b)
    (let ((fall (k-with-effect-fall v)))
      (if (null? fall)
          (k-selected-effect m e a b)
          (let* ((mt (k-lookup m))
                 (given (if (< mt 0)
                            (the (listof k-eff acyclic) nil)
                            (tagcase (k-get mt)
                              (ty-module (abs ds vs)
                                (let ((d (k-comp-find ds e)))
                                  (if (< d 0) (the (listof k-eff acyclic) nil) (k-desc-effect d))))
                              (else y (the (listof k-eff acyclic) nil))))))
            (cond ((not (null? given)) (car given))
                  ((extract (car fall) 2) (k-effect-resolved (extract (car fall) 3) a b))
                  (else (begin (k-fail (k-cat3 (k-quote (symbol->string e)) " is not an effect, "
                                               "nor one a module opened by `with` gives")
                                       a b)
                               (the k-eff nil)))))))))
;; Effect `x` with each variable for a `select` in it resolved
;; (`k-effect-selected`).
(define k-effect-resolved (->* (k-eff int int) k-eff)
  (lambda (x a b)
    (if (null? x)
        nil
        (let ((rest (k-effect-resolved (cdr x) a b)))
          (tagcase (car x)
            (a-var (w)
              (let ((sel (k-effect-sel-var (get k-effect-selects) w)))
                (if (null? sel)
                    (k-union (k-one (car x)) rest)
                    (k-union (k-effect-selected w (extract (car sel) 1) (extract (car sel) 2) a b)
                             rest))))
            (else y (k-union (k-one (car x)) rest)))))))
;; What each effect selected stands for, as a substitution.
(define k-effects-given (->* (k-effect-sels int int) k-map)
  (lambda (ss a b)
    (if (null? ss)
        nil
        (let* ((x (car ss)) (e (k-effect-selected (extract x 3) (extract x 1) (extract x 2) a b))
               (rest (k-effects-given (cdr ss) a b)))
          (the k-map (cons (cons (extract x 3) (de e)) rest))))))
;; Whether `e` names a variable `given` replaces.
(define k-eff-given? (->* (k-eff k-map) bool)
  (lambda (e given)
    (and (not (null? e))
         (or (tagcase (car e) (a-var (v) (not (null? (k-map-find given v)))) (else y #f))
             (k-eff-given? (cdr e) given)))))
(define k-descs-given? (->* (k-descs k-map) bool)
  (lambda (ds given)
    (and (not (null? ds))
         (or (tagcase (car ds) (de (e) (k-eff-given? e given)) (else x #f))
             (k-descs-given? (cdr ds) given)))))
;; Whether node `n` is itself what a `select`'s resolution changes: a
;; `select`, a `(select $k t)`, or an effect naming a variable `given`
;; replaces.
(define k-select-seed? (->* (int k-map) bool)
  (lambda (n given)
    (tagcase (k-get n)
      (ty-select (m s) #t)
      (ty-param (k s) #t)
      (ty-subr (e ps r cv spc) (k-eff-given? e given))
      (ty-tag (a h e r) (k-eff-given? e given))
      (ty-comp (a h e r once) (k-eff-given? e given))
      (ty-lam (bs d) (k-descs-given? (the k-descs (list d)) given))
      (ty-app (f ds) (k-descs-given? ds given))
      (ty-named (g ds) (k-descs-given? ds given))
      (else y #f))))
;; The nodes reached from `t`, through `k-ty-kids`, onto `out`; `e` the walk.
(define-rec
  (k-nodes-from (->* (int int (ref k-ids @t)) unit)
    (lambda (t e out)
      (let ((t (k-resolve t)))
        (if (k-visit? t e)
            #u
            (begin (set out (cons t (get out))) (k-nodes-each (k-ty-kids t) e out))))))
  (k-nodes-each (->* (k-ids int (ref k-ids @t)) unit)
    (lambda (ts e out)
      (if (null? ts) #u (begin (k-nodes-from (car ts) e out) (k-nodes-each (cdr ts) e out))))))
;; Whether a child of `n` is marked `d`.
(define k-kid-marked? (->* (k-ids int) bool)
  (lambda (ks d)
    (and (not (null? ks)) (or (= (k-keep-at (k-resolve (car ks))) d) (k-kid-marked? (cdr ks) d)))))
;; Each of `ns` not marked `d` with a child that is, marked `d`: whether any.
(define k-mark-parents (->* (k-ids int bool) bool)
  (lambda (ns d changed)
    (cond ((null? ns) changed)
          ((and (not (= (k-keep-at (car ns)) d)) (k-kid-marked? (k-ty-kids (car ns)) d))
           (begin (k-keep-set! (car ns) d) (k-mark-parents (cdr ns) d #t)))
          (else (k-mark-parents (cdr ns) d changed)))))
(define k-mark-until-still (->* (k-ids int) unit)
  (lambda (ns d) (if (k-mark-parents ns d #f) (k-mark-until-still ns d) #u)))
;; Each of `ns` that is itself what resolving changes (`k-select-seed?`),
;; marked `d`.
(define k-mark-seeds (->* (k-ids k-map int) unit)
  (lambda (ns given d)
    (if (null? ns)
        #u
        (begin (if (k-select-seed? (car ns) given) (k-keep-set! (car ns) d) #u)
               (k-mark-seeds (cdr ns) given d)))))
(define k-mark-kept (->* (k-ids int int) unit)
  (lambda (ns d k)
    (if (null? ns)
        #u
        (begin (if (= (k-keep-at (car ns)) d) #u (k-keep-set! (car ns) k))
               (k-mark-kept (cdr ns) d k)))))
;; The nodes of `t` from which no `select` is reached, marked kept: the
;; epoch they are marked with. As the Rust checker's `select_clean`.
(define k-select-clean (->* (int k-map) int)
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
(define k-resolve-selects (->* (int int int) int)
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
(define k-select-syn (->* (int syn) int)
  (lambda (t s) (k-resolve-selects t (syn-start s) (syn-end s))))
;; The same for the types a `letrec`'s bindings `bs` are declared, at the
;; `letrec`, `a`..`b`.
(define k-letrec-selected (->* (k-letrec-bs int int) k-letrec-bs)
  (lambda (bs a b)
    (if (null? bs)
        nil
        (let* ((x (car bs))
               (t (k-resolve-selects (extract x 2) a b))
               (marked (k-arrow-star-as (extract x 2) t))
               (rest (k-letrec-selected (cdr bs) a b)))
          (cons (product (1 (extract x 1)) (2 t) (3 (extract x 3))) rest)))))
;; The first `select` of `found` from one of `params`, or none.
(define k-select-from (->* (k-selects k-names) k-selects)
  (lambda (found params)
    (cond ((null? found) nil)
          ((k-has-name? params (extract (car found) 1)) (cons (car found) nil))
          (else (k-select-from (cdr found) params)))))
;; `t` resolved, at `a`..`b`, where `params` are not yet bound, and so may
;; not be selected from: one that names the parameter it is the type of, or
;; a later one.
(define k-resolve-outside (->* (int k-names int int) int)
  (lambda (t params a b)
    (let ((dependent (k-select-from (k-selects-in t) params)))
      (if (null? dependent)
          (k-resolve-selects t a b)
          (let ((s (car dependent)))
            (k-fail (string-append
                     (k-select-shown (extract s 1) (extract s 2))
                     " names a parameter of the same `lambda`: "
                     "a dependent type, not supported yet")
                    a b))))))
(define k-binding-names (->* (k-bindings) k-names)
  (lambda (bs) (if (null? bs) nil (cons (car (car bs)) (k-binding-names (cdr bs)))))))))
