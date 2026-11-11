;;; The checker, in FX-26: what reading types uses that reads none of
;;; them, taken out of its knot: its messages and lists of keywords;
;;; binders and parameters as names, scopes and descriptions; the kids of
;;; a description; parameters' selects. Before `check-read-descs.fx`.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (check-read-types (load-module "fx26:check-read-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (eager-reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-syntax-types (load-module "fx26:check-syntax-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (reader-types (load-module "fx26:reader-types.fx"))
       (check-flat-types (load-module "fx26:check-flat-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-read (select check-read-types check-read-sig))
           (check-env (select check-env-types check-env-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (check-print (select check-print-types check-print-sig))
           (check-syntax (select check-syntax-types check-syntax-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (parser (select reader-types parser-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig))
           ;; Flat data (`check-flat.fx`), whose names its clients use here.
           (check-flat (select check-flat-types check-flat-sig)))
    (module

;; The types it uses of the files before it.
(hide (include check-types-types) (include check-read-types) (include check-env-types)
      (include check-subst-types) (include eager-reader-types) (include parser-types))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-syntax) (include check-print-parts) (include check-env)
      (include check-subst) (include check-print) (include parser))
(import check-read k-atom-head? k-sfail k-items k-any-typed-kind? k-arrow-syntax)
(import check-effects k-one k-insert)
;; Flat data, given on (`check-flat.fx`).
(import check-flat k-flat-not-type k-flat-var-type? k-is-flat? k-parse-flat k-flat-code
        k-flat-layout k-flat-field k-unsized-length k-with-unsized-length k-flat-array-parts
        k-flat-sum-size k-flat-view k-else-type k-in-scope-check k-in-scope-parts k-blobref-variant
        k-blobref-parts k-blobref-of)

;; A `dlambda` of no parameters, as an error says.
(define k-dlambda-empty string "a `dlambda` takes at least one description")
(define k-moduleof-usage string "`(moduleof (abs t type) … (desc d type) … (val x type) …)`")
(define k-abs-usage string
  "an abstract component is a `type`, or a type constructor `(=> (kind …) type)`, for now")
;; Where `->*` is not a definition's signature.
(define k-arrow-star-only string
  (string-append "`(->* (param …) result)` is only the type a definition declares (`define`, "
                 "`define-rec`, `letrec`), its effect found from its `lambda`: "
                 "here, write `->` or `subr`"))
(define k-abs-ctor-usage string "an abstract type constructor is `(abs (f (name kind) …) type)`")
;; What a list headed `hd` is not, read as a type: `hd` applied, if a name.
(define k-not-type-list (->* (symbol) string)
  (lambda (hd)
    (if (symbol=? hd '|()|)
        "expected a type"
        (string-append (k-quote (symbol->string hd)) " is not a description function"))))
;; The heads of the type forms a type is read from, and every keyword: no
;; parameter's name.
(define k-type-forms k-names
  (list 'arrayof 'narrayof 'bloblet 'composable 'dletrec 'icell 'listof 'mark-key 'moduleof 'mu
        'nat 'nlist 'oneshot 'pairof 'place 'poly 'productof 'prompt-tag 'proves 'ref 'select 'subr
        'sumof 'tupleof 'bool 'oneof 'union 'anyof 'allof '-> '->* 'restrict 'modnames))
;; Whether `hd` heads a type form: not a name a `with` shadows.
(define k-type-form? (->* (symbol) bool)
  (lambda (hd) (k-has-name? k-type-forms hd)))
;; The Rust front end's `top::KEYWORDS`, which a test holds this to.
(define k-keywords k-names
  (list 'lambda 'plambda 'proj 'if 'letrec 'let 'begin 'define 'define* 'define-type
        'define-generative 'subr '-> '->* 'poly 'ref 'pairof 'dletrec 'void 'pure 'maxeff 'read
        'write 'alloc 'goto 'comefrom 'region 'effect 'type 'prompt 'prompt-tag 'composable
        'oneshot 'mark-key 'listof 'cond 'case 'else 'and 'or 'let* 'define-effect
        'define-convention 'define-syscall 'define-optional-syscall 'syscall-available?
        'module-parameters 'the 'bloblet 'fields 'frozen 'arrayof 'icell 'await 'define-rec
        'letrena 'letreap 'rlambda 'quote 'productof 'sumof 'product 'tupleof 'tuple 'extract 'sum
        'tagcase 'module 'moduleof 'with 'select 'load-module 'import 'define-datatype
        'make-bloblet 'bloblet-ref 'bloblet-set! 'bloblet-freeze 'bloblet-byte 'bloblet-set-byte!
        'bloblet-bytes 'rmake-bloblet 'dlambda '=> 'blobref-at 'blobref+ 'blobref-owner
        'blobref-offset 'blobref-get 'blobref-set! 'blobref-index 'blobref-length
        'blobref-variant! 'vlambda 'stage 'session-check 'session-commit! 'typecase 'reify-type
        'reify-effect 'reify-region 'confirm-length 'confirm-nat 'convention 'extend 'load-input
        'quasiquote 'letregion 'letfreeze 'spawn 'spawn-monitored 'send 'receive 'self 'par 'race
        'attempt 'attempt-within 'pselect 'icell-get 'icell-put! 'acyclic))
(define k-no-name symbol '||)
;; Whether effect `e` is variable `v` alone.
(define k-eff-is-var? (->* (k-eff int) bool)
  (lambda (e v)
    (and (not (null? e)) (null? (cdr e)) (tagcase (car e) (a-var (w) (= w v)) (else y #f)))))
;; Whether `d` is variable `v` and nothing more.
(define k-is-the-var? (->* (k-desc int) bool)
  (lambda (d v)
    (tagcase d
      (dr (r) (tagcase r (r-var (w) (= w v)) (else y #f)))
      (de (e) (k-eff-is-var? e v))
      (dz (z)
        (tagcase z
          (sz-lin (k ts)
            (and (= k 0) (not (null? ts)) (null? (cdr ts))
                 (= (car (car ts)) v) (= (cdr (car ts)) 1)))
          (else y #f)))
      (dc (c) (tagcase c (cv-var (w) (= w v)) (else y #f)))
      (dt (t) (k-type-is-var? t v))
      (df (t) (k-type-is-var? t v)))))
;; Whether `ds` are `bs`'s variables, in order.
(define k-the-vars? (->* (k-descs k-binders) bool)
  (lambda (ds bs)
    (cond ((null? ds) (null? bs))
          ((null? bs) #f)
          ((k-is-the-var? (car ds) (extract (car bs) 1)) (k-the-vars? (cdr ds) (cdr bs)))
          (else #f))))
;; Whether `f` is one of `bs`'s variables.
(define k-param-head? (->* (int k-binders) bool)
  (lambda (f bs) (tagcase (k-get f) (ty-var (v) (k-binder-has? bs v)) (else y #f))))
;; `(dlambda bs body)`, or, where `body` only applies a function to the
;; parameters in order, that function (eta).
(define k-lam (->* (k-binders k-desc) int)
  (lambda (bs body)
    (let ((eta (tagcase body
                 (dt (t)
                   (tagcase (k-get t)
                     (ty-app (f ds)
                       (if (and (k-the-vars? ds bs) (not (k-param-head? f bs))) f -1))
                     (else y -1)))
                 (else y -1))))
      (if (>= eta 0) eta (k-ty-new (ty-lam bs body))))))
;; Each of binders `bs`, as a description.
(define k-binders-as-descs (->* (k-binders) k-descs)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((d (k-binder-desc (extract (car bs) 2) (extract (car bs) 1)))
               (rest (k-binders-as-descs (cdr bs))))
          (the k-descs (cons d rest))))))
;; "`f` takes n description(s), and has m", `f` shown.
(define k-fun-arity-message (->* (int int int) string)
  (lambda (f want have)
    (k-cat5 (k-quote (k-show-ty f)) " takes " (int->string want)
            " description(s), and has " (int->string have))))
;; Binders of `kinds`, each a fresh variable named as `names`.
(define k-fresh-named (->* (k-names k-ids) k-binders)
  (lambda (ns ks)
    (if (null? ns)
        nil
        (let* ((v (k-new-dvar-of (car ns) (car ks))) (rest (k-fresh-named (cdr ns) (cdr ks))))
          (the k-binders (cons (product (1 v) (2 (car ks))) rest))))))
;; Each binder, as a type family's parameter is bound to what it is given.
(define k-binders-as-scope (->* (k-binders) k-scope)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((v (extract (car bs) 1)) (k (extract (car bs) 2))
               (d (cond ((k-type-kind? k) (ds-rec (k-ty-new (ty-var v))))
                        ((= k 7) (ds-var v 7))
                        ((or (= k 0) (= k 3)) (ds-region (r-var v)))
                        ((= k 1) (ds-eff (k-one (a-var v))))
                        ((= k 5) (ds-size (k-size-var v)))
                        ((= k 6) (ds-conv (cv-var v)))
                        (else (ds-fun (k-ty-new (ty-var v))))))
               (rest (k-binders-as-scope (cdr bs))))
          (the k-scope (cons (cons (k-dvar-name v) d) rest))))))
;; Type form `n`, `listof` and kin, of `ts`, given `t` and `r`.
(define k-ctor-type (->* (string k-binders) int)
  (lambda (n bs)
    (let* ((t (k-ty-new (ty-var (extract (car bs) 1))))
           (second (extract (car (cdr bs)) 1))
           (r (r-var (if (null? (cdr (cdr bs))) second (extract (car (cdr (cdr bs))) 1)))))
      (case n (("ref") (k-ty-new (ty-ref t r)))
              (("icell") (k-ty-new (ty-icell t r)))
              (("arrayof") (k-ty-new (ty-array t (sz-finite) r)))
              (("mark-key") (k-ty-new (ty-markkey t r)))
              (("pairof") (k-ty-new (ty-pair t (k-ty-new (ty-var second)) r #f)))
              (else (let* ((slot (k-slot)) (pair (k-ty-new (ty-pair t slot r #t))))
                      (begin (k-set-link slot pair) slot)))))))
(define k-params-names (->* (k-params) k-names)
  (lambda (ps) (if (null? ps) nil (cons (extract (car ps) 1) (k-params-names (cdr ps))))))
(define k-params-kinds (->* (k-params) k-ids)
  (lambda (ps) (if (null? ps) nil (cons (extract (car ps) 2) (k-params-kinds (cdr ps))))))
;; Whether `n` is bound to a description function.
(define k-fun-bound? (->* (string) bool)
  (lambda (n)
    (if (and (> (string-length n) 11) (string=? (substring n 0 11) "#%toplevel:"))
        ;; `#%toplevel:f`: the top level's `f`.
        (let* ((was (k-toplevel-enter)) (b (k-fun-bound? (substring n 11 (string-length n)))))
          (begin (k-toplevel-leave was) b))
        (let ((d (k-lookup-desc (string->symbol n))))
          (and (not (null? d))
               (tagcase (car d) (ds-var (v k) (k-arrow-kind? k)) (ds-fun (f) #t) (else y #f)))))))
;; What binds `hd`, a type's head: none if it is a type form's name, read
;; by the name alone (`parse.rs`'s `TYPE_FORMS`).
(define k-head-bound (->* (symbol) (listof k-ds acyclic))
  (lambda (hd)
    (if (or (symbol=? hd '|()|) (k-type-form? hd)) nil (k-lookup-desc hd))))
;; Whether `n`, an effect's head, names a description function: never an
;; effect form's name, read by the name alone (`parse.rs`'s `EFFECT_HEADS`).
(define k-effect-fun? (->* (string) bool)
  (lambda (n) (and (not (k-atom-head? n)) (not (string=? n "maxeff")) (k-fun-bound? n))))
;; Binder `b`'s name.
(define k-binder-name (->* ((productof (1 int) (2 int))) symbol)
  (lambda (b) (k-dvar-name (extract b 1))))
(define k-binder-names (->* (k-binders) k-names)
  (lambda (bs) (if (null? bs) nil (cons (k-binder-name (car bs)) (k-binder-names (cdr bs))))))
;; `(select m t)`: as written, for checking to resolve where `m` is bound.
(define k-parse-select (->* (syn k-syns) int)
  (lambda (s items)
    (cond ((not (= (k-length items) 3)) (k-sfail "`(select module name)`" s))
          ((and (syn-symbol? (k-nth items 1)) (syn-symbol? (k-nth items 2)))
           (k-ty-new (ty-select (k-toplevel-qualified (syn-head (k-nth items 1)))
                                (syn-head (k-nth items 2)))))
          (else (k-sfail "`(select module name)`: a module's name, and a component's" s)))))
;; Function `f`, given `have` descriptions at `s`, where it takes `want`.
(define k-arity-fail (->* (int int int syn) void)
  (lambda (f want have s) (k-sfail (k-fun-arity-message f want have) s)))
;; Function `f`, at `s`, giving a `result` where a `wanted` is.
(define k-gives-fail (->* (int int string syn) void)
  (lambda (f result wanted s)
    (k-sfail (k-cat5 (k-quote (k-show-ty f)) " gives a description of kind " (k-kind-text result)
                     ", not " wanted)
             s)))
;; Function `f`, at `s`, not giving a `wanted`.
(define k-not-giving (->* (int string syn) void)
  (lambda (f wanted s) (k-sfail (k-cat3 (k-quote (k-show-ty f)) " does not give " wanted) s)))
;; A generative type as one.
(define k-gen-eta (->* (int k-binders) int)
  (lambda (g ps)
    (let* ((bs (k-fresh-named (k-binder-names ps) (k-binder-kinds ps)))
           (t (k-ty-new (ty-named g (k-binders-as-descs bs)))))
      (k-lam bs (dt t)))))
;; A type form, `listof` and kin, as one.
(define k-ctor-eta (->* (string k-params) int)
  (lambda (n ps)
    (let ((bs (k-fresh-named (k-params-names ps) (k-params-kinds ps))))
      (k-lam bs (dt (k-ctor-type n bs))))))
;; `ps` reversed, onto `acc`.
(define k-parts-reversed (->* (k-parts k-parts) k-parts)
  (lambda (ps acc) (if (null? ps) acc (k-parts-reversed (cdr ps) (cons (car ps) acc)))))
;; The names among `xs`; what is not one is passed over.
(define k-syn-symbols (->* (k-syns) k-names)
  (lambda (xs)
    (cond ((null? xs) nil)
          ((syn-symbol? (car xs)) (cons (syn-head (car xs)) (k-syn-symbols (cdr xs))))
          (else (k-syn-symbols (cdr xs))))))
;; Whether every one of `xs` is a name.
(define k-all-symbols? (->* (k-syns) bool)
  (lambda (xs) (or (null? xs) (and (syn-symbol? (car xs)) (k-all-symbols? (cdr xs))))))
;; `(abs (f (name kind) …) type)`'s parameters' kinds, unread, from `ps`; `name`
;; is said wrong if they are not.
(define k-ctor-param-kinds (->* (k-syns syn) k-syns)
  (lambda (ps name)
    (if (null? ps)
        nil
        (tagcase (car ps)
          (lst (items d a b xpn)
            (if (and (= (k-length items) 2) (syn-symbol? (car items)))
                (cons (car (cdr items)) (k-ctor-param-kinds (cdr ps) name))
                (k-sfail k-abs-ctor-usage name)))
          (else x (k-sfail k-abs-ctor-usage name))))))
;; `(abs (f (name kind) …) type)`'s parameters' kinds, unread: `(abs f (=>
;; (kind …) type))`, as `define-generative` writes its parameters. None for
;; a name, or a list of names.
(define k-abs-ctor-params (->* (syn) k-syns)
  (lambda (name)
    (tagcase name
      (lst (items d a b xpn)
        (cond ((k-all-symbols? items) nil)
              ((syn-symbol? (car items)) (k-ctor-param-kinds (cdr items) name))
              (else (k-sfail k-abs-ctor-usage name))))
      (else x nil))))
;; A component's names: its name; or, an `abs`'s, the names in a list.
(define k-component-names (->* (syn string) k-names)
  (lambda (name head)
    (if (syn-symbol? name)
        (the k-names (cons (syn-head name) nil))
        (tagcase name
          (lst (items d a b xpn)
            (cond ((not (string=? head "abs")) (k-sfail "a component's name" name))
                  ((k-all-symbols? items) (k-syn-symbols items))
                  ;; One constructor, its parameters' kinds given.
                  (else (begin (k-abs-ctor-params name) (cons (syn-head (car items)) nil)))))
          (else x (k-sfail "a component's name" name))))))
;; `seen` and `names`, each named once in component `c`.
(define k-names-once (->* (k-names k-names syn) k-names)
  (lambda (names seen c)
    (cond ((null? names) seen)
          ((k-has-name? seen (car names)) (k-sfail (k-twice (symbol->string (car names))) c))
          (else (k-names-once (cdr names) (cons (car names) seen) c)))))
;; Abstract types `names`, each a variable of kind `k`, in scope from here,
;; onto `abs`; a type constructor among `k-abstract-funs`.
(define k-abs-bound (->* (k-names int k-parts) k-parts)
  (lambda (names k abs)
    (if (null? names)
        abs
        (let* ((n (car names)) (v (k-new-dvar-of n k)))
          (begin (if (= k 2) #u (set k-abstract-funs (cons v (get k-abstract-funs))))
                 (k-push-desc n (ds-var v k))
                 (k-abs-bound (cdr names) k (cons (product (1 n) (2 v)) abs)))))))
;; `(name type)` onto `ps`.
(define k-part-onto (->* (symbol int k-parts) k-parts)
  (lambda (n t ps) (cons (product (1 n) (2 t)) ps)))
;; Whether `s` is written as an effect: `pure`, `spin`, a name bound to one,
;; or one of `k-parse-effect`'s atoms or `maxeff`.
(define k-effect-shaped? (->* (syn) bool)
  (lambda (s)
    (if (syn-symbol? s)
        (let ((n (syn-name s)))
          (or (string=? n "pure") (string=? n "spin") (string=? n "nondet") (string=? n "stage")
              (let ((d (k-lookup-desc (string->symbol n))))
                (and (not (null? d))
                     (tagcase (car d) (ds-eff (e) #t) (ds-var (v k) (= k 1)) (else x #f))))))
        (let ((h (k-list-head s))) (or (k-atom-head? h) (string=? h "maxeff"))))))
;; The types of parts `ps`, onto `tail`.
(define k-parts-onto (->* (k-parts k-ids) k-ids)
  (lambda (ps tail)
    (if (null? ps) tail (cons (extract (car ps) 2) (k-parts-onto (cdr ps) tail)))))
;; `ts`, and `t` after them.
(define k-ids-then (->* (k-ids int) k-ids)
  (lambda (ts t) (if (null? ts) (cons t nil) (cons (car ts) (k-ids-then (cdr ts) t)))))
;; The types and functions among descriptions `ds`.
(define k-desc-kids (->* (k-descs) k-ids)
  (lambda (ds)
    (if (null? ds)
        nil
        (let ((rest (k-desc-kids (cdr ds))))
          (tagcase (car ds) (dt (x) (cons x rest)) (df (x) (cons x rest)) (else y rest))))))
;; The types `t` is made of, one level down.
(define k-ty-kids (->* (int) k-ids)
  (lambda (t)
    (tagcase (k-get t)
      (ty-subr (e ps r cv spc) (k-ids-then ps r))
      (ty-poly (bs x) (the k-ids (cons x nil)))
      (ty-ref (a r) (the k-ids (cons a nil)))
      (ty-array (a nz r) (the k-ids (cons a nil)))
      (ty-icell (a r) (the k-ids (cons a nil)))
      (ty-markkey (a r) (the k-ids (cons a nil)))
      (ty-pair (a d r nl) (k-ids-then (the k-ids (cons a nil)) d))
      (ty-tag (a h e r) (k-ids-then (the k-ids (cons a nil)) h))
      (ty-comp (x a e r once) (k-ids-then (the k-ids (cons x nil)) a))
      (ty-product (ps) (k-parts-onto ps nil))
      (ty-sum (ps) (k-parts-onto ps nil))
      (ty-bloblet (fs z r) fs)
      (ty-union (ms) ms)
      (ty-allof (ms) ms)
      (ty-named (g ds) (k-desc-kids ds))
      (ty-app (f ds) (the k-ids (cons f (k-desc-kids ds))))
      (ty-lam (bs x) (k-desc-kids (the k-descs (cons x nil))))
      (ty-nlist (e z r) (the k-ids (cons e nil)))
      (ty-module (abs ds vs) (k-parts-onto ds (k-parts-onto vs nil)))
      (else y nil))))
;; `ss` reversed, onto `acc`.
(define k-selects-reversed
  (->* (k-selects k-selects) k-selects)
  (lambda (ss acc) (if (null? ss) acc (k-selects-reversed (cdr ss) (cons (car ss) acc)))))
;; A procedure type's parameter written `(name type)`, where `name` names no
;; type or type form: its name, in a list of one; none if it is not one.
(define k-param-name (->* (syn) k-names)
  (lambda (p)
    (tagcase p
      (lst (items d a b xpn)
        (if (and (= (k-length items) 3) (syn-symbol? (car items)) (syn-symbol? (k-nth items 1))
                 (symbol=? (syn-head (k-nth items 1)) ':))
            (the k-names (cons (syn-head (car items)) nil))
            nil))
      (else x nil))))
;; `(h t)`, parameter `p`, is `h` applied; refused, saying how to name a
;; parameter, where `h` is no description function: where `later` (the
;; parameters after it, the result, the specification's clauses) names `h`,
;; as `(select h x)` or a proposition does; or where `h` is unknown and no
;; module included or opened by `with` may give it (`misnamed_param`).
(define k-misnamed-param (->* (syn k-syns) unit)
  (lambda (p later)
    (tagcase p
      (lst (items d a b xpn)
        (if (and (= (k-length items) 2) (syn-symbol? (car items)))
            (let* ((h (syn-head (car items))) (name (symbol->string h)))
              (if (or (k-has-name? k-type-forms h) (k-has-name? k-keywords h)
                      (not (null? (k-lookup-desc h))) (>= (k-find (get k-base) h) 0))
                  #u
                  (let ((fix (k-cat3 "to name a parameter, write `(" name " : type)`"))
                        (used (k-named-in-each later h)))
                    (cond ((not (string=? used "-"))
                           (k-sfail
                             (k-cat5 (k-cat3 "`(" name " …)` applies `") name "`, but "
                                     (if (string=? used "")
                                         "what follows"
                                         (k-cat3 "`" used "` after it"))
                                     (k-cat5 " names `" name "`: " fix ""))
                             p))
                          ((and (null? (k-lookup-desc '%include-scope)) (null? (k-withs-over h)))
                           (k-sfail (k-cat5 "`" name "` is not a description function: " fix "") p))
                          (else #u)))))
            #u))
      (else x #u))))
;; Where `s` has `n` other than as a list's head: the list it is in, shown
;; if all of it is names, else ""; or "-" if nowhere (`named_in`).
(define k-named-in (->* (syn symbol) string)
  (lambda (s n)
    (tagcase s
      (lst (items d a b xpn)
        (if (k-syns-name? (if (and (not (null? items)) (syn-symbol? (car items))) (cdr items) items)
                          n)
            (if (k-all-names? items) (k-cat3 "(" (k-names-shown items) ")") "")
            (k-named-in-each items n)))
      (else x "-"))))
(define k-named-in-each (->* (k-syns symbol) string)
  (lambda (xs n)
    (if (null? xs)
        "-"
        (let ((u (k-named-in (car xs) n))) (if (string=? u "-") (k-named-in-each (cdr xs) n) u)))))
(define k-syns-name? (->* (k-syns symbol) bool)
  (lambda (xs n)
    (and (not (null? xs))
         (or (and (syn-symbol? (car xs)) (symbol=? (syn-head (car xs)) n))
             (k-syns-name? (cdr xs) n)))))
(define k-all-names? (->* (k-syns) bool)
  (lambda (xs) (or (null? xs) (and (syn-symbol? (car xs)) (k-all-names? (cdr xs))))))
(define k-names-shown (->* (k-syns) string)
  (lambda (xs)
    (let ((n (symbol->string (syn-head (car xs)))))
      (if (null? (cdr xs)) n (k-cat3 n " " (k-names-shown (cdr xs)))))))
;; Where `m` last is among `names` (each a name, or `||` for none), from
;; `i`; or -1.
(define k-name-last (->* (k-names symbol int) int)
  (lambda (names m i)
    (if (null? names)
        -1
        (let ((later (k-name-last (cdr names) m (+ i 1))))
          (if (and (< later 0) (symbol=? (car names) m)) i later)))))
;; Of `found`, those that select from a parameter of `names`: each as
;; `(select $k x)`.
(define k-param-selects (->* (k-selects k-names) k-selects)
  (lambda (found names)
    (if (null? found)
        nil
        (let* ((m (extract (car found) 1)) (x (extract (car found) 2))
               (k (k-name-last names m 0))
               (rest (k-param-selects (cdr found) names)))
          (if (< k 0)
              rest
              (the k-selects (cons (product (1 m) (2 x) (3 (k-ty-new (ty-param k x)))) rest)))))))
(define k-all-unnamed? (->* (k-names) bool)
  (lambda (ns) (or (null? ns) (and (symbol=? (car ns) k-no-name) (k-all-unnamed? (cdr ns))))))

;; Kind `s`, or -1 where `k-parse-kind` would refuse it: for a reader that
;; gives its own message instead (`moduleof`'s `abs`).
(define k-try-kind (->* (syn) int)
  (lambda (s)
    (let ((n (if (syn-symbol? s) (syn-name s) "")))
      (case n (("region") 0)
              (("place") 3)
              (("effect") 1)
              (("type") 2)
              (("data") 4)
              (("sendable") 8)
              (("flat") 7)
              (("size") 5)
              (("conv") 6)
              (else
               (cond ((syn-symbol? s) -1)
                     (else (k-try-arrow-kind s))))))))
(define k-try-arrow-kind (->* (syn) int)
  (lambda (s)
    (let ((parts (k-arrow-syntax s)))
      (if (null? parts)
          -1
          (let* ((params (k-try-kinds (car (car parts))))
                 (result (k-try-kind (cdr (car parts)))))
            (cond ((or (k-has-id? params -1) (< result 0)) -1)
                  ((or (= result 0) (= result 3) (= result 5) (= result 6)) -1)
                  ((and (= result 1) (k-any-typed-kind? params)) -1)
                  (else (k-arrow params result))))))))
(define k-try-kinds (->* (k-syns) k-ids)
  (lambda (xs)
    (if (null? xs)
        nil
        (let* ((k (k-try-kind (car xs))) (rest (k-try-kinds (cdr xs))))
          (the k-ids (cons k rest))))))
;; An `abs`'s kind, `what`; or, `(abs (f (name kind) …) type)`, `(=> (kind
;; …) type)`.
(define k-abs-kind (->* (syn syn) int)
  (lambda (name what)
    (let ((ps (k-abs-ctor-params name)))
      (if (null? ps)
          (k-try-kind what)
          (let ((ks (k-try-kinds ps)))
            (if (or (k-has-id? ks -1) (not (= (k-try-kind what) 2)))
                (k-sfail k-abs-ctor-usage name)
                (k-arrow ks 2)))))))
;; Literal `k` at `a`..`b` checked against fixed-width integer type `b`:
;; whether `b` is one, refused, its range said, if `k` is out of it
;; (`Checker::literal_in_range`).
(define k-in-fixed-range? (->* (symbol int int int) bool)
  (lambda (t k a b)
    (let ((r (k-fixed-range (symbol->string t))))
      (cond ((null? r) #f)
            ((and (>= k (car (car r))) (<= k (cdr (car r)))) #t)
            (else (k-fail (k-cat5 (int->string k) " is not a " (symbol->string t)
                                  ": its range is "
                                  (k-cat3 (int->string (car (car r))) " to "
                                          (int->string (cdr (car r)))))
                          a b))))))
(define k-fixed-range
  (->* (string) (listof (pairof int int @t) acyclic))
  (lambda (n)
    (case n
      (("i8") (list (cons -128 127)))
      (("u8") (list (cons 0 255)))
      (("i32") (list (cons -2147483648 2147483647)))
      (("u32") (list (cons 0 4294967295)))
      (("i64") (list (cons -9223372036854775808 9223372036854775807)))
      (("u64") (list (cons 0 18446744073709551615)))
      (else nil))))
;; Whether `x`, at `a`..`b`, is an integer literal as the parsers write one
;; past a fixnum, checked against a fixed-width integer type, `expected`,
;; whose range it is in; refused if out of it (`Checker::literal_value`).
(define k-fixed-literal? (->* (kx int int int) bool)
  (lambda (x expected a b)
    (let ((v (k-literal-value x a b)))
      (and (not (null? v))
           (tagcase (k-get (k-resolve expected))
             (ty-base (t) (k-in-fixed-range? t (car v) a b))
             (else y #f))))))
;; The integer literal `x` is: a fixnum; or arithmetic on fixnums by the
;; standard `+`, `*` and `-`, every node spanning `a`..`b`, the literal
;; (the parser's `big-literal`), which no arithmetic written out does.
(define k-literal-value (->* (kx int int) (listof int acyclic))
  (lambda (x a b)
    (tagcase x
      (x-const (t n c d cdk cdkr) (if (and (= t k-int) (= c a) (= d b)) (list n) nil))
      (x-app (f args c d cdk cdkr)
        (if (and (= c a) (= d b) (= (k-length args) 2))
            (tagcase f
              (x-var (s fa fb fafbk fafbkr)
                (if (and (= fa a) (= fb b) (k-std-binding? s (k-lookup s)))
                    (k-literal-op (symbol->string s) (k-literal-value (car args) a b)
                                  (k-literal-value (car (cdr args)) a b))
                    nil))
              (else y nil))
            nil))
      (else y nil))))
(define k-literal-op
  (->* (string (listof int acyclic) (listof int acyclic)) (listof int acyclic))
  (lambda (op l r)
    (if (or (null? l) (null? r))
        nil
        (case op
          (("+") (list (+ (car l) (car r))))
          (("*") (list (* (car l) (car r))))
          (("-") (list (- (car l) (car r))))
          (else nil)))))
;; Whether `s` is written as a size, not a region (`Checker::size_written`):
;; a natural literal, `finite`, a size variable or value, `(+ …)`, `(- …)`.
(define k-size-written? (->* (syn) bool)
  (lambda (s)
    (cond ((>= (syn-int s) 0) #t)
          ((syn-symbol? s)
           (or (string=? (syn-name s) "finite")
               (let ((d (k-lookup-desc (syn-head s))))
                 (and (not (null? d))
                      (tagcase (car d) (ds-var (v k) (= k 5)) (ds-size (z) #t) (else x #f))))))
          (else
           (let ((items (tagcase s
                          (lst (items d a b xpn) items)
                          (else x (the k-syns nil)))))
             (and (not (null? items)) (syn-symbol? (car items))
                  (case (syn-name (car items)) (("+" "-") #t) (else #f))))))))
;; `(io k)`, `k` a kind of the fixed family (`TODO.md` §84).
(define k-io-atom (->* (syn k-syns) k-eff)
  (lambda (s items)
    (if (= (k-length items) 2)
        (let* ((x (k-nth items 1)) (k (if (syn-symbol? x) (k-io-kind-code (syn-name x)) -1)))
          (if (< k 0)
              (k-sfail (string-append "an I/O effect's kind is one of " k-io-kinds-shown) x)
              (k-one (a-io k))))
        (k-sfail (string-append "`(io kind)`, the kind one of " k-io-kinds-shown) s)))))))
