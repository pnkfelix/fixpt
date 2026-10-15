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
       (reader-types (load-module "fx26:reader-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-read (select check-read-types check-read-sig))
           (check-env (select check-env-types check-env-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (check-print (select check-print-types check-print-sig))
           (check-syntax (select check-syntax-types check-syntax-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (parser (select reader-types parser-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module

;; The types it uses of the files before it.
(hide (include check-types-types) (include check-read-types) (include check-env-types)
      (include check-subst-types) (include eager-reader-types) (include parser-types))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-syntax) (include check-print-parts) (include check-env)
      (include check-subst) (include check-print) (include parser))
(define k-atom-head? (with check-read k-atom-head?))
(define k-sfail (with check-read k-sfail))
(define k-items (with check-read k-items))
(define k-any-typed-kind? (with check-read k-any-typed-kind?))
(define k-arrow-syntax (with check-read k-arrow-syntax))
(define k-one (with check-effects k-one))
(define k-insert (with check-effects k-insert))

;; A `dlambda` of no parameters, as an error says.
(define k-dlambda-empty string "a `dlambda` takes at least one description")
(define k-moduleof-usage string "`(moduleof (abs t type) … (desc d type) … (val x type) …)`")
(define k-abs-usage string
  "an abstract component is a `type`, or a type constructor `(=> (kind …) type)`, for now")
(define k-abs-ctor-usage string "an abstract type constructor is `(abs (f (name kind) …) type)`")
;; What a list headed `hd` is not, read as a type: `hd` applied, if a name.
(define k-not-type-list (subr (read @globals) (symbol) string)
  (lambda (hd)
    (if (symbol=? hd '|()|)
        "expected a type"
        (string-append (k-quote (symbol->string hd)) " is not a description function"))))
;; The heads of the type forms a type is read from, and every keyword: no
;; parameter's name.
(define k-type-forms k-names
  (list 'arrayof 'narrayof 'bloblet 'composable 'dletrec 'icell 'listof 'mark-key 'moduleof 'mu
        'nat 'nlist 'pairof 'place 'poly 'productof 'prompt-tag 'proves 'ref 'select 'subr 'sumof
        'bool 'union))
;; Whether `hd` heads a type form: not a name a `with` shadows.
(define k-type-form? (subr (maxeff (read @globals) (read @t)) (symbol) bool)
  (lambda (hd) (k-has-name? k-type-forms hd)))
(define k-keywords k-names
  (list 'lambda 'plambda 'proj 'if 'letrec 'let 'begin 'define 'define* 'define-type
        'define-generative 'subr 'poly 'ref 'pairof 'dletrec 'void 'pure 'maxeff 'read 'write
        'alloc 'goto 'comefrom 'region 'effect 'type 'prompt 'prompt-tag 'composable 'mark-key
        'listof 'cond 'else 'and 'or 'let* 'define-effect 'module-parameters 'the 'bloblet 'fields
        'frozen 'arrayof 'icell 'await 'define-rec 'letrena 'letreap 'rlambda 'quote 'productof
        'sumof 'product 'extract 'sum 'tagcase 'module 'moduleof 'with 'select 'load-module
        'define-datatype 'make-bloblet 'bloblet-ref 'bloblet-set! 'bloblet-freeze 'bloblet-byte
        'bloblet-set-byte! 'bloblet-bytes 'rmake-bloblet 'dlambda '=> 'case
        'define-convention))
(define k-no-name symbol '||)
;; Whether effect `e` is variable `v` alone.
(define k-eff-is-var? (subr (read @globals) (k-eff int) bool)
  (lambda (e v)
    (and (not (null? e)) (null? (cdr e)) (tagcase (car e) (a-var (w) (= w v)) (else y #f)))))
;; Whether `d` is variable `v` and nothing more.
(define k-is-the-var? (subr (maxeff kreads spin) (k-desc int) bool)
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
(define k-the-vars? (subr (maxeff kreads spin) (k-descs k-binders) bool)
  (lambda (ds bs)
    (cond ((null? ds) (null? bs))
          ((null? bs) #f)
          ((k-is-the-var? (car ds) (extract (car bs) 1)) (k-the-vars? (cdr ds) (cdr bs)))
          (else #f))))
;; Whether `f` is one of `bs`'s variables.
(define k-param-head? (subr (maxeff kreads spin) (int k-binders) bool)
  (lambda (f bs) (tagcase (k-get f) (ty-var (v) (k-binder-has? bs v)) (else y #f))))
;; `(dlambda bs body)`, or, where `body` only applies a function to the
;; parameters in order, that function (eta).
(define k-lam (subr (maxeff kstate spin) (k-binders k-desc) int)
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
(define k-binders-as-descs (subr (maxeff kstate spin) (k-binders) k-descs)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((d (k-binder-desc (extract (car bs) 2) (extract (car bs) 1)))
               (rest (k-binders-as-descs (cdr bs))))
          (the k-descs (cons d rest))))))
;; "`f` takes n description(s), and has m", `f` shown.
(define k-fun-arity-message (subr kbuilds (int int int) string)
  (lambda (f want have)
    (k-cat5 (k-quote (k-show-ty f)) " takes " (int->string want)
            " description(s), and has " (int->string have))))
;; Binders of `kinds`, each a fresh variable named as `names`.
(define k-fresh-named (subr (maxeff kstate spin) (k-names k-ids) k-binders)
  (lambda (ns ks)
    (if (null? ns)
        nil
        (let* ((v (k-new-dvar-of (car ns) (car ks))) (rest (k-fresh-named (cdr ns) (cdr ks))))
          (the k-binders (cons (product (1 v) (2 (car ks))) rest))))))
;; Each binder, as a type family's parameter is bound to what it is given.
(define k-binders-as-scope (subr (maxeff kstate spin) (k-binders) k-scope)
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
(define k-ctor-type (subr (maxeff kstate spin) (string k-binders) int)
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
(define k-params-names (subr (read @globals) (k-params) k-names)
  (lambda (ps) (if (null? ps) nil (cons (extract (car ps) 1) (k-params-names (cdr ps))))))
(define k-params-kinds (subr (read @globals) (k-params) k-ids)
  (lambda (ps) (if (null? ps) nil (cons (extract (car ps) 2) (k-params-kinds (cdr ps))))))
;; Whether `n` is bound to a description function.
(define k-fun-bound? (subr (maxeff kreads (alloc @t)) (string) bool)
  (lambda (n)
    (let ((d (k-lookup-desc (string->symbol n))))
      (and (not (null? d))
           (tagcase (car d) (ds-var (v k) (k-arrow-kind? k)) (ds-fun (f) #t) (else y #f))))))
;; Binder `b`'s name.
(define k-binder-name (subr kreads ((productof (1 int) (2 int))) symbol)
  (lambda (b) (k-dvar-name (extract b 1))))
(define k-binder-names (subr (maxeff kreads spin) (k-binders) k-names)
  (lambda (bs) (if (null? bs) nil (cons (k-binder-name (car bs)) (k-binder-names (cdr bs))))))
;; `(select m t)`: as written, for checking to resolve where `m` is bound.
(define k-parse-select (subr (maxeff checks spin) (syn k-syns) int)
  (lambda (s items)
    (cond ((not (= (k-length items) 3)) (k-sfail "`(select module name)`" s))
          ((and (syn-symbol? (k-nth items 1)) (syn-symbol? (k-nth items 2)))
           (k-ty-new (ty-select (syn-head (k-nth items 1)) (syn-head (k-nth items 2)))))
          (else (k-sfail "`(select module name)`: a module's name, and a component's" s)))))
;; Function `f`, given `have` descriptions at `s`, where it takes `want`.
(define k-arity-fail (subr (maxeff checks spin) (int int int syn) void)
  (lambda (f want have s) (k-sfail (k-fun-arity-message f want have) s)))
;; Function `f`, at `s`, giving a `result` where a `wanted` is.
(define k-gives-fail (subr (maxeff checks spin) (int int string syn) void)
  (lambda (f result wanted s)
    (k-sfail (k-cat5 (k-quote (k-show-ty f)) " gives a description of kind " (k-kind-text result)
                     ", not " wanted)
             s)))
;; Function `f`, at `s`, not giving a `wanted`.
(define k-not-giving (subr (maxeff checks spin) (int string syn) void)
  (lambda (f wanted s) (k-sfail (k-cat3 (k-quote (k-show-ty f)) " does not give " wanted) s)))
;; A generative type as one.
(define k-gen-eta (subr (maxeff checks spin) (int k-binders) int)
  (lambda (g ps)
    (let* ((bs (k-fresh-named (k-binder-names ps) (k-binder-kinds ps)))
           (t (k-ty-new (ty-named g (k-binders-as-descs bs)))))
      (k-lam bs (dt t)))))
;; A type form, `listof` and kin, as one.
(define k-ctor-eta (subr (maxeff checks spin) (string k-params) int)
  (lambda (n ps)
    (let ((bs (k-fresh-named (k-params-names ps) (k-params-kinds ps))))
      (k-lam bs (dt (k-ctor-type n bs))))))
;; `ps` reversed, onto `acc`.
(define k-parts-reversed (subr (maxeff (read @globals) (alloc @t)) (k-parts k-parts) k-parts)
  (lambda (ps acc) (if (null? ps) acc (k-parts-reversed (cdr ps) (cons (car ps) acc)))))
;; The names among `xs`; what is not one is passed over.
(define k-syn-symbols (subr (maxeff (read @globals) (read @s) (alloc @t)) (k-syns) k-names)
  (lambda (xs)
    (cond ((null? xs) nil)
          ((syn-symbol? (car xs)) (cons (syn-head (car xs)) (k-syn-symbols (cdr xs))))
          (else (k-syn-symbols (cdr xs))))))
;; Whether every one of `xs` is a name.
(define k-all-symbols? (subr (read @s) (k-syns) bool)
  (lambda (xs) (or (null? xs) (and (syn-symbol? (car xs)) (k-all-symbols? (cdr xs))))))
;; `(abs (f (name kind) …) type)`'s parameters' kinds, unread, from `ps`; `name`
;; is said wrong if they are not.
(define k-ctor-param-kinds (subr (maxeff checks spin) (k-syns syn) k-syns)
  (lambda (ps name)
    (if (null? ps)
        nil
        (tagcase (car ps)
          (lst (items d a b)
            (if (and (= (k-length items) 2) (syn-symbol? (car items)))
                (cons (car (cdr items)) (k-ctor-param-kinds (cdr ps) name))
                (k-sfail k-abs-ctor-usage name)))
          (else x (k-sfail k-abs-ctor-usage name))))))
;; `(abs (f (name kind) …) type)`'s parameters' kinds, unread: `(abs f (=>
;; (kind …) type))`, as `define-generative` writes its parameters. None for
;; a name, or a list of names.
(define k-abs-ctor-params (subr (maxeff checks spin) (syn) k-syns)
  (lambda (name)
    (tagcase name
      (lst (items d a b)
        (cond ((k-all-symbols? items) nil)
              ((syn-symbol? (car items)) (k-ctor-param-kinds (cdr items) name))
              (else (k-sfail k-abs-ctor-usage name))))
      (else x nil))))
;; A component's names: its name; or, an `abs`'s, the names in a list.
(define k-component-names (subr (maxeff checks spin) (syn string) k-names)
  (lambda (name head)
    (if (syn-symbol? name)
        (the k-names (cons (syn-head name) nil))
        (tagcase name
          (lst (items d a b)
            (cond ((not (string=? head "abs")) (k-sfail "a component's name" name))
                  ((k-all-symbols? items) (k-syn-symbols items))
                  ;; One constructor, its parameters' kinds given.
                  (else (begin (k-abs-ctor-params name) (cons (syn-head (car items)) nil)))))
          (else x (k-sfail "a component's name" name))))))
;; `seen` and `names`, each named once in component `c`.
(define k-names-once (subr (maxeff checks spin) (k-names k-names syn) k-names)
  (lambda (names seen c)
    (cond ((null? names) seen)
          ((k-has-name? seen (car names)) (k-sfail (k-twice (symbol->string (car names))) c))
          (else (k-names-once (cdr names) (cons (car names) seen) c)))))
;; Abstract types `names`, each a variable of kind `k`, in scope from here,
;; onto `abs`; a type constructor among `k-abstract-funs`.
(define k-abs-bound (subr (maxeff kstate spin) (k-names int k-parts) k-parts)
  (lambda (names k abs)
    (if (null? names)
        abs
        (let* ((n (car names)) (v (k-new-dvar-of n k)))
          (begin (if (= k 2) #u (set k-abstract-funs (cons v (get k-abstract-funs))))
                 (k-push-desc n (ds-var v k))
                 (k-abs-bound (cdr names) k (cons (product (1 n) (2 v)) abs)))))))
;; `(name type)` onto `ps`.
(define k-part-onto (subr (alloc @t) (symbol int k-parts) k-parts)
  (lambda (n t ps) (cons (product (1 n) (2 t)) ps)))
;; Whether `s` is written as an effect: `pure`, `spin`, a name bound to one,
;; or one of `k-parse-effect`'s atoms or `maxeff`.
(define k-effect-shaped? (subr (maxeff kreads (read @s) (alloc @t) spin) (syn) bool)
  (lambda (s)
    (if (syn-symbol? s)
        (let ((n (syn-name s)))
          (or (string=? n "pure") (string=? n "spin") (string=? n "nondet")
              (let ((d (k-lookup-desc (string->symbol n))))
                (and (not (null? d))
                     (tagcase (car d) (ds-eff (e) #t) (ds-var (v k) (= k 1)) (else x #f))))))
        (let ((h (k-list-head s))) (or (k-atom-head? h) (string=? h "maxeff"))))))
;; The types of parts `ps`, onto `tail`.
(define k-parts-onto (subr (maxeff (read @globals) (alloc @t)) (k-parts k-ids) k-ids)
  (lambda (ps tail)
    (if (null? ps) tail (cons (extract (car ps) 2) (k-parts-onto (cdr ps) tail)))))
;; `ts`, and `t` after them.
(define k-ids-then (subr (maxeff (read @globals) (alloc @t)) (k-ids int) k-ids)
  (lambda (ts t) (if (null? ts) (cons t nil) (cons (car ts) (k-ids-then (cdr ts) t)))))
;; The types and functions among descriptions `ds`.
(define k-desc-kids (subr (maxeff (read @globals) (alloc @t)) (k-descs) k-ids)
  (lambda (ds)
    (if (null? ds)
        nil
        (let ((rest (k-desc-kids (cdr ds))))
          (tagcase (car ds) (dt (x) (cons x rest)) (df (x) (cons x rest)) (else y rest))))))
;; The types `t` is made of, one level down.
(define k-ty-kids (subr (maxeff kmakes spin) (int) k-ids)
  (lambda (t)
    (tagcase (k-get t)
      (ty-subr (e ps r cv) (k-ids-then ps r))
      (ty-poly (bs x) (the k-ids (cons x nil)))
      (ty-ref (a r) (the k-ids (cons a nil)))
      (ty-array (a nz r) (the k-ids (cons a nil)))
      (ty-icell (a r) (the k-ids (cons a nil)))
      (ty-markkey (a r) (the k-ids (cons a nil)))
      (ty-pair (a d r nl) (k-ids-then (the k-ids (cons a nil)) d))
      (ty-tag (a h e r) (k-ids-then (the k-ids (cons a nil)) h))
      (ty-comp (x a e r) (k-ids-then (the k-ids (cons x nil)) a))
      (ty-product (ps) (k-parts-onto ps nil))
      (ty-sum (ps) (k-parts-onto ps nil))
      (ty-bloblet (fs z r) fs)
      (ty-union (ms) ms)
      (ty-named (g ds) (k-desc-kids ds))
      (ty-app (f ds) (the k-ids (cons f (k-desc-kids ds))))
      (ty-lam (bs x) (k-desc-kids (the k-descs (cons x nil))))
      (ty-nlist (e z r) (the k-ids (cons e nil)))
      (ty-module (abs ds vs) (k-parts-onto ds (k-parts-onto vs nil)))
      (else y nil))))
;; `ss` reversed, onto `acc`.
(define k-selects-reversed
  (subr (maxeff (read @globals) (alloc @t)) (k-selects k-selects) k-selects)
  (lambda (ss acc) (if (null? ss) acc (k-selects-reversed (cdr ss) (cons (car ss) acc)))))
;; A procedure type's parameter written `(name type)`, where `name` names no
;; type or type form: its name, in a list of one; none if it is not one.
(define k-param-name (subr (maxeff kreads (alloc @t) (read @s) spin) (syn) k-names)
  (lambda (p)
    (tagcase p
      (lst (items d a b)
        (if (and (= (k-length items) 2) (syn-symbol? (car items)))
            (let ((n (syn-head (car items))))
              (if (or (k-has-name? k-type-forms n) (k-has-name? k-keywords n)
                      (not (null? (k-lookup-desc n))) (>= (k-find (get k-base) n) 0))
                  nil
                  (the k-names (cons n nil))))
            nil))
      (else x nil))))
;; Where `m` last is among `names` (each a name, or `||` for none), from
;; `i`; or -1.
(define k-name-last (subr (maxeff kreads spin) (k-names symbol int) int)
  (lambda (names m i)
    (if (null? names)
        -1
        (let ((later (k-name-last (cdr names) m (+ i 1))))
          (if (and (< later 0) (symbol=? (car names) m)) i later)))))
;; Of `found`, those that select from a parameter of `names`: each as
;; `(select $k x)`.
(define k-param-selects (subr (maxeff kstate spin) (k-selects k-names) k-selects)
  (lambda (found names)
    (if (null? found)
        nil
        (let* ((m (extract (car found) 1)) (x (extract (car found) 2))
               (k (k-name-last names m 0))
               (rest (k-param-selects (cdr found) names)))
          (if (< k 0)
              rest
              (the k-selects (cons (product (1 m) (2 x) (3 (k-ty-new (ty-param k x)))) rest)))))))
(define k-all-unnamed? (subr (maxeff (read @globals) spin) (k-names) bool)
  (lambda (ns) (or (null? ns) (and (symbol=? (car ns) k-no-name) (k-all-unnamed? (cdr ns))))))

;; A flat (`TODO.md` §77): the scalars' names, whose bytes a `blobref`
;; reads as a value of the type of the same name.
(define k-flat-scalar? (subr (read @globals) (symbol) bool)
  (lambda (s)
    (or (symbol=? s 'f64) (symbol=? s 'f32) (symbol=? s 'i32) (symbol=? s 'u32)
        (symbol=? s 'i64) (symbol=? s 'u64))))
(define k-flat-usage string
  (string-append "a flat is `f64`, `f32`, `i32`, `u32`, `i64`, `u64`, "
                 (k-cat3 "`(productof (label flat) …)`, `(sumof [key] (label flat) …)`, "
                         "`(arrayof flat n)`, " "or a variable of kind `flat`")))
;; What a flat named `n` where a type is wanted is told.
(define k-flat-not-type (subr (read @globals) (string) string)
  (lambda (n) (string-append "`" n "` is a flat, not a type")))
;; Whether `t` is a variable of kind `flat`.
(define k-flat-var-type? (subr (maxeff kreads spin) (int) bool)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-var (v) (k-flat-var? v)) (else y #f))))
;; Whether `t` is a flat: a scalar, or a variable of kind `flat`.
(define k-is-flat? (subr (maxeff kreads spin) (int) bool)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-base (s) (k-flat-scalar? s))
      (ty-var (v) (k-flat-var? v))
      (ty-product (ps) (k-flat-parts? ps))
      (ty-sum (ps) (k-flat-parts? ps))
      (ty-named (g ds) (or (= g k-flat-arrayof-gen) (= g k-flat-keyed-gen)))
      (else y #f))))
(define k-flat-parts? (subr (maxeff kreads spin) (k-parts) bool)
  (lambda (ps) (or (null? ps) (and (k-is-flat? (extract (car ps) 2)) (k-flat-parts? (cdr ps))))))
;; A flat, as written (`Checker::parse_flat`): a scalar's name, as the type
;; its bytes are read as; or a variable of kind `flat`, or a family's flat
;; parameter.
(define k-parse-flat (subr (maxeff checks spin) (syn) int)
  (lambda (s)
    (if (not (null? (k-list-items s)))
        (k-parse-flat-list s (k-list-items s))
    (if (syn-symbol? s)
        (let* ((sym (syn-head s)) (d (k-lookup-desc sym)))
          (if (null? d)
              (if (k-flat-scalar? sym) (k-ty-new (ty-base sym)) (k-sfail k-flat-usage s))
              (tagcase (car d)
                (ds-var (v k) (if (= k 7) (k-ty-new (ty-var v)) (k-sfail k-flat-usage s)))
                ;; A type named, read as a flat: its parts as `productof` and
                ;; `sumof` would have them (`TODO.md` §77).
                (ds-rec (t)
                  (if (k-is-flat? t)
                      (let ((why (k-flat-parts-wrong t))) (if (string=? why "") t (k-sfail why s)))
                      (k-sfail k-flat-usage s)))
                (else x (k-sfail k-flat-usage s)))))
        (k-sfail k-flat-usage s)))))
;; A list's items, or none for what is no list (or an empty one).
(define k-list-items (subr (read @s) (syn) k-syns)
  (lambda (s) (tagcase s (lst (items d a b) items) (else x nil))))
;; `(productof (label flat) …)`, its fields laid out in the order written;
;; or `(arrayof flat n)`, `n` a literal length (`Checker::parse_flat_list`).
(define k-parse-flat-list (subr (maxeff checks spin) (syn k-syns) int)
  (lambda (s items)
    (let ((hd (if (syn-symbol? (car items)) (syn-name (car items)) "")))
      (cond ((string=? hd "productof")
             (let* ((parts (k-parse-flat-parts (cdr items) nil 0))
                    (bad (k-unsized-before-last parts (cdr items) nil)))
               (if (null? bad)
                   (k-ty-new (ty-product parts))
                   (k-sfail (string-append "only a flat product's last part may be of a length not "
                                           "known: it runs to the end of the suffix")
                            (car bad)))))
            ((string=? hd "sumof") (k-parse-flat-sum (cdr items)))
            ;; A length a literal; or a size, which runs to the end of the
            ;; suffix (`TODO.md` §77).
            ((and (string=? hd "arrayof") (= (k-length items) 3))
             (let ((f (k-parse-flat (k-nth items 1))) (n (k-nth items 2)))
               (if (not (k-flat-sized? f))
                   (k-sfail "a flat array's element has a length of its own" (k-nth items 1))
                   (let ((z (k-parse-size n)))
                     (if (tagcase z
                           (sz-lin (k ts) (and (null? ts) (or (< k 0) (>= k 268435455))))
                           (else y #f))
                         (k-sfail "a flat array's literal length is 0 to 268435454" n)
                         (k-ty-new (ty-named k-flat-arrayof-gen (list (dt f) (dz z)))))))))
            (else (k-sfail k-flat-usage s))))))
(define k-parse-flat-parts (subr (maxeff checks spin) (k-syns k-parts int) k-parts)
  (lambda (ps done w)
    (if (null? ps)
        (reverse done)
        (let ((pair (k-items (car ps) "`(label flat)`")))
          (if (= (k-length pair) 2)
              (let ((l (k-syn-label (car pair))))
                (cond ((k-has-label? done l) (k-sfail (k-twice (symbol->string l)) (car ps)))
                      ((and (> w 0) (not (k-digits-below? (symbol->string l) 0 0 (k-key-limit w))))
                       (k-sfail (k-cat5 "a label of a sum keyed by `u" (int->string (* 8 w))
                                        "` is a number below 2^" (int->string (* 8 w)) "")
                                (car pair)))
                      (else
                       (let ((f (k-parse-flat (k-nth pair 1))))
                         (k-parse-flat-parts (cdr ps) (cons (product (1 l) (2 f)) done) w)))))
              (k-sfail "`(label flat)`" (car ps)))))))
;; `(sumof [key] (label flat) …)`: a key first, a width, if the labels are numbers stored as they
;; are; else the tag indexes the owner's fields, which hold the labels (`TODO.md` §77).
(define k-parse-flat-sum (subr (maxeff checks spin) (k-syns) int)
  (lambda (ps)
    (let* ((w (if (and (not (null? ps)) (syn-symbol? (car ps))) (k-key-width (car ps)) 0))
           (written (if (= w 0) ps (cdr ps)))
           (parts (k-parse-flat-parts written nil w))
           (bad (k-unsized-first parts written)))
      (cond ((not (null? bad)) (k-sfail "a flat sum's variant has a length of its own" (car bad)))
            ((= w 0) (k-ty-new (ty-sum parts)))
            (else
             (k-ty-new (ty-named k-flat-keyed-gen
                                 (list (dz (k-size-lit w)) (dt (k-ty-new (ty-sum parts)))))))))))
;; What is wrong with flat `t`'s parts, "" if nothing (`Checker::flat_parts_wrong`).
(define k-flat-parts-wrong (subr (maxeff kreads (alloc @t) spin) (int) string)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-product (ps)
        (if (k-unsized-before-last? ps)
            (string-append "only a flat product's last part may be of a length not known: it runs "
                           "to the end of the suffix")
            ""))
      (ty-sum (ps) (if (k-any-unsized? ps) "a flat sum's variant has a length of its own" ""))
      (else y ""))))
(define k-unsized-before-last? (subr (maxeff kreads (alloc @t) spin) (k-parts) bool)
  (lambda (ps)
    (and (not (null? ps)) (not (null? (cdr ps)))
         (or (not (k-flat-sized? (extract (car ps) 2))) (k-unsized-before-last? (cdr ps))))))
(define k-any-unsized? (subr (maxeff kreads (alloc @t) spin) (k-parts) bool)
  (lambda (ps)
    (and (not (null? ps))
         (or (not (k-flat-sized? (extract (car ps) 2))) (k-any-unsized? (cdr ps))))))
;; The first of `parts`, written `ps`, of a length not known: its syntax.
(define k-unsized-first (subr (maxeff kreads (alloc @t) spin) (k-parts k-syns) k-syns)
  (lambda (parts ps)
    (cond ((null? parts) nil)
          ((not (k-flat-sized? (extract (car parts) 2))) (the k-syns (cons (car ps) nil)))
          (else (k-unsized-first (cdr parts) (cdr ps))))))
;; The last of `parts` before the last, written `ps`, of a length not known,
;; `found` so far: its syntax.
(define k-unsized-before-last
  (subr (maxeff kreads (alloc @t) spin) (k-parts k-syns k-syns) k-syns)
  (lambda (parts ps found)
    (cond ((or (null? parts) (null? (cdr parts))) found)
          ((not (k-flat-sized? (extract (car parts) 2)))
           (k-unsized-before-last (cdr parts) (cdr ps) (the k-syns (cons (car ps) nil))))
          (else (k-unsized-before-last (cdr parts) (cdr ps) found)))))
(define k-key-width (subr (maxeff checks spin) (syn) int)
  (lambda (k)
    (case (syn-name k)
      (("u8") 1) (("u16") 2) (("u32") 4)
      (else (k-sfail "a flat sum's key is `u8`, `u16` or `u32`" k)))))
(define k-key-limit (subr (read @globals) (int) int)
  (lambda (w) (case w ((1) 256) ((2) 65536) (else 4294967296))))
;; Whether `s` from `i` is a number's digits, `n` so far, below `limit`.
(define k-digits-below? (subr (maxeff (read @globals) spin) (string int int int) bool)
  (lambda (s i n limit)
    (cond ((>= n limit) #f)
          ((= i (string-length s)) (> i 0))
          ((and (char>=? (string-ref s i) #\0) (char<=? (string-ref s i) #\9))
           (k-digits-below? s (+ i 1) (+ (* n 10) (- (char->integer (string-ref s i)) 48)) limit))
          (else #f))))

;; `blobref`, standard generative type 5 (`check::BLOBREF_INDEX`); a flat
;; array, 6 (`check::FLAT_ARRAYOF_INDEX`); a flat sum with a key, 7.
(define k-blobref-gen int 5)
(define k-flat-arrayof-gen int 6)
(define k-flat-keyed-gen int 7)
;; A scalar flat's layout (`fixpt_heap::layout::FLAT_*`), or -1.
(define k-flat-code (subr (read @globals) (symbol) int)
  (lambda (s)
    (case (symbol->string s)
      (("i32") 0) (("u32") 1) (("i64") 2) (("u64") 3) (("f32") 4) (("f64") 5) (else -1))))
(define-type k-int-pair (pairof int int @t))
;; `n` rounded up to a multiple of `a`.
(define k-round-up (subr pure (int int) int)
  (lambda (n a) (* (quotient (+ n (- a 1)) a) a)))
;; A flat's size and alignment in bytes (`Checker::flat_layout`); -1s for
;; one whose layout is not known.
(define k-flat-layout (subr (maxeff kreads (alloc @t) spin) (int) k-int-pair)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-base (s)
        (case (symbol->string s)
          (("i32" "u32" "f32") (cons 4 4)) (("i64" "u64" "f64") (cons 8 8)) (else (cons -1 -1))))
      (ty-product (ps) (k-flat-parts-layout ps 0 1))
      (ty-sum (ps) (k-flat-sum-size t))
      (ty-named (g ds)
        (let ((p (k-flat-array-parts t)))
          (if (= g k-flat-keyed-gen)
              (k-flat-sum-size t)
          (if (or (< (car p) 0) (not (k-flat-sized? t)))
              (cons -1 -1)
              (let ((e (k-flat-layout (car p))))
                (if (< (car e) 0) e (cons (* (car e) (cdr p)) (cdr e))))))))
      (else y (cons -1 -1)))))
(define k-flat-parts-layout (subr (maxeff kreads (alloc @t) spin) (k-parts int int) k-int-pair)
  (lambda (ps at align)
    (if (null? ps)
        (cons (k-round-up at align) align)
        (let ((l (k-flat-layout (extract (car ps) 2))))
          (if (< (car l) 0)
              l
              (k-flat-parts-layout (cdr ps) (+ (k-round-up at (cdr l)) (car l))
                                   (if (> (cdr l) align) (cdr l) align)))))))
;; Flat product `t`'s field `l`: its offset in bytes, and its flat; -1s if
;; none (`Checker::flat_field`).
(define k-flat-field (subr (maxeff kreads (alloc @t) spin) (int symbol) k-int-pair)
  (lambda (t l)
    (tagcase (k-get (k-resolve t))
      (ty-product (ps) (k-flat-field-from ps l 0))
      (else y (cons -1 -1)))))
(define k-flat-field-from (subr (maxeff kreads (alloc @t) spin) (k-parts symbol int) k-int-pair)
  (lambda (ps l at)
    (if (null? ps)
        (cons -1 -1)
        (let ((a (k-flat-align (extract (car ps) 2))))
          (cond ((< a 0) (cons -1 -1))
                ;; The last may be of a length not known: its offset is not.
                ((symbol=? (extract (car ps) 1) l) (cons (k-round-up at a) (extract (car ps) 2)))
                (else
                 (let ((e (k-flat-layout (extract (car ps) 2))))
                   (if (< (car e) 0)
                       (cons -1 -1)
                       (k-flat-field-from (cdr ps) l (+ (k-round-up at a) (car e)))))))))))
;; A flat's alignment in bytes, known whether or not its size is; -1 if not
;; known (`Checker::flat_align`).
(define k-flat-align (subr (maxeff kreads (alloc @t) spin) (int) int)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-product (ps) (k-parts-align ps 1))
      (ty-named (g ds)
        (if (= g k-flat-arrayof-gen)
            (let ((p (k-flat-array-parts t))) (if (< (car p) 0) -1 (k-flat-align (car p))))
            (cdr (k-flat-layout t))))
      (else y (cdr (k-flat-layout t))))))
(define k-parts-align (subr (maxeff kreads (alloc @t) spin) (k-parts int) int)
  (lambda (ps a)
    (if (null? ps)
        a
        (let ((b (k-flat-align (extract (car ps) 2))))
          (if (< b 0) -1 (k-parts-align (cdr ps) (if (> b a) b a)))))))
;; The length of the array of a length not known that flat `t` is, or ends
;; in: none if `t` has a size of its own (`TODO.md` §77).
(define k-unsized-length (subr (maxeff kreads (alloc @t) spin) (int) (listof k-size acyclic))
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-named (g ds)
        (if (and (= g k-flat-arrayof-gen) (= (k-length ds) 2))
            (tagcase (car (cdr ds))
              (dz (z) (tagcase z
                        (sz-lin (k ts) (if (null? ts) nil (the (listof k-size acyclic) (list z))))
                        (else y (the (listof k-size acyclic) (list z)))))
              (else y nil))
            nil))
      (ty-product (ps) (if (null? ps) nil (k-unsized-length (extract (k-last-part ps) 2))))
      (else y nil))))
(define k-last-part (subr (read @globals) (k-parts) (productof (1 symbol) (2 int)))
  (lambda (ps) (if (null? (cdr ps)) (car ps) (k-last-part (cdr ps)))))
(define k-flat-sized? (subr (maxeff kreads (alloc @t) spin) (int) bool)
  (lambda (t) (null? (k-unsized-length t))))
;; Flat `t` with the length of the array of a length not known that it is,
;; or ends in, `z`.
(define k-with-unsized-length (subr (maxeff kstate spin) (int k-size) int)
  (lambda (t z)
    (tagcase (k-get (k-resolve t))
      (ty-named (g ds)
        (tagcase (car ds)
          (dt (f) (k-ty-new (ty-named k-flat-arrayof-gen (list (dt f) (dz z)))))
          (else y t)))
      (ty-product (ps) (k-ty-new (ty-product (k-with-last-part ps z))))
      (else y t))))
(define k-with-last-part (subr (maxeff kstate spin) (k-parts k-size) k-parts)
  (lambda (ps z)
    (if (null? (cdr ps))
        (the k-parts
             (list (product (1 (extract (car ps) 1))
                            (2 (k-with-unsized-length (extract (car ps) 2) z)))))
        (cons (car ps) (k-with-last-part (cdr ps) z)))))
;; Flat array `t`'s element and length, 268435455 (`FLAT_TO_THE_END`) for
;; one that runs to the end of the suffix; -1s if it is none.
(define k-flat-array-parts (subr (maxeff kreads (alloc @t) spin) (int) k-int-pair)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-named (g ds)
        (if (and (= g k-flat-arrayof-gen) (= (k-length ds) 2))
            (tagcase (car ds)
              (dt (f)
                (tagcase (car (cdr ds))
                  (dz (z) (tagcase z (sz-lin (k ts) (if (null? ts) (cons f k) (cons f 268435455)))
                            (else y (cons f 268435455))))
                  (else y (cons -1 -1))))
              (else y (cons -1 -1)))
            (cons -1 -1)))
      (else y (cons -1 -1)))))
;; A flat sum's variants, its key's width in bytes (-1 if `t` is no flat
;; sum), and whether its labels are numbers (`Checker::flat_sum_parts`).
(define-type k-sum-parts (productof (1 k-parts) (2 int) (3 bool)))
(define k-no-sum k-sum-parts (product (1 (the k-parts nil)) (2 -1) (3 #f)))
(define k-flat-sum-parts (subr (maxeff kreads (alloc @t) spin) (int) k-sum-parts)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-sum (ps) (if (k-flat-parts? ps) (product (1 ps) (2 1) (3 #f)) k-no-sum))
      (ty-named (g ds)
        (if (and (= g k-flat-keyed-gen) (= (k-length ds) 2))
            (tagcase (car ds)
              (dz (z)
                (tagcase z
                  (sz-lin (k ts)
                    (tagcase (car (cdr ds))
                      (dt (s) (tagcase (k-get (k-resolve s))
                                (ty-sum (ps) (product (1 ps) (2 k) (3 #t)))
                                (else y k-no-sum)))
                      (else y k-no-sum)))
                  (else y k-no-sum)))
              (else y k-no-sum))
            k-no-sum))
      (else y k-no-sum))))
;; A flat sum's code for the compilers, size, alignment and variants
;; (`Checker::flat_sum_layout`): the tag, `w` bytes, then the variant at the
;; widest one's alignment, at `p`; the code `w + 8 * numeric + 256 * p`, or
;; -1 if `t` is no flat sum or its layout is not known.
(define-type k-sum-layout (productof (1 int) (2 int) (3 int) (4 k-parts)))
(define k-no-layout k-sum-layout (product (1 -1) (2 -1) (3 -1) (4 (the k-parts nil))))
(define k-flat-sum-layout (subr (maxeff kreads (alloc @t) spin) (int) k-sum-layout)
  (lambda (t)
    (let ((p (k-flat-sum-parts t)))
      (if (< (extract p 2) 0)
          k-no-layout
          (k-sum-layout-of (extract p 1) (extract p 2) (extract p 3) (extract p 1) 0 1)))))
(define k-sum-layout-of
  (subr (maxeff kreads (alloc @t) spin) (k-parts int bool k-parts int int) k-sum-layout)
  (lambda (ps w numeric all size align)
    (if (null? ps)
        (let ((p (k-round-up w align)) (al (if (> w align) w align)))
          (product (1 (+ (+ w (if numeric 8 0)) (* 256 p))) (2 (k-round-up (+ p size) al)) (3 al)
                   (4 all)))
        (let ((l (k-flat-layout (extract (car ps) 2))))
          (if (< (car l) 0)
              k-no-layout
              (k-sum-layout-of (cdr ps) w numeric all (if (> (car l) size) (car l) size)
                               (if (> (cdr l) align) (cdr l) align)))))))
(define k-flat-sum-size (subr (maxeff kreads (alloc @t) spin) (int) k-int-pair)
  (lambda (t)
    (let ((l (k-flat-sum-layout t)))
      (if (< (extract l 1) 0) (cons -1 -1) (cons (extract l 2) (extract l 3))))))
;; A `tagcase`, `at`, whose scrutinee is of type and effect `rs`: if a
;; blobref to a flat sum (`TODO.md` §77), seen as a sum of blobrefs to its
;; variants, its tag read from the owner's region, and its layout's code
;; noted for the compilers; else `rs`.
(define k-flat-view (subr (maxeff checks spin) (k-at k-te) k-te)
  (lambda (at rs)
    (let* ((st (extract rs 1)) (p (k-blobref-parts st))
           (l (if (null? p) k-no-layout (k-flat-sum-layout (cdr (car p))))))
      (if (< (extract l 1) 0)
          rs
          (let* ((b (car (car p))) (r (k-owner-region (extract at 1) (extract at 2) st b)))
            (begin
              (set k-extracts (cons (product (1 at) (2 (extract l 1))) (get k-extracts)))
              (k-te (k-ty-new (ty-sum (k-blobref-variants b (extract l 4))))
                    (k-insert (a-read r) (extract rs 2)))))))))
(define k-blobref-variants (subr (maxeff kstate spin) (int k-parts) k-parts)
  (lambda (b ps)
    (if (null? ps)
        nil
        (let* ((v (product (1 (extract (car ps) 1)) (2 (k-blobref-of b (extract (car ps) 2)))))
               (rest (k-blobref-variants b (cdr ps))))
          (the k-parts (cons v rest))))))
;; What a `tagcase`'s `else` binds, its scrutinee of type `st`, the variants
;; `rest` not named: the blobref as it is, to a flat sum; else their sum.
(define k-else-type (subr (maxeff kstate spin) (int k-parts) int)
  (lambda (st rest)
    (let ((p (k-blobref-parts st)))
      (if (and (not (null? p)) (>= (extract (k-flat-sum-layout (cdr (car p))) 1) 0))
          st
          (k-ty-new (ty-sum rest))))))
;; The region of blobref type `xt`'s owner, `b`, at `a`..`z`.
(define k-owner-region (subr (maxeff checks spin) (int int int int) k-region)
  (lambda (a z xt b)
    (tagcase (k-get (k-resolve b))
      (ty-bloblet (fs fz r) r)
      (else y (k-fail (k-cat3 "the region of a " (k-show-ty xt) "'s owner is not known") a z)))))
;; `body`'s type and effect with `y` bound to `t`, by `synth-as` (the
;; checker's knot), against `expected` if given (≥ 0).
(define-type k-synth-as-knot (subr (maxeff checks spin) (kx int) k-te))
(define k-in-scope-check (subr (maxeff checks spin) (symbol int kx int k-synth-as-knot) k-te)
  (lambda (y t body expected synth-as)
    (let ((saved (k-mark)))
      (begin
        (k-bind y t)
        (let ((r (synth-as body expected)))
          (begin (k-unbind-to saved) r))))))
;; `body`, at `ba`..`bb`, its type and effect with `ps` bound, the first
;; first, by `synth-as` (the checker's knot), against `expected` if given
;; (≥ 0): a `with`'s body, at `a`..`b`, of which an error at the body is
;; said, so that a call's argument's is the argument's (`Checker::with_as`).
(define k-in-scope-parts
  (subr (maxeff checks spin) (k-parts kx int k-synth-as-knot int int int int) k-te)
  (lambda (ps body expected synth-as a b ba bb)
    (let ((saved (k-mark)))
      (begin
        (k-bind-each ps)
        (let ((r (if (< expected 0)
                     (synth-as body expected)
                     (k-respanning (lambda () (synth-as body expected)) ba bb a b))))
          (begin (k-unbind-to saved) r))))))
;; `f`, an error at `a`..`b` said at `ta`..`tb` instead, any other as it is.
(define k-respanning
  (subr (maxeff checks spin) ((subr (maxeff checks spin) () k-te) int int int int) k-te)
  (lambda (f a b ta tb)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb) (if (and (= ea a) (= eb b)) (k-fail m ta tb) (k-fail m ea eb)))
        (k-ok (xs) (k-fail "k-ok inside" a b))))))
(define k-bind-each (subr (maxeff kstate spin) (k-parts) unit)
  (lambda (ps)
    (if (null? ps)
        #u
        (begin (k-bind (extract (car ps) 1) (extract (car ps) 2)) (k-bind-each (cdr ps))))))
;; `blobref-variant!` at `a`..`z` of the flat sum `f` a blobref of type `xt`
;; and owner `b` points to, its label `lx` at `la`..`lz`: a blobref to the
;; variant, of effect `e` and the owner's region read and written; the
;; layout's code noted for the compilers (`Checker::synth_blobref`).
(define k-blobref-variant
  (subr (maxeff checks spin) (int int int int int int kx int int k-eff) k-te)
  (lambda (a z k xt b f lx la lz e)
    (let* ((l (k-flat-sum-layout f)) (code (extract l 1)) (label (k-variant-label lx code)))
      (if (null? label)
          (k-fail (string-append "a variant is named by a literal: `'label`, or a number where "
                                 "the sum has a key")
                  la lz)
          (let ((g (k-variant-find (extract l 4) (car label))))
            (if (< g 0)
                (k-fail (k-cat5 "a " (k-show-ty f) " has no variant `" (symbol->string (car label))
                                "`")
                        la lz)
                (let ((r (k-owner-region a z xt b)))
                  (begin
                    (set k-extracts
                         (cons (product (1 (product (1 a) (2 z) (3 k))) (2 code))
                               (get k-extracts)))
                    (k-te (k-blobref-of b g) (k-insert (a-write r) (k-insert (a-read r) e)))))))))))
;; A `blobref-variant!`'s label, `lx`, for a sum of layout `code`: a number
;; where the sum has a key, else a name, as `check-modules-read.fx`'s
;; `k-label-const` resolves it (its value -1, its name the type's); none if
;; it is neither.
(define k-variant-label (subr (maxeff kreads spin) (kx int) (listof symbol acyclic))
  (lambda (lx code)
    (tagcase lx
      (x-const (t n c d cdk)
        (cond ((= (modulo (quotient code 8) 2) 1)
               (if (= t k-int) (list (string->symbol (int->string n))) nil))
              ((or (= t k-int) (not (= n -1))) nil)
              (else (tagcase (k-get t) (ty-base (s) (list s)) (else y nil)))))
      (else y nil))))
(define k-variant-find (subr (maxeff (read @globals) spin) (k-parts symbol) int)
  (lambda (ps l)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) l) (extract (car ps) 2))
          (else (k-variant-find (cdr ps) l)))))
;; `(blobref b f)`'s owner and flat, if `t` is one.
(define-type k-owner-flat (listof (pairof int int @t) acyclic))
(define k-blobref-parts (subr (maxeff kreads (alloc @t) spin) (int) k-owner-flat)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-named (g ds)
        (if (and (= g k-blobref-gen) (= (k-length ds) 2))
            (tagcase (car ds)
              (dt (b) (tagcase (car (cdr ds)) (dt (f) (list (cons b f))) (else y nil)))
              (else y nil))
            nil))
      (else y nil))))
(define k-blobref-of (subr (maxeff kstate spin) (int int) int)
  (lambda (b f) (k-ty-new (ty-named k-blobref-gen (list (dt b) (dt f))))))
;; Kind `s`, or -1 where `k-parse-kind` would refuse it: for a reader that
;; gives its own message instead (`moduleof`'s `abs`).
(define k-try-kind (subr (maxeff kstate (read @s) spin) (syn) int)
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
(define k-try-arrow-kind (subr (maxeff kstate (read @s) spin) (syn) int)
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
(define k-try-kinds (subr (maxeff kstate (read @s) spin) (k-syns) k-ids)
  (lambda (xs)
    (if (null? xs)
        nil
        (let* ((k (k-try-kind (car xs))) (rest (k-try-kinds (cdr xs))))
          (the k-ids (cons k rest))))))
;; An `abs`'s kind, `what`; or, `(abs (f (name kind) …) type)`, `(=> (kind
;; …) type)`.
(define k-abs-kind (subr (maxeff checks spin) (syn syn) int)
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
(define k-in-fixed-range? (subr (maxeff checks spin) (symbol int int int) bool)
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
  (subr (maxeff (read @globals) (alloc @t)) (string) (listof (pairof int int @t) acyclic))
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
(define k-fixed-literal? (subr (maxeff checks spin) (kx int int int) bool)
  (lambda (x expected a b)
    (let ((v (k-literal-value x a b)))
      (and (not (null? v))
           (tagcase (k-get (k-resolve expected))
             (ty-base (t) (k-in-fixed-range? t (car v) a b))
             (else y #f))))))
;; The integer literal `x` is: a fixnum; or arithmetic on fixnums by the
;; standard `+`, `*` and `-`, every node spanning `a`..`b`, the literal
;; (the parser's `big-literal`), which no arithmetic written out does.
(define k-literal-value (subr (maxeff kreads spin) (kx int int) (listof int acyclic))
  (lambda (x a b)
    (tagcase x
      (x-const (t n c d cdk) (if (and (= t k-int) (= c a) (= d b)) (list n) nil))
      (x-app (f args c d cdk)
        (if (and (= c a) (= d b) (= (k-length args) 2))
            (tagcase f
              (x-var (s fa fb fafbk)
                (if (and (= fa a) (= fb b) (k-std-binding? s (k-lookup s)))
                    (k-literal-op (symbol->string s) (k-literal-value (car args) a b)
                                  (k-literal-value (car (cdr args)) a b))
                    nil))
              (else y nil))
            nil))
      (else y nil))))
(define k-literal-op
  (subr (read @globals) (string (listof int acyclic) (listof int acyclic)) (listof int acyclic))
  (lambda (op l r)
    (if (or (null? l) (null? r))
        nil
        (case op
          (("+") (list (+ (car l) (car r))))
          (("*") (list (* (car l) (car r))))
          (("-") (list (- (car l) (car r))))
          (else nil)))))
)))
