;;; The checker, in FX-26: what reading types uses that reads none of
;;; them, taken out of its knot: its messages and lists of keywords;
;;; binders and parameters as names, scopes and descriptions; the kids of
;;; a description; parameters' selects. Before `check-read-descs.fx`.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-read-helpers-module (module

;; A `dlambda` of no parameters, as an error says.
(define k-dlambda-empty string "a `dlambda` takes at least one description")
(define k-moduleof-usage string "`(moduleof (abs t type) … (desc d type) … (val x type) …)`")
(define k-abs-usage string
  "an abstract component is a `type`, or a type constructor `(=> (kind …) type)`, for now")
;; The heads of the type forms a type is read from, and every keyword: no
;; parameter's name.
(define k-type-forms k-names
  (list 'arrayof 'bloblet 'composable 'dletrec 'icell 'listof 'mark-key 'moduleof 'mu 'nat 'nlist
        'pairof 'place 'poly 'productof 'prompt-tag 'proves 'ref 'select 'subr 'sumof 'bool
        'union))
(define k-keywords k-names
  (list 'lambda 'plambda 'proj 'if 'letrec 'let 'begin 'define 'define* 'define-type
        'define-generative 'subr 'poly 'ref 'pairof 'dletrec 'void 'pure 'maxeff 'read 'write
        'alloc 'goto 'comefrom 'region 'effect 'type 'prompt 'prompt-tag 'composable 'mark-key
        'listof 'cond 'else 'and 'or 'let* 'define-effect 'module-parameters 'the 'bloblet 'fields
        'frozen 'arrayof 'icell 'await 'define-rec 'letrena 'letreap 'rlambda 'quote 'productof
        'sumof 'product 'extract 'sum 'tagcase 'module 'moduleof 'with 'select 'load-module
        'define-datatype 'make-bloblet 'bloblet-ref 'bloblet-set! 'bloblet-freeze 'bloblet-byte
        'bloblet-set-byte! 'bloblet-bytes 'rmake-bloblet 'dlambda '=> 'case))
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
              (("arrayof") (k-ty-new (ty-array t r)))
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
;; A component's names: its name; or, an `abs`'s, the names in a list.
(define k-component-names (subr (maxeff checks spin) (syn string) k-names)
  (lambda (name head)
    (if (syn-symbol? name)
        (the k-names (cons (syn-head name) nil))
        (tagcase name
          (lst (items d a b)
            (if (string=? head "abs") (k-syn-symbols items) (k-sfail "a component's name" name)))
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
          (or (string=? n "pure") (string=? n "spin")
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
      (ty-array (a r) (the k-ids (cons a nil)))
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
  (lambda (ns) (or (null? ns) (and (symbol=? (car ns) k-no-name) (k-all-unnamed? (cdr ns))))))))

(define k-abs-bound (with check-read-helpers-module k-abs-bound))
(define k-abs-usage (with check-read-helpers-module k-abs-usage))
(define k-all-unnamed? (with check-read-helpers-module k-all-unnamed?))
(define k-arity-fail (with check-read-helpers-module k-arity-fail))
(define k-binders-as-descs (with check-read-helpers-module k-binders-as-descs))
(define k-binders-as-scope (with check-read-helpers-module k-binders-as-scope))
(define k-component-names (with check-read-helpers-module k-component-names))
(define k-ctor-eta (with check-read-helpers-module k-ctor-eta))
(define k-desc-kids (with check-read-helpers-module k-desc-kids))
(define k-dlambda-empty (with check-read-helpers-module k-dlambda-empty))
(define k-effect-shaped? (with check-read-helpers-module k-effect-shaped?))
(define k-fresh-named (with check-read-helpers-module k-fresh-named))
(define k-fun-bound? (with check-read-helpers-module k-fun-bound?))
(define k-gen-eta (with check-read-helpers-module k-gen-eta))
(define k-gives-fail (with check-read-helpers-module k-gives-fail))
(define k-ids-then (with check-read-helpers-module k-ids-then))
(define k-lam (with check-read-helpers-module k-lam))
(define k-moduleof-usage (with check-read-helpers-module k-moduleof-usage))
(define k-names-once (with check-read-helpers-module k-names-once))
(define k-no-name (with check-read-helpers-module k-no-name))
(define k-not-giving (with check-read-helpers-module k-not-giving))
(define k-param-name (with check-read-helpers-module k-param-name))
(define k-param-selects (with check-read-helpers-module k-param-selects))
(define k-params-kinds (with check-read-helpers-module k-params-kinds))
(define k-params-names (with check-read-helpers-module k-params-names))
(define k-parse-select (with check-read-helpers-module k-parse-select))
(define k-part-onto (with check-read-helpers-module k-part-onto))
(define k-parts-reversed (with check-read-helpers-module k-parts-reversed))
(define k-selects-reversed (with check-read-helpers-module k-selects-reversed))
(define k-ty-kids (with check-read-helpers-module k-ty-kids))
