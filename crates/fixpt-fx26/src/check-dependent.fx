;;; The checker, in FX-26: dependent procedures (`docs/research/
;;; first-class-modules.md`, stage M5), as the Rust checker's `modules.rs`
;;; and `synth_lambda_as` make them. After `check-subtype.fx`, whose
;;; `k-name-nat` names a parameter's module. Part of the checker,
;;; `check-types.fx` first.

;;; ------------------------------------------------------------ dependent procedures
;;; A procedure's parameter may be named, `(name type)`, for the types after
;;; it to select from (`first-class-modules.md`, M5): in its type, `(select
;;; $k t)`, the `k`th parameter's type `t`.

;; `t` with each `(select $k n)` what `given` says it is.
(define k-instantiate-params (subr (maxeff kstate spin) (int k-params-given) int)
  (lambda (t given)
    (if (null? given)
        t
        (let ((outer (get k-param-map)))
          (begin (set k-param-map given)
                 (let ((r (k-subst t nil))) (begin (set k-param-map outer) r)))))))
;; A module-typed binding's abstract types, from parameter `j`: each as named
;; for the binding, onto `given`; and as `(select $j t)`, onto `back`.
(define-type k-given-back (productof (1 k-params-given) (2 k-map)))
(define k-abs-given (subr (maxeff kstate spin) (int k-parts k-params-given k-map) k-given-back)
  (lambda (j abs given back)
    (if (null? abs)
        (product (1 given) (2 back))
        (let* ((a (extract (car abs) 1)) (w (extract (car abs) 2))
               (g (product (1 j) (2 a) (3 (k-ty-new (ty-var w)))))
               (bk (the (pairof int k-desc @t) (cons w (dt (k-ty-new (ty-param j a)))))))
          (k-abs-given j (cdr abs) (the k-params-given (cons g given))
                       (the k-map (cons bk back)))))))
;; What a `lambda`'s parameters were bound to: their types for the
;; procedure's type; and what each earlier one gives its `(select $k t)`s.
(define-type k-dependent (productof (1 k-bindings) (2 k-params-given) (3 k-map)))
;; Parameters `typed`, from the `j`th, bound in order, at `a`..`b`: a
;; parameter's type may name a module in scope, or an earlier parameter.
;; What it names of an earlier one is, in the procedure's type, `(select $k
;; t)`; a type told it says it so, and is given the earlier parameter's.
(define k-bind-dependent
  (subr (maxeff checks spin) (k-bindings k-names int k-params-given k-map int int) k-dependent)
  (lambda (typed names j given back a b)
    (if (null? typed)
        (product (1 (the k-bindings nil)) (2 given) (3 back))
        (let* ((n (car (car typed)))
               (outside (k-resolve-outside (cdr (car typed)) names a b))
               (resolved (k-instantiate-params outside given))
               (bound (k-name-nat n resolved))
               (pushed (k-bind n bound))
               (t (if (null? back) resolved (k-subst resolved back)))
               (gb (tagcase (k-get bound)
                     (ty-module (abs ds vs) (k-abs-given j abs given back))
                     (else y (product (1 given) (2 back)))))
               (rest (k-bind-dependent (cdr typed) (cdr names) (+ j 1)
                                       (extract gb 1) (extract gb 2) a b)))
          (product (1 (the k-bindings (cons (cons n t) (extract rest 1))))
                   (2 (extract rest 2)) (3 (extract rest 3)))))))
;; A `lambda`'s parameters `typed`, at `a`..`b`, bound so.
(define k-bind-params (subr (maxeff checks spin) (k-bindings int int) k-dependent)
  (lambda (typed a b) (k-bind-dependent typed (k-binding-names typed) 0 nil nil a b)))
;; A lambda's result type `t`, as the procedure's type says it.
(define k-result-back (subr (maxeff kstate spin) (int k-map) int)
  (lambda (t back) (if (null? back) t (k-subst t back))))

;; The heads of the type forms a type is read from, and every keyword: no
;; parameter's name.
(define k-type-forms k-names
  (list 'arrayof 'bloblet 'composable 'dletrec 'icell 'listof 'mark-key 'moduleof 'mu 'nat 'nlist
        'pairof 'place 'poly 'productof 'prompt-tag 'proves 'ref 'select 'subr 'sumof))
(define k-keywords k-names
  (list 'lambda 'plambda 'proj 'if 'letrec 'let 'begin 'define 'define* 'define-type
        'define-generative 'subr 'poly 'ref 'pairof 'dletrec 'void 'pure 'maxeff 'read 'write
        'alloc 'goto 'comefrom 'region 'effect 'type 'prompt 'prompt-tag 'composable 'mark-key
        'listof 'cond 'else 'and 'or 'let* 'define-effect 'private-regions 'the 'bloblet 'fields
        'frozen 'arrayof 'icell 'await 'define-rec 'letrena 'letreap 'rlambda 'quote 'productof
        'sumof 'product 'extract 'sum 'tagcase 'module 'moduleof 'with 'select 'load-module
        'define-datatype 'make-bloblet 'bloblet-ref 'bloblet-set! 'bloblet-freeze 'bloblet-byte
        'bloblet-set-byte! 'bloblet-bytes 'rmake-bloblet))
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
(define k-no-name symbol '||)
(define k-all-unnamed? (subr (maxeff (read @globals) spin) (k-names) bool)
  (lambda (ns) (or (null? ns) (and (symbol=? (car ns) k-no-name) (k-all-unnamed? (cdr ns))))))
;; `t` with each `(select m x)` of a parameter named before it, the `k`th,
;; made `(select $k x)`.
(define k-select-params (subr (maxeff kstate spin) (int k-names) int)
  (lambda (t names)
    (let ((sel (if (k-all-unnamed? names)
                   (the k-selects nil)
                   (k-param-selects (k-selects-in t) names))))
      (if (null? sel)
          t
          (let ((outer (get k-select-map)))
            (begin (set k-select-map sel)
                   (let ((r (k-subst t nil))) (begin (set k-select-map outer) r))))))))
;; `names` with `n` last.
(define k-names-snoc (subr (maxeff (read @globals) (alloc @t) spin) (k-names symbol) k-names)
  (lambda (ns n) (if (null? ns) (cons n nil) (cons (car ns) (k-names-snoc (cdr ns) n)))))
;; A `subr` type's parameters `ps` (from those named `names`) and its
;; result `r`, read: their types, the result last.
(define k-read-params-from (subr (maxeff checks spin) (k-syns syn k-names) k-ids)
  (lambda (ps r names)
    (if (null? ps)
        (cons (k-select-params (k-parse-type r) names) nil)
        (let* ((named (k-param-name (car ps)))
               (written (if (null? named) (car ps) (k-nth (k-items (car ps) "a parameter") 1)))
               (t (k-select-params (k-parse-type written) names))
               (name (if (null? named) k-no-name (car named)))
               (rest (k-read-params-from (cdr ps) r (k-names-snoc names name))))
          (cons t rest)))))
(define k-read-params (subr (maxeff checks spin) (k-syns syn) k-ids)
  (lambda (ps r) (k-read-params-from ps r nil)))
(set k-parse-params k-read-params)

(define k-abs-types (subr (maxeff kstate spin) (k-parts k-parts) k-parts)
  (lambda (abs ds)
    (if (null? abs)
        ds
        (cons (product (1 (extract (car abs) 1)) (2 (k-ty-new (ty-var (extract (car abs) 2)))))
              (k-abs-types (cdr abs) ds)))))
;; A module-typed binding's types, by component name: each abstract type as
;; named for the binding, then each transparent one.
(define k-module-types (subr (maxeff kstate spin) (int) k-parts)
  (lambda (mt)
    (tagcase (k-get mt)
      (ty-module (abs ds vs) (k-abs-types abs ds))
      (else y nil))))
;; Each `(select $k x)` in `t`, as first met, onto `out`.
(define-rec
  (k-param-sels-from (subr (maxeff kstate spin) (int (ref k-ids @t) (ref k-params-given @t)) unit)
    (lambda (t seen out)
      (let ((t (k-resolve t)))
        (if (k-has-id? (get seen) t)
            #u
            (begin
              (set seen (cons t (get seen)))
              (tagcase (k-get t)
                (ty-param (k x)
                  (if (>= (k-param-in (get out) k x -1) 0)
                      #u
                      (set out (cons (product (1 k) (2 x) (3 t)) (get out)))))
                (else y (k-param-sels-each (k-ty-kids t) seen out))))))))
  (k-param-sels-each (subr (maxeff kstate spin) (k-ids (ref k-ids @t) (ref k-params-given @t)) unit)
    (lambda (ts seen out)
      (if (null? ts)
          #u
          (begin (k-param-sels-from (car ts) seen out) (k-param-sels-each (cdr ts) seen out))))))
;; `ps` reversed, onto `acc`.
(define k-given-reversed
  (subr (maxeff (read @globals) (alloc @t) spin) (k-params-given k-params-given) k-params-given)
  (lambda (ps acc) (if (null? ps) acc (k-given-reversed (cdr ps) (cons (car ps) acc)))))
;; What an argument a procedure's types depend on, not a name, says.
(define k-by-name string
  (string-append " is a module the procedure's types depend on: "
                 "give it by name (bind it with `let` first)"))
(define k-part-of-types (subr (maxeff kreads spin) (k-parts symbol) int)
  (lambda (ps n)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) n) (extract (car ps) 2))
          (else (k-part-of-types (cdr ps) n)))))
;; What each `(select $k x)` of `found` is for a call with `args`, at
;; `a`..`b`: the type `x` of the module the `k`th argument names, by name.
(define k-args-given (subr (maxeff checks spin) (k-params-given kxs int int) k-params-given)
  (lambda (found args a b)
    (if (null? found)
        nil
        (let* ((k (extract (car found) 1)) (x (extract (car found) 2))
               (arg (if (< k (k-length args)) (the kxs (cons (k-nth args k) nil)) (the kxs nil)))
               (v (if (null? arg) '|| (tagcase (car arg) (x-var (v va vb) v) (else z '||))))
               (mt (if (symbol=? v '||) -1 (k-lookup v)))
               (to (if (< mt 0)
                       (k-fail (k-cat3 "argument " (int->string (+ k 1)) k-by-name) a b)
                       (let ((t (k-part-of-types (k-module-types mt) x)))
                         (if (< t 0)
                             (k-fail (k-cat5 "`" (symbol->string v) "` has no type `"
                                             (symbol->string x) "`")
                                     a b)
                             t))))
               (rest (k-args-given (cdr found) args a b)))
          (cons (product (1 k) (2 x) (3 to)) rest)))))
;; A dependent procedure's callee, `c` (none or one), for a call with `args`
;; at `a`..`b`: its types given the modules its arguments name.
(define-type k-callables (listof k-callable acyclic))
(define k-instantiate-all (subr (maxeff kstate spin) (k-ids k-params-given) k-ids)
  (lambda (ts given)
    (if (null? ts)
        nil
        (let ((t (k-instantiate-params (car ts) given)))
          (cons t (k-instantiate-all (cdr ts) given))))))
(define k-dependent-callee (subr (maxeff checks spin) (k-callables kxs int int) k-callables)
  (lambda (c args a b)
    (if (null? c)
        c
        (let* ((ps (extract (car c) 2)) (r (extract (car c) 3))
               (out (the (ref k-params-given @t) (new nil)))
               (seen (the (ref k-ids @t) (new nil)))
               (walked (begin (k-param-sels-each ps seen out) (k-param-sels-from r seen out))))
          (if (null? (get out))
              c
              (let ((given (k-args-given (k-given-reversed (get out) nil) args a b)))
                (cons (product (1 (extract (car c) 1)) (2 (k-instantiate-all ps given))
                               (3 (k-instantiate-params r given)))
                      nil)))))))
