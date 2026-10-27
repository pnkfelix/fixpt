;;; The checker, in FX-26: the types of the modules files make,
;;; `(load-moduleof "file" arg …)` and `(load-input-moduleof "file" arg …)`,
;;; as the parser leaves them (`type-loaded`): `(%type-made g "file" arg …)`,
;;; `g` the file's hidden global. As `parse.rs`'s `type_made`. Before the
;;; types' reader, which reads with it (`docs/research/derived-signatures.md`).

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (eager-reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-read-types (load-module "fx26:check-read-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-holds-types (load-module "fx26:check-holds-types.fx"))
       (check-read-helpers-types (load-module "fx26:check-read-helpers-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-read-made-types (load-module "fx26:check-read-made-types.fx"))
       (reader-types (load-module "fx26:reader-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-read-helpers (select check-read-helpers-types check-read-helpers-sig))
           (check-read (select check-read-types check-read-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (check-env (select check-env-types check-env-sig))
           (check-print (select check-print-types check-print-sig))
           (check-holds (select check-holds-types check-holds-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig))
           (parser (select reader-types parser-sig)))
    (module

;; The types it uses of the files before it.
(hide (include check-types-types) (include eager-reader-types) (include parser-types)
      (include check-read-types) (include check-env-types) (include check-holds-types)
      (include check-read-made-types))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-read-helpers) (include check-read)
      (include check-subst) (include check-env) (include check-print) (include check-holds)
      (include check-print-parts) (include parser))

;; The string `s` is, as written; "" if it is none.
(define k-made-string (->* (syn) string)
  (lambda (s) (tagcase s (atom (d a b) (typecase d (string x x) (else y ""))) (else y ""))))
;; `xs` but the first `n`.
(define k-made-drop (->* (k-syns int) k-syns)
  (lambda (xs n) (if (= n 0) xs (k-made-drop (cdr xs) (- n 1)))))
;; `(%type-made g "file" arg …)`: the type of the module a `load-module`
;; of the file makes given `arg …`, the hidden global `g` the load of it;
;; `(%input-made …)`, of the module a `load-input` file's value makes
;; (`load-moduleof`, `load-input-moduleof`: `type-loaded`, `type_made`).
;; `parse-d` reads a description (`check-read-descs.fx`'s `k-parse-d`).
(define k-type-made-by (->* (syn k-syns bool k-desc-reader) int)
  (lambda (s items input? parse-d)
    (let* ((g (syn-head (k-nth items 1))) (path (k-made-string (k-nth items 2))) (t (k-lookup g)))
      (if (< t 0)
          (k-sfail (k-cat3 "`" path "` is not loaded here") s)
          (k-made-walk (if input? (k-module-val t 'input) t) (k-made-drop items 3)
                       s path parse-d)))))
;; The type of value `n` of module type `t`.
(define k-module-val (->* (int symbol) int)
  (lambda (t n)
    (tagcase (k-get (k-resolve t))
      (ty-module (abs ds vs) (k-made-part vs n))
      (else y -1))))
(define k-made-part (->* (k-parts symbol) int)
  (lambda (ps n)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) n) (extract (car ps) 2))
          (else (k-made-part (cdr ps) n)))))
;; What a value of type `t`, of the file `path`, makes given `args`: a
;; `poly` takes as many descriptions as it binds, as `proj` does; a
;; procedure of no parameters is applied; a procedure's parameters take one
;; argument each, a module's name where the types after it select from it.
;; Done when the arguments are, and no procedure of no parameters is left: a
;; module's type, or refused (`type_made`).
(define k-made-walk (->* (int k-syns syn string k-desc-reader) int)
  (lambda (t args s path parse-d)
    (let ((t (k-resolve t)))
      (tagcase (k-get t)
        (ty-poly (bs inner)
          (cond ((null? args) (k-made-done t s path))
                ((< (k-length args) (k-length bs))
                 (k-sfail (k-made-count path "a `poly` of " (k-length bs) " description(s)" args)
                          s))
                (else (k-made-walk (k-subst inner (k-made-map bs args parse-d))
                                   (k-made-drop args (k-length bs)) s path parse-d))))
        (ty-subr (e ps r cv sp)
          (cond ((null? ps) (k-made-walk r args s path parse-d))
                ((null? args) (k-made-done t s path))
                ((< (k-length args) (k-length ps))
                 (k-sfail (k-made-count path "a procedure of " (k-length ps) " parameter(s)" args)
                          s))
                (else (k-made-walk (k-made-params r args path) (k-made-drop args (k-length ps))
                                   s path parse-d))))
        (else y (if (null? args)
                    (k-made-done t s path)
                    (k-sfail (k-cat5 "what `" path "` makes is a " (k-show-ty t) ", given no more")
                             s)))))))
(define k-made-count (->* (string string int string k-syns) string)
  (lambda (path what n of args)
    (k-cat5 (k-cat3 "`" path "` makes ") (k-cat3 what (int->string n) of) ", and "
            (int->string (k-length args)) " are given")))
;; `t`, all arguments taken: a module's type, or refused.
(define k-made-done (->* (int syn string) int)
  (lambda (t s path)
    (tagcase (k-get t)
      (ty-module (abs ds vs) t)
      (else y (k-sfail (k-cat5 "what `" path "` makes, given these, is a " (k-show-ty t)
                               ", not a module")
                       s)))))
;; A `poly`'s binders `bs`, each the description of `args` it is given.
(define k-made-map (->* (k-binders k-syns k-desc-reader) k-map)
  (lambda (bs args parse-d)
    (if (null? bs)
        nil
        (let* ((v (extract (car bs) 1)) (k (extract (car bs) 2)) (d (parse-d (car args))))
          (if (k-made-fits? d k)
              (cons (cons v d) (k-made-map (cdr bs) (cdr args) parse-d))
              (k-sfail (k-cat4 (k-quote (symbol->string (k-dvar-name v))) " is bound as a "
                               (k-kind-word k) ", and the description given is not one")
                       (car args)))))))
;; Whether description `d` is of kind `k` (`k-desc-of-kind?`, which comes
;; after this; a function's own kind not compared).
(define k-made-fits? (->* (k-desc int) bool)
  (lambda (d k)
    (tagcase d
      (dr (r) (or (= k 0) (and (= k 3) (k-place? r))))
      (de (e) (= k 1))
      (dt (t) (or (= k 2) (= k 4) (= k 8) (and (= k 7) (k-is-flat? t))))
      (dz (z) (= k 5))
      (dc (c) (= k 6))
      (df (f) (k-arrow-kind? k)))))
;; Result `r` of a procedure given `args`: each `(select $k x)` in it the
;; type `x` of the module the `k`th names.
(define k-made-params (->* (int k-syns string) int)
  (lambda (r args path)
    (let ((out (the (ref k-params-given @t) (new nil))) (outer (get k-param-map)))
      (begin (k-made-sels r (k-new-seen) args path out)
             (set k-param-map (get out))
             (let ((t (k-subst r nil))) (begin (set k-param-map outer) t))))))
(define k-made-sels (->* (int k-seen k-syns string (ref k-params-given @t)) unit)
  (lambda (t seen args path out)
    (let ((t (k-resolve t)))
      (if (k-seen? seen t)
          #u
          (tagcase (k-get t)
            (ty-param (k n)
              (let ((m (k-nth args k)))
                (if (syn-symbol? m)
                    (set out (cons (product (1 k) (2 n) (3 (k-ty-new (ty-select (syn-head m) n))))
                                   (get out)))
                    (k-sfail (k-cat5 "argument " (int->string (+ k 1))
                                     " is a module the types `" path
                                     "` makes depend on: give it by name")
                             m))))
            (else y (k-made-sels-each (k-ty-kids t) seen args path out)))))))
(define k-made-sels-each (->* (k-ids k-seen k-syns string (ref k-params-given @t)) unit)
  (lambda (ts seen args path out)
    (if (null? ts)
        #u
        (begin (k-made-sels (car ts) seen args path out)
               (k-made-sels-each (cdr ts) seen args path out))))))))
