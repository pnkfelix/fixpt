;;; The checker, in FX-26: the pieces of types and effects as the Rust
;;; checker shows them: the names of variables, regions and globals;
;;; effects' atoms; kinds; the names `define-type` gave; sizes, linear,
;;; with the facts relating them; conventions, abstract types, shapes and
;;; propositions. Before `check-print.fx`, which puts them together.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
;; Its types (`check-print-types.fx`, its file's after it), loaded before the
;; module so that they are not among its values; the module names what it
;; uses of them.
(let* ((check-print-types (load-module "fx26:check-print-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (eager-reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (check-effects-types (load-module "fx26:check-effects-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-env (select check-env-types check-env-sig)))
    (module
(hide (include check-print-types) (include check-types-types) (include check-env-types)
      (include parser-types) (include eager-reader-types))
;; The types it uses of the files before it.
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-effects))
(import check-env k-dscope k-globals-region?)

;; Whether two types are being shown apart (`k-show-apart`): each
;; description variable printed as a mark, named after.
(define k-show-marks (ref bool @t) (new #f))
;; What brackets a variable's mark.
(define k-mark string (char->string (integer->char 1)))
;; Variable `v`'s name; or, while two types are shown apart, a mark for it,
;; named after: `f` where it is free, `b` where it is bound, `h` where it is
;; bound and not printed (a `moduleof`'s abstract type, shown by its
;; component's name).
(define k-dvar-text (->* (int string) string)
  (lambda (v how)
    (cond ((get k-show-marks) (k-cat4 k-mark how (int->string v) k-mark))
          ((string=? how "h") "")
          (else (symbol->string (k-dvar-name v))))))
;; A description variable's name, free where it is printed.
(define k-dvar-string (->* (int) string)
  (lambda (v) (k-dvar-text v "f")))
;; `(const p)` or `(acyclic p)`, frozen into place `p`; or, for the heap
;; (-1), `const` or `acyclic`.
(define k-frozen-show (->* (int bool) string)
  (lambda (p f)
    (let ((word (if f "acyclic" "const")))
      (if (< p 0) word (k-cat5 "(" word " " (k-dvar-string p) ")")))))
(define k-region-show (->* (k-region) string)
  (lambda (r)
    (tagcase r
      (r-const (n) (symbol->string n))
      (r-fresh (i n) n)
      (r-var (v) (k-dvar-string v))
      (r-frozen (p f) (k-frozen-show p f))
      (r-heap () "heap")
      (r-global (g) (k-cat3 "(globals " (symbol->string g) ")"))
      (r-globals () "@globals"))))
;; `(op r)`: an atom on region `r`.
(define k-region-atom-show (->* (string k-region) string)
  (lambda (op r) (k-cat5 "(" op " " (k-region-show r) ")")))
(define-rec
  (k-atom-show (->* (k-atom) string)
    (lambda (a)
      (tagcase a
        (a-read (r) (k-region-atom-show "read" r))
        (a-write (r) (k-region-atom-show "write" r))
        (a-alloc (r) (k-region-atom-show "alloc" r))
        (a-goto (r) (k-region-atom-show "goto" r))
        (a-comefrom (r) (k-region-atom-show "comefrom" r))
        (a-await (r) (k-region-atom-show "await" r))
        (a-init (r) (k-region-atom-show "init" r))
        (a-send (r) (k-region-atom-show "send" r))
        (a-receive (r) (k-region-atom-show "receive" r))
        (a-spin () "spin")
        (a-nondet () "nondet")
        (a-io (k) (k-cat3 "(io " (k-io-kind-name k) ")"))
        (a-var (v) (k-dvar-string v))
        (a-app (v ds) (k-cat4 "(" (k-dvar-string v) (k-eargs-show ds) ")")))))
  ;; What an effect application was given, each after a space.
  (k-eargs-show (->* (k-descs) string)
    (lambda (ds)
      (if (null? ds)
          ""
          (k-cat3 " "
                  (tagcase (car ds)
                    (dr (r) (k-region-show r))
                    (de (e) (k-eff-show-plain e))
                    (dz (z) (tagcase z (sz-finite () "finite") (sz-lin (k ts) (int->string k))))
                    (dc (c) (tagcase c
                              (cv-cellular () "cellular") (cv-native () "native") (cv-fx () "fx")
                              (cv-var (v) (k-dvar-string v))))
                    (else y "?"))
                  (k-eargs-show (cdr ds))))))
  ;; An effect inside one given an effect function: `pure`, an atom, or
  ;; `(maxeff …)`.
  (k-eff-show-plain (->* (k-eff) string)
    (lambda (e)
      (cond ((null? e) "pure")
            ((null? (cdr e)) (k-atom-show (car e)))
            (else (k-cat3 "(maxeff" (k-atoms-plain e) ")")))))
  (k-atoms-plain (->* (k-eff) string)
    (lambda (e) (if (null? e) "" (k-cat3 " " (k-atom-show (car e)) (k-atoms-plain (cdr e)))))))
(define k-atoms-show (->* (k-eff) string)
  (lambda (e) (if (null? e) "" (k-cat3 " " (k-atom-show (car e)) (k-atoms-show (cdr e))))))
(define k-strings-append (->* (k-strings k-strings) k-strings)
  (lambda (xs ys)
    (if (null? xs) ys (the k-strings (cons (car xs) (k-strings-append (cdr xs) ys))))))
(define k-strings-spaced (->* (k-strings) string)
  (lambda (xs) (if (null? xs) "" (k-cat3 " " (car xs) (k-strings-spaced (cdr xs))))))
;; ` g`, for the binding of global `g`; nothing for any other region.
(define k-global-shown (->* (k-region) string)
  (lambda (r) (tagcase r (r-global (g) (string-append " " (symbol->string g))) (else y ""))))
;; The names of the globals `e` reads (`op` 0) or writes (1), each after a
;; space, in the order of their text: effects are kept in their hashes'
;; order (`k-atom-cmp`), and put in this one only to be shown.
(define k-globals-shown (->* (k-eff int) string)
  (lambda (e op) (k-names-spaced (k-global-names e op nil))))
(define k-global-names (->* (k-eff int k-names) k-names)
  (lambda (e op acc)
    (if (null? e)
        acc
        (k-global-names (cdr e) op
                        (tagcase (car e)
                          (a-read (r) (if (= op 0) (k-global-name-into r acc) acc))
                          (a-write (r) (if (= op 1) (k-global-name-into r acc) acc))
                          (else y acc))))))
(define k-global-name-into (->* (k-region k-names) k-names)
  (lambda (r acc) (tagcase r (r-global (g) (k-name-insert g acc)) (else y acc))))
;; `g` into `xs`, kept in the order of the names' text.
(define k-name-insert (->* (symbol k-names) k-names)
  (lambda (g xs)
    (if (or (null? xs) (< (symbol-compare g (car xs)) 0))
        (the k-names (cons g xs))
        (the k-names (cons (car xs) (k-name-insert g (cdr xs)))))))
(define k-names-spaced (->* (k-names) string)
  (lambda (xs)
    (if (null? xs)
        ""
        (string-append " " (symbol->string (car xs)) (k-names-spaced (cdr xs))))))
(define k-one-global? (->* (k-atom) bool)
  (lambda (a)
    (tagcase a
      (a-read (r) (tagcase r (r-global (g) #t) (else y #f)))
      (a-write (r) (tagcase r (r-global (g) #t) (else y #f)))
      (else y #f))))
;; Whether `a` is on globals' bindings, which are never masked.
(define k-globals-atom? (->* (k-atom) bool)
  (lambda (a) (and (k-has-region? a) (k-globals-region? (k-atom-region a)))))
;; The atoms of `e` shown, but for those on one global's binding.
(define k-other-atom-strings (->* (k-eff) k-strings)
  (lambda (e)
    (cond ((null? e) nil)
          ((k-one-global? (car e)) (k-other-atom-strings (cdr e)))
          (else (the k-strings (cons (k-atom-show (car e)) (k-other-atom-strings (cdr e))))))))
;; `(op (globals names))`, alone in a list; none if there are no names.
(define k-globals-grouped (->* (string string) k-strings)
  (lambda (op names)
    (if (string=? names "") nil (the k-strings (cons (k-cat5 "(" op " (globals" names "))") nil)))))
;; The atoms shown, reads, or writes, of several globals being one atom:
;; `(read (globals f g))`.
(define k-atom-strings (->* (k-eff) k-strings)
  (lambda (e)
    (let* ((others (k-other-atom-strings e))
           (reads (k-globals-grouped "read" (k-globals-shown e 0)))
           (writes (k-globals-grouped "write" (k-globals-shown e 1))))
      (k-strings-append others (k-strings-append reads writes)))))
;; `pure`, a single atom, or `…`.
(define k-show-effect (->* (k-eff) string)
  (lambda (e)
    (let ((xs (k-atom-strings e)))
      (cond ((null? xs) "pure")
            ((null? (cdr xs)) (car xs))
            (else (k-cat3 "(maxeff" (k-strings-spaced xs) ")"))))))

(define k-kind-name (->* (int) string)
  (lambda (k)
    (case k ((0) "region")
            ((1) "effect")
            ((3) "place")
            ((4) "data")
            ((8) "sendable")
            ((7) "flat")
            ((5) "size")
            ((6) "conv")
            (else "type"))))
;; A convention as a program writes it.
(define k-conv-show (->* (k-conv) string)
  (lambda (c)
    (tagcase c
      (cv-cellular () "cellular")
      (cv-native () "native")
      (cv-fx () "fx")
      (cv-var (v) (k-dvar-string v)))))
;; The program's convention: what a subroutine type that names none has,
;; and what a convention nothing solves defaults to. Cellular, unless a
;; driver says otherwise (`--calling-convention`).
(define k-conv-default (ref k-conv @t) (new (cv-cellular)))
;; For a driver: whether the program's convention is native.
(define check-conv-native! (->* (bool) unit)
  (lambda (on) (set k-conv-default (if on (cv-native) (cv-cellular)))))
(define k-conv=? (->* (k-conv k-conv) bool)
  (lambda (a b) (= (k-conv-code a) (k-conv-code b))))
;; As Rust's `{:?}` writes a kind.
(define k-kind-debug (->* (int) string)
  (lambda (k)
    (case k ((0) "Region")
            ((1) "Effect")
            ((3) "Place")
            ((4) "Data")
            ((8) "Sendable")
            ((7) "Flat")
            ((5) "Size")
            ((6) "Conv")
            (else "Type"))))
(define-rec
  ;; A kind as it is written: `type`, or `(=> (type) type)`.
  (k-kind-text (->* (int) string)
    (lambda (k)
      (let ((a (k-arrow-parts k)))
        (if (null? a)
            (k-kind-name k)
            (k-cat5 "(=> (" (k-join (k-kinds-text (car (car a))) " ") ") "
                    (k-kind-text (cdr (car a))) ")")))))
  (k-kinds-text (->* (k-ids) k-strings)
    (lambda (ks)
      (if (null? ks) nil (cons (k-kind-text (car ks)) (k-kinds-text (cdr ks)))))))
;; A kind as the older messages name it, `Region`, `Type`, …; an arrow
;; kind as it is written.
(define k-kind-word (->* (int) string)
  (lambda (k) (if (k-arrow-kind? k) (k-kind-text k) (k-kind-debug k))))
;; Whether a region is a place: a variable bound as one.
(define k-place? (->* (k-region) bool)
  (lambda (r) (tagcase r (r-var (v) (k-place-var? v)) (r-heap () #t) (else x #f))))

;; Whether one of the first `i` bindings of `ds` is a `define-type` of `n`.
(define k-rec-named-within? (->* (k-scope int symbol) bool)
  (lambda (ds i n)
    (and (> i 0)
         (not (null? ds))
         (or (and (symbol=? (car (car ds)) n) (tagcase (cdr (car ds)) (ds-rec (d) #t) (else y #f)))
             (k-rec-named-within? (cdr ds) (- i 1) n)))))
;; The name `define-type` gave `t`, innermost first: each name's innermost
;; binding only. `ds` is `all` from binding `i` on; a binding that matches
;; is looked for again among those before it, matches being rare (once
;; every binding was, which made printing a type quadratic in the names in
;; scope at each of its nodes: `TODO.md` §34).
(define k-abbrev-in (->* (k-scope k-scope int int) k-strings)
  (lambda (all ds i t)
    (if (null? ds)
        nil
        (let ((n (car (car ds))))
          (tagcase (cdr (car ds))
            (ds-rec (d)
              (if (and (= (k-resolve d) t) (not (k-rec-named-within? all i n)))
                  (cons (symbol->string n) nil)
                  (k-abbrev-in all (cdr ds) (+ i 1) t)))
            (else y (k-abbrev-in all (cdr ds) (+ i 1) t)))))))
(define k-scramble (->* (int) int) (lambda (t) (remainder (* t 40503) 65521)))
(define-rec
  (k-atree-put (->* (k-atree int int symbol int) k-atree)
    (lambda (tr h t n i)
      (tagcase tr
        (a-leaf () (a-node h t n i (a-leaf) (a-leaf)))
        (a-node (h2 t2 n2 i2 l r)
          (cond ((or (< h h2) (and (= h h2) (< t t2)))
                 (a-node h2 t2 n2 i2 (k-atree-put l h t n i) r))
                ((or (> h h2) (and (= h h2) (> t t2)))
                 (a-node h2 t2 n2 i2 l (k-atree-put r h t n i)))
                (else tr)))))))
(define-rec
  (k-atree-get (->* (k-atree int int) k-named-at)
    (lambda (tr h t)
      (tagcase tr
        (a-leaf () nil)
        (a-node (h2 t2 n2 i2 l r)
          (cond ((or (< h h2) (and (= h h2) (< t t2))) (k-atree-get l h t))
                ((or (> h h2) (and (= h h2) (> t t2))) (k-atree-get r h t))
                (else (the k-named-at (list (product (1 n2) (2 i2)))))))))))
;; Every `define-type` of scope `ds`, from binding `i` on, into `tr`.
(define k-atree-of (->* (k-scope int k-atree) k-atree)
  (lambda (ds i tr)
    (if (null? ds)
        tr
        (tagcase (cdr (car ds))
          (ds-rec (d)
            (let ((t (k-resolve d)))
              (k-atree-of (cdr ds) (+ i 1) (k-atree-put tr (k-scramble t) t (car (car ds)) i))))
          (else y (k-atree-of (cdr ds) (+ i 1) tr))))))
;; Scope `ds` from binding `i` on.
(define k-scope-from (->* (k-scope int) k-scope)
  (lambda (ds i) (if (or (<= i 0) (null? ds)) ds (k-scope-from (cdr ds) (- i 1)))))
;; The name `define-type` gave `t`, as `k-abbrev-in` finds it, by tree `trs`
;; if there is one.
(define k-abbrev-by (->* (k-atrees int) k-strings)
  (lambda (trs t)
    (let ((all (get k-dscope)))
      (if (null? trs)
          (k-abbrev-in all all 0 t)
          (let ((f (k-atree-get (car trs) (k-scramble t) t)))
            (cond ((null? f) nil)
                  ((k-rec-named-within? all (extract (car f) 2) (extract (car f) 1))
                   (let ((i (+ (extract (car f) 2) 1))) (k-abbrev-in all (k-scope-from all i) i t)))
                  (else (the k-strings (list (symbol->string (extract (car f) 1)))))))))))
;; Binder `v` of kind `kind`: `(name kind)`, or `(name region bound)`.
(define k-binder-show (->* (int int) string)
  (lambda (v kind)
    (let* ((b (k-bound-of v)) (named (k-cat3 (k-dvar-text v "b") " " (k-kind-text kind)))
           (d (if (k-distinct-var? v) " distinct)" ")")))
      (if (null? b) (k-cat3 "(" named d) (k-cat5 "(" named " " (k-region-show (car b)) d)))))
(define k-show-binders (->* (k-binders) k-strings)
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((b (car bs)))
          (cons (k-binder-show (extract b 1) (extract b 2)) (k-show-binders (cdr bs)))))))

;; How deep `t` is in `path`, newest first: its place from the root, from 1.
(define k-depth-of (->* (k-ids int) int)
  (lambda (path t) (if (= (car path) t) (k-length path) (k-depth-of (cdr path) t))))
;; Sizes: a literal, `finite`, one more or less, and whether one list's
;; size is another's.
(define k-size-lit (->* (int) k-size) (lambda (k) (sz-lin k nil)))
;; The literal a size is, or -1.
(define k-size-as-lit (->* (k-size) int)
  (lambda (z) (tagcase z (sz-lin (k ts) (if (null? ts) k -1)) (else y -1))))
(define k-size-plus (->* (k-size int) k-size)
  (lambda (z d) (tagcase z (sz-lin (k ts) (sz-lin (+ k d) ts)) (else y z))))
;; Whether two terms are one variable with one coefficient.
(define k-term=? (->* ((pairof int int acyclic) (pairof int int acyclic)) bool)
  (lambda (x y) (and (= (car x) (car y)) (= (cdr x) (cdr y)))))
(define k-terms=? (->* (k-terms k-terms) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys)) (k-term=? (car xs) (car ys)) (k-terms=? (cdr xs) (cdr ys))))))
(define k-size=? (->* (k-size k-size) bool)
  (lambda (a b)
    (tagcase a
      (sz-finite () (tagcase b (sz-finite () #t) (else y #f)))
      (sz-lin (k ts) (tagcase b (sz-lin (k2 ts2) (and (= k k2) (k-terms=? ts ts2))) (else y #f))))))

(define k-map-find (->* (k-map int) k-map)
  (lambda (m v) (cond ((null? m) nil) ((= (car (car m)) v) m) (else (k-map-find (cdr m) v)))))
;; Linear sizes (`src/sizes.rs`): a variable; `a + c·b`; `v` replaced.
(define k-size-var (->* (int) k-size)
  (lambda (v) (sz-lin 0 (the k-terms (cons (cons v 1) nil)))))
;; Term `n·v` before `rest`, unless `n` is zero.
(define k-term-cons (->* (int int k-terms) k-terms)
  (lambda (v n rest) (if (= n 0) rest (the k-terms (cons (cons v n) rest)))))
;; `xs + c·ys`, terms in variable order, none zero.
(define k-terms-add (->* (k-terms k-terms int) k-terms)
  (lambda (xs ys c)
    (cond ((null? ys) xs)
          ((or (null? xs) (> (car (car xs)) (car (car ys))))
           (k-term-cons (car (car ys)) (* c (cdr (car ys))) (k-terms-add xs (cdr ys) c)))
          ((< (car (car xs)) (car (car ys)))
           (the k-terms (cons (car xs) (k-terms-add (cdr xs) ys c))))
          (else (let ((n (+ (cdr (car xs)) (* c (cdr (car ys))))))
                  (k-term-cons (car (car xs)) n (k-terms-add (cdr xs) (cdr ys) c)))))))
(define k-size-add-scaled (->* (k-size k-size int) k-size)
  (lambda (a b c)
    (tagcase a
      (sz-lin (k ts)
        (tagcase b
          (sz-lin (k2 ts2) (sz-lin (+ k (* c k2)) (k-terms-add ts ts2 c)))
          (else y (sz-finite))))
      (else y (sz-finite)))))
(define k-coef-of (->* (k-terms int) int)
  (lambda (ts v)
    (cond ((null? ts) 0) ((= (car (car ts)) v) (cdr (car ts))) (else (k-coef-of (cdr ts) v)))))
(define k-size-replace (->* (k-size int k-size) k-size)
  (lambda (s v by)
    (tagcase s
      (sz-lin (k ts)
        (let ((c (k-coef-of ts v)))
          (if (= c 0) s (k-size-add-scaled (k-size-add-scaled s (k-size-var v) (- 0 c)) by c))))
      (else y (sz-finite)))))
(define k-size-facts (ref (listof k-size-fact acyclic) @t) (new nil))
;; The terms from the first whose coefficient is 1 or -1 on.
(define k-unit-terms (->* (k-terms) k-terms)
  (lambda (xs)
    (cond ((null? xs) xs)
          ((or (= (cdr (car xs)) 1) (= (cdr (car xs)) -1)) xs)
          (else (k-unit-terms (cdr xs))))))
;; `s` with the variable fact `f` determines rewritten away: one of
;; coefficient 1 or -1 in an equality. `s` itself if there is none.
(define k-apply-fact (->* (k-size k-size-fact) k-size)
  (lambda (s f)
    (if (not (extract f 2))
        s
        (tagcase (extract f 1)
          (sz-lin (k ts)
            (let ((u (k-unit-terms ts)))
              (if (null? u)
                  s
                  (let* ((v (car (car u))) (c (cdr (car u)))
                         (rest (k-size-add-scaled (extract f 1) (k-size-var v) (- 0 c)))
                         (by (k-size-add-scaled (k-size-lit 0) rest (- 0 c))))
                    (k-size-replace s v by)))))
          (else y s)))))
;; `s` with each variable an equality determines rewritten away, oldest
;; fact first.
(define k-reduced (->* (k-size) k-size)
  (lambda (s)
    (letrec ((go (subr (read @globals) (k-size (listof k-size-fact acyclic)) k-size)
                   (lambda (s fs) (if (null? fs) s (go (k-apply-fact s (car fs)) (cdr fs))))))
      (go s (the (listof k-size-fact acyclic) (reverse (get k-size-facts)))))))
;; Whether no term's coefficient is negative.
(define k-coefs-nonneg? (->* (k-terms) bool)
  (lambda (xs) (or (null? xs) (and (>= (cdr (car xs)) 0) (k-coefs-nonneg? (cdr xs))))))
;; Whether a size is plainly non-negative: every size is a natural.
(define k-plainly-nonneg? (->* (k-size) bool)
  (lambda (s) (tagcase s (sz-lin (k ts) (and (>= k 0) (k-coefs-nonneg? ts))) (else y #f))))
;; Whether, for some fact `f ≥ 0` of `fs`, `a - f` is plainly non-negative.
(define k-nonneg-by-fact? (->* (k-size (listof k-size-fact acyclic)) bool)
  (lambda (a fs)
    (and (not (null? fs))
         (or (and (not (extract (car fs) 2))
                  (k-plainly-nonneg? (k-size-add-scaled a (k-reduced (extract (car fs) 1)) -1)))
             (k-nonneg-by-fact? a (cdr fs))))))
;; `gcd(a, b)` of naturals, Euclid's, counting down `fuel` (100 is more
;; steps than any pair of 64-bit numbers takes).
(define k-gcd (->* (int int nat) int)
  (lambda (a b fuel)
    (cond ((= b 0) a) ((= fuel 0) 1) (else (k-gcd b (remainder a b) (- fuel 1))))))
(define k-abs (->* (int) int) (lambda (n) (if (< n 0) (- 0 n) n)))
(define k-terms-gcd (->* (k-terms int) int)
  (lambda (ts g) (if (null? ts) g (k-terms-gcd (cdr ts) (k-gcd g (k-abs (cdr (car ts))) 100)))))
(define k-terms-div (->* (k-terms int) k-terms)
  (lambda (ts g)
    (if (null? ts)
        nil
        (let ((t (the (pairof int int acyclic) (cons (car (car ts)) (quotient (cdr (car ts)) g)))))
          (the k-terms (cons t (k-terms-div (cdr ts) g)))))))
;; `c ≥ 0` as integers allow: its coefficients divided by their gcd, its
;; constant rounded down after the same division.
(define k-tightened (->* (k-size) k-size)
  (lambda (c)
    (tagcase c
      (sz-lin (k ts)
        (let ((g (k-terms-gcd ts 0)))
          (if (<= g 1) c (sz-lin (quotient (- k (modulo k g)) g) (k-terms-div ts g)))))
      (else y c))))
;; Variable `v` added to the sorted `vs`, once.
(define k-var-into (->* (k-ids int) k-ids)
  (lambda (vs v)
    (cond ((null? vs) (the k-ids (cons v nil)))
          ((= (car vs) v) vs)
          ((< v (car vs)) (the k-ids (cons v vs)))
          (else (the k-ids (cons (car vs) (k-var-into (cdr vs) v)))))))
(define k-terms-vars (->* (k-terms k-ids) k-ids)
  (lambda (ts vs) (if (null? ts) vs (k-terms-vars (cdr ts) (k-var-into vs (car (car ts)))))))
;; The variables of `cs`, sorted, each once.
(define k-lins-vars (->* (k-lins k-ids) k-ids)
  (lambda (cs vs)
    (if (null? cs)
        vs
        (let ((more (tagcase (car cs) (sz-lin (k ts) (k-terms-vars ts vs)) (else y vs))))
          (k-lins-vars (cdr cs) more)))))
(define k-lins-append (->* (k-lins k-lins) k-lins)
  (lambda (xs ys) (if (null? xs) ys (the k-lins (cons (car xs) (k-lins-append (cdr xs) ys))))))
;; `v ≥ 0` for each of `vs`.
(define k-lins-of-vars (->* (k-ids) k-lins)
  (lambda (vs)
    (if (null? vs) nil (the k-lins (cons (k-size-var (car vs)) (k-lins-of-vars (cdr vs)))))))
(define k-coef-in (->* (k-size int) int)
  (lambda (c v) (tagcase c (sz-lin (k ts) (k-coef-of ts v)) (else y 0))))
(define k-sign (->* (int) int) (lambda (n) (cond ((< n 0) -1) ((> n 0) 1) (else 0))))
;; Those of `cs` whose coefficient of `v` has the sign `s` (-1, 0 or 1).
(define k-lins-signed (->* (k-lins int int) k-lins)
  (lambda (cs v s)
    (cond ((null? cs) nil)
          ((= (k-sign (k-coef-in (car cs) v)) s)
           (the k-lins (cons (car cs) (k-lins-signed (cdr cs) v s))))
          (else (k-lins-signed (cdr cs) v s)))))
;; `p` with each of `ns`, scaled so that `v` cancels, tightened, onto `acc`.
(define k-lins-cancel (->* (k-size k-lins int k-lins) k-lins)
  (lambda (p ns v acc)
    (if (null? ns)
        acc
        (let* ((n (car ns)) (x (k-coef-in p v)) (y (- 0 (k-coef-in n v)))
               (c (k-tightened (k-size-add-scaled (k-size-add-scaled (k-size-lit 0) p y) n x))))
          (k-lins-cancel p (cdr ns) v (the k-lins (cons c acc)))))))
(define k-lins-combined (->* (k-lins k-lins int k-lins) k-lins)
  (lambda (ps ns v acc)
    (if (null? ps) acc (k-lins-combined (cdr ps) ns v (k-lins-cancel (car ps) ns v acc)))))
;; How many of `cs` there are, and `n`.
(define k-lins-count (->* (k-lins int) int)
  (lambda (cs n) (if (null? cs) n (k-lins-count (cdr cs) (+ n 1)))))
;; Whether some constraint of `cs` is a constant below 0.
(define k-lins-contradict? (->* (k-lins) bool)
  (lambda (cs)
    (and (not (null? cs))
         (or (tagcase (car cs) (sz-lin (k ts) (and (null? ts) (< k 0))) (else y #f))
             (k-lins-contradict? (cdr cs))))))
;; Each of `vs`, lowest first, eliminated from `cs`; giving up past 64.
(define k-fm-eliminate (->* (k-lins k-ids) bool)
  (lambda (cs vs)
    (if (null? vs)
        (k-lins-contradict? cs)
        (let* ((v (car vs))
               (next (k-lins-combined (k-lins-signed cs v 1) (k-lins-signed cs v -1) v
                                      (k-lins-signed cs v 0))))
          (if (> (k-lins-count next 0) 64) #f (k-fm-eliminate next (cdr vs)))))))
;; The inequalities in scope, oldest first, reduced, `finite` left out.
(define k-fact-lins (->* ((listof k-size-fact acyclic)) k-lins)
  (lambda (fs)
    (cond ((null? fs) nil)
          ((extract (car fs) 2) (k-fact-lins (cdr fs)))
          (else (let ((c (k-reduced (extract (car fs) 1))))
                  (tagcase c
                    (sz-lin (k ts) (the k-lins (cons c (k-fact-lins (cdr fs)))))
                    (else y (k-fact-lins (cdr fs)))))))))
(define k-refuted-below? (->* (k-size) bool)
  (lambda (a)
    (tagcase a
      (sz-lin (k ts)
        (let* ((facts (k-fact-lins (the (listof k-size-fact acyclic) (reverse (get k-size-facts)))))
               (below (k-size-add-scaled (k-size-lit -1) a -1))
               (cs (k-lins-append facts (the k-lins (cons below nil))))
               (vs (k-lins-vars cs nil)))
          (k-fm-eliminate (k-lins-append cs (k-lins-of-vars vs)) vs)))
      (else y #f))))
;; Whether the facts show `a ≥ 0`: plainly, or with a fact `f ≥ 0` to spare, or
;; by Fourier–Motzkin.
(define k-size-nonneg? (->* (k-size) bool)
  (lambda (a0)
    (let ((a (k-reduced a0)))
      (or (k-plainly-nonneg? a)
          (k-nonneg-by-fact? a (the (listof k-size-fact acyclic) (reverse (get k-size-facts))))
          (k-refuted-below? a)))))
;; Whether the facts reduce `s` to 0.
(define k-size-zero? (->* (k-size) bool)
  (lambda (s) (k-size=? (k-reduced s) (k-size-lit 0))))
;; Whether the facts show `a = b`.
(define k-size-eq? (->* (k-size k-size) bool)
  (lambda (a b)
    (tagcase a
      (sz-finite () (tagcase b (sz-finite () #t) (else y #f)))
      (else y (tagcase b (sz-finite () #f) (else w (k-size-zero? (k-size-add-scaled a b -1))))))))
;; The size of the tail of a list of size `n`: one less, where the facts
;; show `n ≥ 1`; `finite` otherwise.
(define k-tail-size (->* (k-size) k-size)
  (lambda (n)
    (tagcase n
      (sz-finite () n)
      (else y (let ((less (k-size-plus n -1))) (if (k-size-nonneg? less) less (sz-finite)))))))
;; Whether a list of size `m` is one of size `n`: the facts show them
;; equal, or `n` is `finite`.
(define k-size-le? (->* (k-size k-size) bool)
  (lambda (m n) (or (tagcase n (sz-finite () #t) (else y #f)) (k-size-eq? m n))))
;; `out` with variable `v` replaced by the size `m` gives it, if any.
(define k-size-given (->* (k-size int k-map) k-size)
  (lambda (out v m)
    (let ((f (k-map-find m v)))
      (if (null? f) out (tagcase (cdr (car f)) (dz (by) (k-size-replace out v by)) (else y out))))))
;; `s` with `m`'s sizes for its variables.
(define k-subst-size (->* (k-size k-map) k-size)
  (lambda (s m)
    (tagcase s
      (sz-lin (k ts)
        (letrec ((go (subr kreads (k-size k-terms) k-size)
                       (lambda (out xs)
                         (if (null? xs) out (go (k-size-given out (car (car xs)) m) (cdr xs))))))
          (go s ts)))
      (else y s))))
(define k-show-terms (->* (k-terms) k-strings)
  (lambda (ts)
    (if (null? ts)
        nil
        (let* ((n (k-dvar-string (car (car ts))))
               (c (cdr (car ts)))
               (x (if (= c 1) n (k-cat5 "(* " (int->string c) " " n ")"))))
          (cons x (k-show-terms (cdr ts)))))))
(define k-show-size (->* (k-size) string)
  (lambda (z)
    (tagcase z
      (sz-finite () "finite")
      (sz-lin (k ts)
        (let ((parts (k-show-terms ts)))
          (cond ((null? parts) (int->string k))
                ((and (null? (cdr parts)) (= k 0)) (car parts))
                ((and (null? (cdr parts)) (< k 0))
                 (k-cat5 "(- " (car parts) " " (int->string (- 0 k)) ")"))
                ((= k 0) (k-cat3 "(+ " (k-join parts " ") ")"))
                (else (k-cat5 "(+ " (k-join parts " ") " " (int->string k) ")"))))))))
;; How an `nlist` type ends: with the place it is frozen into, if not the
;; heap.
(define k-nlist-end (->* (k-region) string)
  (lambda (r)
    (tagcase r
      (r-frozen (q f) (if (>= q 0) (k-cat3 " " (k-dvar-string q) ")") ")"))
      (else y ")"))))
;; `(conv C) `, where a `subr` type's convention `C` is not the program's;
;; nothing where it is.
(define k-conv-prefix (->* (k-conv) string)
  (lambda (cv) (if (k-conv=? cv (get k-conv-default)) "" (k-cat3 "(conv " (k-conv-show cv) ") "))))

;; Abstract type `n`, variable `v`: ` (abs n kind)`.
(define k-show-abs-one (->* (symbol int) string)
  (lambda (n v)
    ;; `v` is bound here, as a `poly`'s binders are.
    (let ((bound (k-dvar-text v "h")))
      (k-cat5 " (abs " (symbol->string n) bound " "
              (k-cat3 (k-kind-text (k-dvar-kind v)) ")" "")))))
;; A module type's abstract types: ` (abs t type)` each.
(define k-show-abs (->* (k-parts) string)
  (lambda (ps)
    (if (null? ps)
        ""
        (string-append (k-show-abs-one (extract (car ps) 1) (extract (car ps) 2))
                       (k-show-abs (cdr ps))))))

(define k-printing-none k-printing
  (product (1 (the k-ids nil)) (2 (the k-parts nil)) (3 (the k-atrees nil))))
;; `p` with the names of descriptions `ds` too.
(define k-printing-named (->* (k-printing k-parts) k-printing)
  (lambda (p ds)
    (product (1 (extract p 1)) (2 (k-parts-onto-front ds (extract p 2))) (3 (extract p 3)))))
(define k-parts-onto-front (->* (k-parts k-parts) k-parts)
  (lambda (ps acc)
    (if (null? ps) acc (k-parts-onto-front (cdr ps) (the k-parts (cons (car ps) acc))))))
;; The name of the part of `ps` that is type `t`, in a list; none if none.
(define k-part-named (->* (k-parts int) k-strings)
  (lambda (ps t)
    (cond ((null? ps) nil)
          ((= (k-resolve (extract (car ps) 2)) t)
           (the k-strings (cons (symbol->string (extract (car ps) 1)) nil)))
          (else (k-part-named (cdr ps) t)))))

;; A shape's name (`check-unions.fx`'s numbers).
(define k-shape-name (->* (int) string)
  (lambda (k)
    (case k
      ((0) "int") ((1) "f64") ((2) "f32") ((3) "char") ((4) "bool") ((5) "nil") ((6) "pair")
      ((7) "string") ((8) "symbol") ((9) "procedure") ((10) "bloblet") ((11) "box")
      ((12) "sum") (else "product"))))
;; A proposition, and a size in one, as written.
(define k-show-term (->* (k-term) string)
  (lambda (t)
    (tagcase t
      (tm-param (i) (int->string i))
      (tm-length (i) (k-cat3 "(length " (int->string i) ")"))
      (tm-lit (k) (k-cat3 "(lit " (int->string k) ")")))))
(define k-show-prop (->* (k-prop) string)
  (lambda (p)
    (tagcase p
      (pr-shape (i k f)
        (let ((shape (k-cat5 "(shape " (int->string i) " " (k-shape-name k) ")")))
          (if f (k-cat3 "(not " shape ")") shape)))
      (pr-acyclic (i) (k-cat3 "(acyclic " (int->string i) ")"))
      (pr-nat (i) (k-cat3 "(nat " (int->string i) ")"))
      (pr-length (i j) (k-cat5 "(length " (int->string i) " " (int->string j) ")"))
      (pr-rel (o a b)
        (let* ((name (case o ((0) "<") ((1) "<=") (else "=")))
               (r (k-cat5 (k-cat3 "(" name " ") (k-show-term a) " " (k-show-term b) ")")))
          (if (= o 3) (k-cat3 "(not " r ")") r))))))
(define k-show-props-each (->* (k-props) string)
  (lambda (ps)
    (if (null? ps)
        ""
        (k-cat3 " " (k-show-prop (car ps)) (k-show-props-each (cdr ps))))))
(define k-show-props (->* (string k-props) string)
  (lambda (which ps) (k-cat4 "(" which (k-show-props-each ps) ")")))
;; Marks, as `k-show-apart` reads them: how each is printed, and its
;; variable; and the names given some.
(define-type k-marks (listof (pairof string int @t) acyclic))
(define-type k-primes (listof (pairof int string @t) acyclic))
;; The number written in `s` from `i` to `j`, after `n`.
(define k-digits (->* (string int int int) int)
  (lambda (s i j n)
    (if (>= i j)
        n
        (k-digits s (+ i 1) j (+ (* n 10) (- (char->integer (string-ref s i)) 48))))))
;; The marks in `s` from `i`, in order.
(define k-marks-in (->* (string int) k-marks)
  (lambda (s i)
    (let ((a (string-search s k-mark i)))
      (if (< a 0)
          nil
          (let ((b (string-search s k-mark (+ a 1))))
            (cons (cons (substring s (+ a 1) (+ a 2)) (k-digits s (+ a 2) b 0))
                  (k-marks-in s (+ b 1))))))))
;; The marks in each of `ss`, in order.
(define k-marks-all (->* (k-strings) k-marks)
  (lambda (ss) (if (null? ss) nil (append (k-marks-in (car ss) 0) (k-marks-all (cdr ss))))))
(define k-id-in? (->* (int k-ids) bool)
  (lambda (v vs) (and (not (null? vs)) (or (= (car vs) v) (k-id-in? v (cdr vs))))))
;; Whether `v` is printed bound among `ms`.
(define k-mark-bound? (->* (int k-marks) bool)
  (lambda (v ms)
    (and (not (null? ms))
         (or (and (= (cdr (car ms)) v) (not (string=? (car (car ms)) "f")))
             (k-mark-bound? v (cdr ms))))))
;; The variables of `ms` from `rest` on that are free, each once, in the
;; order they are read, after `acc` (reversed).
(define k-free-marks (->* (k-marks k-marks k-ids) k-ids)
  (lambda (rest ms acc)
    (if (null? rest)
        (reverse acc)
        (let ((v (cdr (car rest))))
          (k-free-marks (cdr rest) ms
                        (if (or (k-id-in? v acc) (k-mark-bound? v ms)) acc (cons v acc)))))))
;; Those of `vs` named `n`.
(define k-named-like (->* (k-ids symbol) k-ids)
  (lambda (vs n)
    (cond ((null? vs) nil)
          ((symbol=? (k-dvar-name (car vs)) n) (cons (car vs) (k-named-like (cdr vs) n)))
          (else (k-named-like (cdr vs) n)))))
;; `n` primed `k` times.
(define k-primed (->* (string int) string)
  (lambda (n k) (if (= k 0) n (k-primed (string-append n "'") (- k 1)))))
;; `vs`, named `n` primed 0, 1, … times from `k`, onto `acc`.
(define k-primes-of (->* (k-ids string int k-primes) k-primes)
  (lambda (vs n k acc)
    (if (null? vs)
        acc
        (k-primes-of (cdr vs) n (+ k 1) (cons (cons (car vs) (k-primed n k)) acc)))))
(define k-prime-of (->* (int k-primes) string)
  (lambda (v ps) (cond ((null? ps) "") ((= (car (car ps)) v) (cdr (car ps)))
                       (else (k-prime-of v (cdr ps))))))
(define k-primed? (->* (int k-primes) bool)
  (lambda (v ps) (and (not (null? ps)) (or (= (car (car ps)) v) (k-primed? v (cdr ps))))))
;; "`a`, `a'` and `a''`": names `k` to `n`-1 of `x`, quoted, after `acc`.
(define k-primes-said (->* (string int int string) string)
  (lambda (x k n acc)
    (let ((q (k-cat3 "`" (k-primed x k) "`")))
      (cond ((= k n) acc)
            ((= k 0) (k-primes-said x 1 n q))
            ((= k (- n 1)) (k-primes-said x (+ k 1) n (k-cat3 acc " and " q)))
            (else (k-primes-said x (+ k 1) n (k-cat3 acc ", " q)))))))
;; The names `free` from `rest` on are given where two share a name,
;; after `ps`, and the lines that say so, after `hint`.
(define k-prime-all (->* (k-ids k-ids k-primes string) (pairof k-primes string @t))
  (lambda (rest free ps hint)
    (if (null? rest)
        (cons ps hint)
        (let* ((v (car rest)) (n (k-dvar-name v)) (same (k-named-like free n))
               (x (symbol->string n)) (count (k-length same)))
          (if (or (k-primed? v ps) (< count 2))
              (k-prime-all (cdr rest) free ps hint)
              (k-prime-all (cdr rest) free (k-primes-of same x 0 ps)
                           (string-append hint
                                          (k-cat5 (char->string (integer->char 10)) "  "
                                                  (k-primes-said x 0 count "")
                                                  " are different variables, each named "
                                                  (k-cat3 "`" x "`")))))))))
;; `s` from `i`, each mark named as `ps` says or by its variable's name;
;; an `h` mark by nothing.
(define k-named-marks (->* (string int k-primes) string)
  (lambda (s i ps)
    (let ((a (string-search s k-mark i)))
      (if (< a 0)
          (substring s i (string-length s))
          (let* ((b (string-search s k-mark (+ a 1)))
                 (how (substring s (+ a 1) (+ a 2)))
                 (v (k-digits s (+ a 2) b 0))
                 (name (cond ((string=? how "h") "")
                             ((k-primed? v ps) (k-prime-of v ps))
                             (else (symbol->string (k-dvar-name v))))))
            (k-cat3 (substring s i a) name (k-named-marks s (+ b 1) ps)))))))
(define k-named-each (->* (k-strings k-primes) k-strings)
  (lambda (ss ps)
    (if (null? ss) nil (cons (k-named-marks (car ss) 0 ps) (k-named-each (cdr ss) ps)))))
;; `ss`, printed with `k-show-marks` on, with two free variables of one name
;; told apart: the first, in the order they are read, keeps its name, the
;; next is primed, `a'`, and so on; then a line for each such name saying
;; so, all in one string, or "" (`Checker::show_apart`).
(define k-show-apart (->* (k-strings) k-strings)
  (lambda (ss)
    (let* ((ms (k-marks-all ss)) (free (k-free-marks ms ms nil))
           (named (k-prime-all free free nil "")))
      (append (k-named-each ss (car named)) (list (cdr named))))))
)))
