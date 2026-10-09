;;; The checker, in FX-26: types and effects shown as the Rust checker shows
;;; them; and what a type holds: where a procedure kept in it could reach
;;; itself, and at which polarities a variable occurs in it.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ printing

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
;; Its types (`check-print-types.fx`), loaded before the module so that they are not
;; among its values; the module names what it uses of them.
(define check-print-types (load-module "fx26:check-print-types.fx"))
(define check-print-module (module
(define-type k-atree (select check-print-types k-atree))
(define a-leaf (with check-print-types a-leaf))
(define a-node (with check-print-types a-node))
(define-type k-atrees (select check-print-types k-atrees))
(define-type k-named-at (select check-print-types k-named-at))
(define-type k-size-fact (select check-print-types k-size-fact))
(define-type k-lins (select check-print-types k-lins))
(define-type k-printing (select check-print-types k-printing))
(define-effect kshows (select check-print-types kshows))

;; A description variable's name.
(define k-dvar-string (subr kreads (int) string)
  (lambda (v) (symbol->string (k-dvar-name v))))
;; `(const p)` or `(acyclic p)`, frozen into place `p`; or, for the heap
;; (-1), `const` or `acyclic`.
(define k-frozen-show (subr kreads (int bool) string)
  (lambda (p f)
    (let ((word (if f "acyclic" "const")))
      (if (< p 0) word (k-cat5 "(" word " " (k-dvar-string p) ")")))))
(define k-region-show (subr kreads (k-region) string)
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
(define k-region-atom-show (subr kreads (string k-region) string)
  (lambda (op r) (k-cat5 "(" op " " (k-region-show r) ")")))
(define-rec
  (k-atom-show (subr kreads (k-atom) string)
    (lambda (a)
      (tagcase a
        (a-read (r) (k-region-atom-show "read" r))
        (a-write (r) (k-region-atom-show "write" r))
        (a-alloc (r) (k-region-atom-show "alloc" r))
        (a-goto (r) (k-region-atom-show "goto" r))
        (a-comefrom (r) (k-region-atom-show "comefrom" r))
        (a-await (r) (k-region-atom-show "await" r))
        (a-spin () "spin")
        (a-var (v) (k-dvar-string v))
        (a-app (v ds) (k-cat4 "(" (k-dvar-string v) (k-eargs-show ds) ")")))))
  ;; What an effect application was given, each after a space.
  (k-eargs-show (subr kreads (k-descs) string)
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
  (k-eff-show-plain (subr kreads (k-eff) string)
    (lambda (e)
      (cond ((null? e) "pure")
            ((null? (cdr e)) (k-atom-show (car e)))
            (else (k-cat3 "(maxeff" (k-atoms-plain e) ")")))))
  (k-atoms-plain (subr kreads (k-eff) string)
    (lambda (e) (if (null? e) "" (k-cat3 " " (k-atom-show (car e)) (k-atoms-plain (cdr e)))))))
(define k-atoms-show (subr kreads (k-eff) string)
  (lambda (e) (if (null? e) "" (k-cat3 " " (k-atom-show (car e)) (k-atoms-show (cdr e))))))
(define k-strings-append (subr (read @globals) (k-strings k-strings) k-strings)
  (lambda (xs ys)
    (if (null? xs) ys (the k-strings (cons (car xs) (k-strings-append (cdr xs) ys))))))
(define k-strings-spaced (subr (read @globals) (k-strings) string)
  (lambda (xs) (if (null? xs) "" (k-cat3 " " (car xs) (k-strings-spaced (cdr xs))))))
;; ` g`, for the binding of global `g`; nothing for any other region.
(define k-global-shown (subr (read @globals) (k-region) string)
  (lambda (r) (tagcase r (r-global (g) (string-append " " (symbol->string g))) (else y ""))))
;; The names of the globals `e` reads (`op` 0) or writes (1), each after a
;; space, in the order of their text: effects are kept in their hashes'
;; order (`k-atom-cmp`), and put in this one only to be shown.
(define k-globals-shown (subr kreads (k-eff int) string)
  (lambda (e op) (k-names-spaced (k-global-names e op nil))))
(define k-global-names (subr kreads (k-eff int k-names) k-names)
  (lambda (e op acc)
    (if (null? e)
        acc
        (k-global-names (cdr e) op
                        (tagcase (car e)
                          (a-read (r) (if (= op 0) (k-global-name-into r acc) acc))
                          (a-write (r) (if (= op 1) (k-global-name-into r acc) acc))
                          (else y acc))))))
(define k-global-name-into (subr (read @globals) (k-region k-names) k-names)
  (lambda (r acc) (tagcase r (r-global (g) (k-name-insert g acc)) (else y acc))))
;; `g` into `xs`, kept in the order of the names' text.
(define k-name-insert (subr (read @globals) (symbol k-names) k-names)
  (lambda (g xs)
    (if (or (null? xs) (< (symbol-compare g (car xs)) 0))
        (the k-names (cons g xs))
        (the k-names (cons (car xs) (k-name-insert g (cdr xs)))))))
(define k-names-spaced (subr (read @globals) (k-names) string)
  (lambda (xs)
    (if (null? xs)
        ""
        (string-append (string-append " " (symbol->string (car xs))) (k-names-spaced (cdr xs))))))
(define k-one-global? (subr pure (k-atom) bool)
  (lambda (a)
    (tagcase a
      (a-read (r) (tagcase r (r-global (g) #t) (else y #f)))
      (a-write (r) (tagcase r (r-global (g) #t) (else y #f)))
      (else y #f))))
;; Whether `a` is on globals' bindings, which are never masked.
(define k-globals-atom? (subr (read @globals) (k-atom) bool)
  (lambda (a) (and (k-has-region? a) (k-globals-region? (k-atom-region a)))))
;; The atoms of `e` shown, but for those on one global's binding.
(define k-other-atom-strings (subr kreads (k-eff) k-strings)
  (lambda (e)
    (cond ((null? e) nil)
          ((k-one-global? (car e)) (k-other-atom-strings (cdr e)))
          (else (the k-strings (cons (k-atom-show (car e)) (k-other-atom-strings (cdr e))))))))
;; `(op (globals names))`, alone in a list; none if there are no names.
(define k-globals-grouped (subr kreads (string string) k-strings)
  (lambda (op names)
    (if (string=? names "") nil (the k-strings (cons (k-cat5 "(" op " (globals" names "))") nil)))))
;; The atoms shown, reads, or writes, of several globals being one atom:
;; `(read (globals f g))`.
(define k-atom-strings (subr kreads (k-eff) k-strings)
  (lambda (e)
    (let* ((others (k-other-atom-strings e))
           (reads (k-globals-grouped "read" (k-globals-shown e 0)))
           (writes (k-globals-grouped "write" (k-globals-shown e 1))))
      (k-strings-append others (k-strings-append reads writes)))))
;; `pure`, a single atom, or `…`.
(define k-show-effect (subr (maxeff (read @globals) (read @t)) (k-eff) string)
  (lambda (e)
    (let ((xs (k-atom-strings e)))
      (cond ((null? xs) "pure")
            ((null? (cdr xs)) (car xs))
            (else (k-cat3 "(maxeff" (k-strings-spaced xs) ")"))))))

(define k-kind-name (subr pure (int) string)
  (lambda (k)
    (case k ((0) "region")
            ((1) "effect")
            ((3) "place")
            ((4) "data")
            ((5) "size")
            ((6) "conv")
            (else "type"))))
;; A convention as a program writes it.
(define k-conv-show (subr kreads (k-conv) string)
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
(define check-conv-native! (subr (maxeff (read @globals) (write @t)) (bool) unit)
  (lambda (on) (set k-conv-default (if on (cv-native) (cv-cellular)))))
(define k-conv=? (subr (read @globals) (k-conv k-conv) bool)
  (lambda (a b) (= (k-conv-code a) (k-conv-code b))))
;; As Rust's `{:?}` writes a kind.
(define k-kind-debug (subr pure (int) string)
  (lambda (k)
    (case k ((0) "Region")
            ((1) "Effect")
            ((3) "Place")
            ((4) "Data")
            ((5) "Size")
            ((6) "Conv")
            (else "Type"))))
(define-rec
  ;; A kind as it is written: `type`, or `(=> (type) type)`.
  (k-kind-text (subr (maxeff kreads (alloc @t) spin) (int) string)
    (lambda (k)
      (let ((a (k-arrow-parts k)))
        (if (null? a)
            (k-kind-name k)
            (k-cat5 "(=> (" (k-join (k-kinds-text (car (car a))) " ") ") "
                    (k-kind-text (cdr (car a))) ")")))))
  (k-kinds-text (subr (maxeff kreads (alloc @t) spin) (k-ids) k-strings)
    (lambda (ks)
      (if (null? ks) nil (cons (k-kind-text (car ks)) (k-kinds-text (cdr ks)))))))
;; A kind as the older messages name it, `Region`, `Type`, …; an arrow
;; kind as it is written.
(define k-kind-word (subr (maxeff kreads (alloc @t) spin) (int) string)
  (lambda (k) (if (k-arrow-kind? k) (k-kind-text k) (k-kind-debug k))))
;; Whether a region is a place: a variable bound as one.
(define k-place? (subr (maxeff (read @globals) (read @t)) (k-region) bool)
  (lambda (r) (tagcase r (r-var (v) (k-place-var? v)) (r-heap () #t) (else x #f))))

;; Whether one of the first `i` bindings of `ds` is a `define-type` of `n`.
(define k-rec-named-within? (subr (maxeff (read @globals) (read @t)) (k-scope int symbol) bool)
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
(define k-abbrev-in (subr kbuilds (k-scope k-scope int int) k-strings)
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
(define k-scramble (subr pure (int) int) (lambda (t) (remainder (* t 40503) 65521)))
(define-rec
  (k-atree-put (subr spin (k-atree int int symbol int) k-atree)
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
  (k-atree-get (subr (maxeff (read @globals) spin) (k-atree int int) k-named-at)
    (lambda (tr h t)
      (tagcase tr
        (a-leaf () nil)
        (a-node (h2 t2 n2 i2 l r)
          (cond ((or (< h h2) (and (= h h2) (< t t2))) (k-atree-get l h t))
                ((or (> h h2) (and (= h h2) (> t t2))) (k-atree-get r h t))
                (else (the k-named-at (list (product (1 n2) (2 i2)))))))))))
;; Every `define-type` of scope `ds`, from binding `i` on, into `tr`.
(define k-atree-of (subr (maxeff kreads spin) (k-scope int k-atree) k-atree)
  (lambda (ds i tr)
    (if (null? ds)
        tr
        (tagcase (cdr (car ds))
          (ds-rec (d)
            (let ((t (k-resolve d)))
              (k-atree-of (cdr ds) (+ i 1) (k-atree-put tr (k-scramble t) t (car (car ds)) i))))
          (else y (k-atree-of (cdr ds) (+ i 1) tr))))))
;; Scope `ds` from binding `i` on.
(define k-scope-from (subr (read @globals) (k-scope int) k-scope)
  (lambda (ds i) (if (or (<= i 0) (null? ds)) ds (k-scope-from (cdr ds) (- i 1)))))
;; The name `define-type` gave `t`, as `k-abbrev-in` finds it, by tree `trs`
;; if there is one.
(define k-abbrev-by (subr kbuilds (k-atrees int) k-strings)
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
(define k-binder-show (subr kbuilds (int int) string)
  (lambda (v kind)
    (let* ((b (k-bound-of v)) (named (k-cat3 (k-dvar-string v) " " (k-kind-text kind))))
      (if (null? b) (k-cat3 "(" named ")") (k-cat5 "(" named " " (k-region-show (car b)) ")")))))
(define k-show-binders (subr kbuilds (k-binders) k-strings)
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((b (car bs)))
          (cons (k-binder-show (extract b 1) (extract b 2)) (k-show-binders (cdr bs)))))))

;; How deep `t` is in `path`, newest first: its place from the root, from 1.
(define k-depth-of (subr (maxeff (read @globals) (read @t)) (k-ids int) int)
  (lambda (path t) (if (= (car path) t) (k-length path) (k-depth-of (cdr path) t))))
;; Sizes: a literal, `finite`, one more or less, and whether one list's
;; size is another's.
(define k-size-lit (subr (read @globals) (int) k-size) (lambda (k) (sz-lin k nil)))
;; The literal a size is, or -1.
(define k-size-as-lit (subr pure (k-size) int)
  (lambda (z) (tagcase z (sz-lin (k ts) (if (null? ts) k -1)) (else y -1))))
(define k-size-plus (subr (read @globals) (k-size int) k-size)
  (lambda (z d) (tagcase z (sz-lin (k ts) (sz-lin (+ k d) ts)) (else y z))))
;; Whether two terms are one variable with one coefficient.
(define k-term=? (subr pure ((pairof int int acyclic) (pairof int int acyclic)) bool)
  (lambda (x y) (and (= (car x) (car y)) (= (cdr x) (cdr y)))))
(define k-terms=? (subr (read @globals) (k-terms k-terms) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys)) (k-term=? (car xs) (car ys)) (k-terms=? (cdr xs) (cdr ys))))))
(define k-size=? (subr (read @globals) (k-size k-size) bool)
  (lambda (a b)
    (tagcase a
      (sz-finite () (tagcase b (sz-finite () #t) (else y #f)))
      (sz-lin (k ts) (tagcase b (sz-lin (k2 ts2) (and (= k k2) (k-terms=? ts ts2))) (else y #f))))))

(define k-map-find (subr kreads (k-map int) k-map)
  (lambda (m v) (cond ((null? m) nil) ((= (car (car m)) v) m) (else (k-map-find (cdr m) v)))))
;; Linear sizes (`src/sizes.rs`): a variable; `a + c·b`; `v` replaced.
(define k-size-var (subr (read @globals) (int) k-size)
  (lambda (v) (sz-lin 0 (the k-terms (cons (cons v 1) nil)))))
;; Term `n·v` before `rest`, unless `n` is zero.
(define k-term-cons (subr (read @globals) (int int k-terms) k-terms)
  (lambda (v n rest) (if (= n 0) rest (the k-terms (cons (cons v n) rest)))))
;; `xs + c·ys`, terms in variable order, none zero.
(define k-terms-add (subr (read @globals) (k-terms k-terms int) k-terms)
  (lambda (xs ys c)
    (cond ((null? ys) xs)
          ((or (null? xs) (> (car (car xs)) (car (car ys))))
           (k-term-cons (car (car ys)) (* c (cdr (car ys))) (k-terms-add xs (cdr ys) c)))
          ((< (car (car xs)) (car (car ys)))
           (the k-terms (cons (car xs) (k-terms-add (cdr xs) ys c))))
          (else (let ((n (+ (cdr (car xs)) (* c (cdr (car ys))))))
                  (k-term-cons (car (car xs)) n (k-terms-add (cdr xs) (cdr ys) c)))))))
(define k-size-add-scaled (subr (read @globals) (k-size k-size int) k-size)
  (lambda (a b c)
    (tagcase a
      (sz-lin (k ts)
        (tagcase b
          (sz-lin (k2 ts2) (sz-lin (+ k (* c k2)) (k-terms-add ts ts2 c)))
          (else y (sz-finite))))
      (else y (sz-finite)))))
(define k-coef-of (subr (read @globals) (k-terms int) int)
  (lambda (ts v)
    (cond ((null? ts) 0) ((= (car (car ts)) v) (cdr (car ts))) (else (k-coef-of (cdr ts) v)))))
(define k-size-replace (subr (read @globals) (k-size int k-size) k-size)
  (lambda (s v by)
    (tagcase s
      (sz-lin (k ts)
        (let ((c (k-coef-of ts v)))
          (if (= c 0) s (k-size-add-scaled (k-size-add-scaled s (k-size-var v) (- 0 c)) by c))))
      (else y (sz-finite)))))
(define k-size-facts (ref (listof k-size-fact acyclic) @t) (new nil))
;; The terms from the first whose coefficient is 1 or -1 on.
(define k-unit-terms (subr (read @globals) (k-terms) k-terms)
  (lambda (xs)
    (cond ((null? xs) xs)
          ((or (= (cdr (car xs)) 1) (= (cdr (car xs)) -1)) xs)
          (else (k-unit-terms (cdr xs))))))
;; `s` with the variable fact `f` determines rewritten away: one of
;; coefficient 1 or -1 in an equality. `s` itself if there is none.
(define k-apply-fact (subr (read @globals) (k-size k-size-fact) k-size)
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
(define k-reduced (subr kreads (k-size) k-size)
  (lambda (s)
    (letrec ((go (subr (read @globals) (k-size (listof k-size-fact acyclic)) k-size)
                   (lambda (s fs) (if (null? fs) s (go (k-apply-fact s (car fs)) (cdr fs))))))
      (go s (the (listof k-size-fact acyclic) (reverse (get k-size-facts)))))))
;; Whether no term's coefficient is negative.
(define k-coefs-nonneg? (subr (read @globals) (k-terms) bool)
  (lambda (xs) (or (null? xs) (and (>= (cdr (car xs)) 0) (k-coefs-nonneg? (cdr xs))))))
;; Whether a size is plainly non-negative: every size is a natural.
(define k-plainly-nonneg? (subr (read @globals) (k-size) bool)
  (lambda (s) (tagcase s (sz-lin (k ts) (and (>= k 0) (k-coefs-nonneg? ts))) (else y #f))))
;; Whether, for some fact `f ≥ 0` of `fs`, `a - f` is plainly non-negative.
(define k-nonneg-by-fact? (subr kreads (k-size (listof k-size-fact acyclic)) bool)
  (lambda (a fs)
    (and (not (null? fs))
         (or (and (not (extract (car fs) 2))
                  (k-plainly-nonneg? (k-size-add-scaled a (k-reduced (extract (car fs) 1)) -1)))
             (k-nonneg-by-fact? a (cdr fs))))))
;; `gcd(a, b)` of naturals, Euclid's, counting down `fuel` (100 is more
;; steps than any pair of 64-bit numbers takes).
(define k-gcd (subr (read @globals) (int int nat) int)
  (lambda (a b fuel)
    (cond ((= b 0) a) ((= fuel 0) 1) (else (k-gcd b (remainder a b) (- fuel 1))))))
(define k-abs (subr pure (int) int) (lambda (n) (if (< n 0) (- 0 n) n)))
(define k-terms-gcd (subr (read @globals) (k-terms int) int)
  (lambda (ts g) (if (null? ts) g (k-terms-gcd (cdr ts) (k-gcd g (k-abs (cdr (car ts))) 100)))))
(define k-terms-div (subr (read @globals) (k-terms int) k-terms)
  (lambda (ts g)
    (if (null? ts)
        nil
        (let ((t (the (pairof int int acyclic) (cons (car (car ts)) (quotient (cdr (car ts)) g)))))
          (the k-terms (cons t (k-terms-div (cdr ts) g)))))))
;; `c ≥ 0` as integers allow: its coefficients divided by their gcd, its
;; constant rounded down after the same division.
(define* k-tightened (subr pure (k-size) k-size)
  (lambda (c)
    (tagcase c
      (sz-lin (k ts)
        (let ((g (k-terms-gcd ts 0)))
          (if (<= g 1) c (sz-lin (quotient (- k (modulo k g)) g) (k-terms-div ts g)))))
      (else y c))))
;; Variable `v` added to the sorted `vs`, once.
(define k-var-into (subr (read @globals) (k-ids int) k-ids)
  (lambda (vs v)
    (cond ((null? vs) (the k-ids (cons v nil)))
          ((= (car vs) v) vs)
          ((< v (car vs)) (the k-ids (cons v vs)))
          (else (the k-ids (cons (car vs) (k-var-into (cdr vs) v)))))))
(define k-terms-vars (subr (read @globals) (k-terms k-ids) k-ids)
  (lambda (ts vs) (if (null? ts) vs (k-terms-vars (cdr ts) (k-var-into vs (car (car ts)))))))
;; The variables of `cs`, sorted, each once.
(define k-lins-vars (subr (read @globals) (k-lins k-ids) k-ids)
  (lambda (cs vs)
    (if (null? cs)
        vs
        (let ((more (tagcase (car cs) (sz-lin (k ts) (k-terms-vars ts vs)) (else y vs))))
          (k-lins-vars (cdr cs) more)))))
(define k-lins-append (subr (read @globals) (k-lins k-lins) k-lins)
  (lambda (xs ys) (if (null? xs) ys (the k-lins (cons (car xs) (k-lins-append (cdr xs) ys))))))
;; `v ≥ 0` for each of `vs`.
(define k-lins-of-vars (subr (read @globals) (k-ids) k-lins)
  (lambda (vs)
    (if (null? vs) nil (the k-lins (cons (k-size-var (car vs)) (k-lins-of-vars (cdr vs)))))))
(define k-coef-in (subr (read @globals) (k-size int) int)
  (lambda (c v) (tagcase c (sz-lin (k ts) (k-coef-of ts v)) (else y 0))))
(define k-sign (subr pure (int) int) (lambda (n) (cond ((< n 0) -1) ((> n 0) 1) (else 0))))
;; Those of `cs` whose coefficient of `v` has the sign `s` (-1, 0 or 1).
(define k-lins-signed (subr (read @globals) (k-lins int int) k-lins)
  (lambda (cs v s)
    (cond ((null? cs) nil)
          ((= (k-sign (k-coef-in (car cs) v)) s)
           (the k-lins (cons (car cs) (k-lins-signed (cdr cs) v s))))
          (else (k-lins-signed (cdr cs) v s)))))
;; `p` with each of `ns`, scaled so that `v` cancels, tightened, onto `acc`.
(define k-lins-cancel (subr (read @globals) (k-size k-lins int k-lins) k-lins)
  (lambda (p ns v acc)
    (if (null? ns)
        acc
        (let* ((n (car ns)) (x (k-coef-in p v)) (y (- 0 (k-coef-in n v)))
               (c (k-tightened (k-size-add-scaled (k-size-add-scaled (k-size-lit 0) p y) n x))))
          (k-lins-cancel p (cdr ns) v (the k-lins (cons c acc)))))))
(define k-lins-combined (subr (read @globals) (k-lins k-lins int k-lins) k-lins)
  (lambda (ps ns v acc)
    (if (null? ps) acc (k-lins-combined (cdr ps) ns v (k-lins-cancel (car ps) ns v acc)))))
;; How many of `cs` there are, and `n`.
(define k-lins-count (subr (read @globals) (k-lins int) int)
  (lambda (cs n) (if (null? cs) n (k-lins-count (cdr cs) (+ n 1)))))
;; Whether some constraint of `cs` is a constant below 0.
(define k-lins-contradict? (subr (read @globals) (k-lins) bool)
  (lambda (cs)
    (and (not (null? cs))
         (or (tagcase (car cs) (sz-lin (k ts) (and (null? ts) (< k 0))) (else y #f))
             (k-lins-contradict? (cdr cs))))))
;; Each of `vs`, lowest first, eliminated from `cs`; giving up past 64.
(define k-fm-eliminate (subr (read @globals) (k-lins k-ids) bool)
  (lambda (cs vs)
    (if (null? vs)
        (k-lins-contradict? cs)
        (let* ((v (car vs))
               (next (k-lins-combined (k-lins-signed cs v 1) (k-lins-signed cs v -1) v
                                      (k-lins-signed cs v 0))))
          (if (> (k-lins-count next 0) 64) #f (k-fm-eliminate next (cdr vs)))))))
;; The inequalities in scope, oldest first, reduced, `finite` left out.
(define k-fact-lins (subr kreads ((listof k-size-fact acyclic)) k-lins)
  (lambda (fs)
    (cond ((null? fs) nil)
          ((extract (car fs) 2) (k-fact-lins (cdr fs)))
          (else (let ((c (k-reduced (extract (car fs) 1))))
                  (tagcase c
                    (sz-lin (k ts) (the k-lins (cons c (k-fact-lins (cdr fs)))))
                    (else y (k-fact-lins (cdr fs)))))))))
(define* k-refuted-below? (subr kreads (k-size) bool)
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
(define k-size-nonneg? (subr kreads (k-size) bool)
  (lambda (a0)
    (let ((a (k-reduced a0)))
      (or (k-plainly-nonneg? a)
          (k-nonneg-by-fact? a (the (listof k-size-fact acyclic) (reverse (get k-size-facts))))
          (k-refuted-below? a)))))
;; Whether the facts reduce `s` to 0.
(define k-size-zero? (subr kreads (k-size) bool)
  (lambda (s) (k-size=? (k-reduced s) (k-size-lit 0))))
;; Whether the facts show `a = b`.
(define k-size-eq? (subr kreads (k-size k-size) bool)
  (lambda (a b)
    (tagcase a
      (sz-finite () (tagcase b (sz-finite () #t) (else y #f)))
      (else y (tagcase b (sz-finite () #f) (else w (k-size-zero? (k-size-add-scaled a b -1))))))))
;; The size of the tail of a list of size `n`: one less, where the facts
;; show `n ≥ 1`; `finite` otherwise.
(define k-tail-size (subr kreads (k-size) k-size)
  (lambda (n)
    (tagcase n
      (sz-finite () n)
      (else y (let ((less (k-size-plus n -1))) (if (k-size-nonneg? less) less (sz-finite)))))))
;; Whether a list of size `m` is one of size `n`: the facts show them
;; equal, or `n` is `finite`.
(define k-size-le? (subr kreads (k-size k-size) bool)
  (lambda (m n) (or (tagcase n (sz-finite () #t) (else y #f)) (k-size-eq? m n))))
;; `out` with variable `v` replaced by the size `m` gives it, if any.
(define k-size-given (subr kreads (k-size int k-map) k-size)
  (lambda (out v m)
    (let ((f (k-map-find m v)))
      (if (null? f) out (tagcase (cdr (car f)) (dz (by) (k-size-replace out v by)) (else y out))))))
;; `s` with `m`'s sizes for its variables.
(define k-subst-size (subr kreads (k-size k-map) k-size)
  (lambda (s m)
    (tagcase s
      (sz-lin (k ts)
        (letrec ((go (subr kreads (k-size k-terms) k-size)
                       (lambda (out xs)
                         (if (null? xs) out (go (k-size-given out (car (car xs)) m) (cdr xs))))))
          (go s ts)))
      (else y s))))
(define k-show-terms (subr kbuilds (k-terms) k-strings)
  (lambda (ts)
    (if (null? ts)
        nil
        (let* ((n (k-dvar-string (car (car ts))))
               (c (cdr (car ts)))
               (x (if (= c 1) n (k-cat5 "(* " (int->string c) " " n ")"))))
          (cons x (k-show-terms (cdr ts)))))))
(define k-show-size (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-size) string)
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
(define k-nlist-end (subr kreads (k-region) string)
  (lambda (r)
    (tagcase r
      (r-frozen (q f) (if (>= q 0) (k-cat3 " " (k-dvar-string q) ")") ")"))
      (else y ")"))))
;; `(conv C) `, where a `subr` type's convention `C` is not the program's;
;; nothing where it is.
(define k-conv-prefix (subr kreads (k-conv) string)
  (lambda (cv) (if (k-conv=? cv (get k-conv-default)) "" (k-cat3 "(conv " (k-conv-show cv) ") "))))

;; Abstract type `n`, variable `v`: ` (abs n kind)`.
(define k-show-abs-one (subr kbuilds (symbol int) string)
  (lambda (n v) (k-cat5 " (abs " (symbol->string n) " " (k-kind-text (k-dvar-kind v)) ")")))
;; A module type's abstract types: ` (abs t type)` each.
(define k-show-abs (subr kbuilds (k-parts) string)
  (lambda (ps)
    (if (null? ps)
        ""
        (string-append (k-show-abs-one (extract (car ps) 1) (extract (car ps) 2))
                       (k-show-abs (cdr ps))))))

(define k-printing-none k-printing
  (product (1 (the k-ids nil)) (2 (the k-parts nil)) (3 (the k-atrees nil))))
;; `p` with the names of descriptions `ds` too.
(define k-printing-named (subr (maxeff (read @globals) (alloc @t)) (k-printing k-parts)
                                k-printing)
  (lambda (p ds)
    (product (1 (extract p 1)) (2 (k-parts-onto-front ds (extract p 2))) (3 (extract p 3)))))
(define k-parts-onto-front (subr (maxeff (read @globals) (alloc @t)) (k-parts k-parts) k-parts)
  (lambda (ps acc)
    (if (null? ps) acc (k-parts-onto-front (cdr ps) (the k-parts (cons (car ps) acc))))))
;; The name of the part of `ps` that is type `t`, in a list; none if none.
(define k-part-named (subr (maxeff kreads spin (alloc @t)) (k-parts int) k-strings)
  (lambda (ps t)
    (cond ((null? ps) nil)
          ((= (k-resolve (extract (car ps) 2)) t)
           (the k-strings (cons (symbol->string (extract (car ps) 1)) nil)))
          (else (k-part-named (cdr ps) t)))))

;; A shape's name (`check-unions.fx`'s numbers).
(define k-shape-name (subr pure (int) string)
  (lambda (k)
    (case k
      ((0) "int") ((1) "f64") ((2) "f32") ((3) "char") ((4) "bool") ((5) "nil") ((6) "pair")
      ((7) "string") ((8) "symbol") ((9) "procedure") ((10) "bloblet") ((11) "box")
      ((12) "sum") (else "product"))))
;; A proposition, and a size in one, as written.
(define k-show-term (subr kshows (k-term) string)
  (lambda (t)
    (tagcase t
      (tm-param (i) (int->string i))
      (tm-length (i) (k-cat3 "(length " (int->string i) ")"))
      (tm-lit (k) (k-cat3 "(lit " (int->string k) ")")))))
(define k-show-prop (subr kshows (k-prop) string)
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
(define k-show-props-each (subr kshows (k-props) string)
  (lambda (ps)
    (if (null? ps)
        ""
        (k-cat3 " " (k-show-prop (car ps)) (k-show-props-each (cdr ps))))))
(define k-show-props (subr kshows (string k-props) string)
  (lambda (which ps) (k-cat4 "(" which (k-show-props-each ps) ")")))
;; What a type is shown as so far: its pieces, the last first, joined
;; once, at the end (`k-pieces-string`), so that each character is written
;; once, not again at each node above it, as appending did; the depths of
;; the nodes met again below (`%d`), each to be written `(mu %d …)`; and how
;; many pieces there are.
(define-type k-shown (productof (1 k-strings) (2 k-ids) (3 int)))
(define k-shown-none k-shown (product (1 (the k-strings nil)) (2 (the k-ids nil)) (3 0)))
;; `st`, then `s`.
(define k-put (subr (read @globals) (string k-shown) k-shown)
  (lambda (s st)
    (product (1 (the k-strings (cons s (extract st 1)))) (2 (extract st 2))
             (3 (+ (extract st 3) 1)))))
;; `st`, its depths `ds`.
(define k-shown-depths (subr pure (k-shown k-ids) k-shown)
  (lambda (st ds) (product (1 (extract st 1)) (2 ds) (3 (extract st 3)))))
;; `ds` without `d`.
(define k-ids-without (subr (read @globals) (k-ids int) k-ids)
  (lambda (ds d)
    (cond ((null? ds) ds)
          ((= (car ds) d) (k-ids-without (cdr ds) d))
          (else (the k-ids (cons (car ds) (k-ids-without (cdr ds) d)))))))
;; The first `k` pieces of `xs`, then `mid`, then the rest: `(mu %d ` put
;; before a node's pieces once it is known to be met again below.
(define k-pieces-before (subr (maxeff (read @globals) spin) (k-strings int string) k-strings)
  (lambda (xs k mid)
    (if (or (<= k 0) (null? xs))
        (the k-strings (cons mid xs))
        (the k-strings (cons (car xs) (k-pieces-before (cdr xs) (- k 1) mid))))))
;; The pieces, the last first, joined: their characters gathered, last to
;; first, into one list in an arena of its own, made a string once.
(define k-pieces-string (subr (maxeff (read @globals) (read @t)) (k-strings) string)
  (lambda (xs)
    (letrena r
      (letrec ((chars (subr (alloc r) (string int (listof char r)) (listof char r))
                 (lambda (s i acc)
                   (if (< i 0) acc (chars s (- i 1) (rcons r (string-ref s i) acc)))))
               (all (subr (maxeff (alloc r) (read @t)) (k-strings (listof char r)) (listof char r))
                 (lambda (xs acc)
                   (if (null? xs)
                       acc
                       (all (cdr xs) (chars (car xs) (- (string-length (car xs)) 1) acc))))))
        (list->string (all xs nil))))))
(define-rec
  (k-show-on (subr kbuilds (int k-printing k-shown) k-shown)
    (lambda (t path st)
      (let* ((t (k-resolve t))
             (named (k-part-named (extract path 2) t))
             (name (if (null? named) (k-abbrev-by (extract path 3) t) named)))
        (if (null? name) (k-show-body t path st) (k-put (car name) st)))))
  ;; Each of `ts`, `sep` between each two.
  (k-show-seq (subr kbuilds (k-ids k-printing string k-shown) k-shown)
    (lambda (ts path sep st)
      (cond ((null? ts) st)
            ((null? (cdr ts)) (k-show-on (car ts) path st))
            (else (k-show-seq (cdr ts) path sep (k-put sep (k-show-on (car ts) path st)))))))
  ;; Each part's ` (label type)`.
  (k-show-parts (subr kbuilds (k-parts k-printing k-shown) k-shown)
    (lambda (ps path st)
      (if (null? ps)
          st
          (let* ((st (k-put (k-cat3 " (" (symbol->string (extract (car ps) 1)) " ") st))
                 (st (k-put ")" (k-show-on (extract (car ps) 2) path st))))
            (k-show-parts (cdr ps) path st)))))
  (k-show-desc (subr kbuilds (k-desc k-printing k-shown) k-shown)
    (lambda (d p st)
      (tagcase d
        (dt (t) (k-show-on t p st))
        (dr (r) (k-put (k-region-show r) st))
        (de (e) (k-put (k-show-effect e) st))
        (dz (z) (k-put (k-show-size z) st))
        (dc (c) (k-put (k-conv-show c) st))
        (df (f) (k-show-on f p st)))))
  ;; Each of `ds`, a space between each two.
  (k-show-descs (subr kbuilds (k-descs k-printing k-shown) k-shown)
    (lambda (ds p st)
      (cond ((null? ds) st)
            ((null? (cdr ds)) (k-show-desc (car ds) p st))
            (else (k-show-descs (cdr ds) p (k-put " " (k-show-desc (car ds) p st)))))))
  ;; A `subr` type.
  (k-show-subr (subr kbuilds (k-eff k-ids int k-conv k-printing k-shown) k-shown)
    (lambda (e ps r cv p st)
      (let* ((st (k-put (k-cat5 "(subr " (k-conv-prefix cv) (k-show-effect e) " (" "") st))
             (st (k-put ") " (k-show-seq ps p " " st))))
        (k-put ")" (k-show-on r p st)))))
  ;; `(head a h e r)`: a prompt tag's type, or a composable continuation's.
  (k-show-control (subr kbuilds (string int int k-eff k-region k-printing k-shown) k-shown)
    (lambda (head a h e r p st)
      (let* ((st (k-put " " (k-show-on a p (k-put head st))))
             (st (k-show-on h p st)))
        (k-put (k-cat5 " " (k-show-effect e) " " (k-region-show r) ")") st))))
  ;; `(head a r)`.
  (k-show-in-region (subr kbuilds (string int k-region k-printing k-shown) k-shown)
    (lambda (head a r p st)
      (k-put (k-cat3 " " (k-region-show r) ")") (k-show-on a p (k-put head st)))))
  ;; A node met again on the way down is a cycle: named by its depth, and
  ;; written `(mu %d …)` where the cycle starts, once its pieces are known
  ;; to name it.
  (k-show-body (subr kbuilds (int k-printing k-shown) k-shown)
    (lambda (t path st)
      (let ((ids (extract path 1)))
        (if (k-has-id? ids t)
            (let ((d (k-depth-of ids t)))
              (k-put (string-append "%" (int->string d))
                     (if (k-has-id? (extract st 2) d)
                         st
                         (k-shown-depths st (the k-ids (cons d (extract st 2)))))))
            (let* ((p (product (1 (the k-ids (cons t ids))) (2 (extract path 2))
                               (3 (extract path 3))))
                   (d (k-length (extract p 1)))
                   (out (k-show-node t p st)))
              (if (k-has-id? (extract out 2) d)
                  (let ((mu (k-cat3 "(mu %" (int->string d) " "))
                        (n (- (extract out 3) (extract st 3))))
                    (product (1 (the k-strings
                                  (cons ")" (k-pieces-before (extract out 1) n mu))))
                             (2 (k-ids-without (extract out 2) d))
                             (3 (+ (extract out 3) 2))))
                  out))))))
  ;; What node `t` shows as, `p` the path to it from the root, newest
  ;; first.
  (k-show-node (subr kbuilds (int k-printing k-shown) k-shown)
    (lambda (t p st)
      (tagcase (k-get t)
        (ty-base (s) (k-put (symbol->string s) st))
        (ty-void () (k-put "void" st))
        (ty-nil () (k-put "nil" st))
        (ty-false () (k-put "false" st))
        (ty-union (ms) (k-put ")" (k-show-seq ms p " " (k-put "(union " st))))
        (ty-proving (t e)
          (k-put (k-cat5 "(bool " (k-show-props "then" t) " " (k-show-props "else" e) ")") st))
        (ty-var (v) (k-put (k-dvar-string v) st))
        (ty-link (x) (k-put "?" st))
        (ty-subr (e ps r cv) (k-show-subr e ps r cv p st))
        (ty-poly (bs body)
          (let ((binders (k-join (k-show-binders bs) " ")))
            (k-put ")" (k-show-on body p (k-put (k-cat3 "(poly (" binders ") ") st)))))
        (ty-ref (a r) (k-show-in-region "(ref " a r p st))
        (ty-product (ps) (k-put ")" (k-show-parts ps p (k-put "(productof" st))))
        (ty-sum (ps) (k-put ")" (k-show-parts ps p (k-put "(sumof" st))))
        (ty-array (a r) (k-show-in-region "(arrayof " a r p st))
        (ty-icell (a r) (k-show-in-region "(icell " a r p st))
        (ty-place (r) (k-put (k-cat3 "(place " (k-region-show r) ")") st))
        (ty-pair (a b r nl)
          (if (and nl (= (k-resolve b) t))
              (k-show-in-region "(listof " a r p st)
              (let* ((st (k-put (if nl "(union nil (pairof " "(pairof ") st))
                     (st (k-show-on b p (k-put " " (k-show-on a p st))))
                     (st (k-put (k-cat3 " " (k-region-show r) ")") st)))
                (if nl (k-put ")" st) st))))
        (ty-tag (a h e r) (k-show-control "(prompt-tag " a h e r p st))
        (ty-comp (a h e r) (k-show-control "(composable " a h e r p st))
        (ty-markkey (a r) (k-show-in-region "(mark-key " a r p st))
        (ty-bloblet (fs z r)
          (let* ((head (if z "(bloblet (frozen" "(bloblet (fields"))
                 (st (k-put (if (null? fs) head (string-append head " ")) st))
                 (st (k-show-seq fs p " " st)))
            (k-put (k-cat3 ") " (k-region-show r) ")") st)))
        (ty-nlist (e z r)
          (let ((st (k-show-on e p (k-put "(nlist " st))))
            (k-put (k-cat3 " " (k-show-size z) (k-nlist-end r)) st)))
        (ty-nat (z)
          (k-put (tagcase z (sz-finite () "nat") (else y (k-cat3 "(nat " (k-show-size z) ")"))) st))
        (ty-named (g ds)
          (let ((name (symbol->string (extract (k-gen-of g) 1))))
            (if (null? ds)
                (k-put name st)
                (k-put ")" (k-show-descs ds p (k-put (k-cat3 "(" name " ") st))))))
        ;; Each description's name, after it, names what it is.
        (ty-module (abs ds vs)
          (let* ((st (k-put (string-append "(moduleof" (k-show-abs abs)) st))
                 (st (k-show-comps "desc" ds p st)))
            (k-put ")" (k-show-comps "val" vs (k-printing-named p ds) st))))
        (ty-select (m n)
          (k-put (k-cat5 "(select " (symbol->string m) " " (symbol->string n) ")") st))
        (ty-param (k n)
          (k-put (k-cat5 "(select $" (int->string (+ k 1)) " " (symbol->string n) ")") st))
        (ty-app (g ds)
          (let ((st (k-put " " (k-show-on g p (k-put "(" st)))))
            (k-put ")" (k-show-descs ds p st))))
        (ty-lam (bs body)
          (let ((head (k-cat3 "(dlambda (" (k-join (k-show-binders bs) " ") ") ")))
            (k-put ")" (k-show-desc body p (k-put head st))))))))
  ;; A module type's components of kind `what`: ` (what name type)` each.
  ;; A description's name naming it in the components after it.
  (k-show-comps (subr kbuilds (string k-parts k-printing k-shown) k-shown)
    (lambda (what ps p st)
      (if (null? ps)
          st
          (let* ((one (k-cat5 " (" what " " (symbol->string (extract (car ps) 1)) " "))
                 (after (if (string=? what "desc") (k-printing-named p (list (car ps))) p))
                 (own (if (string=? what "desc") (extract (car ps) 1) '||))
                 (st (k-put ")" (k-show-comp (extract (car ps) 2) p own (k-put one st)))))
            (k-show-comps what (cdr ps) after st)))))
  ;; A component's type; an effect, a description function of no parameters,
  ;; as the effect. A description shows what it is, not its own name `n` (a
  ;; value's, `||`, no name): a `define-type` alias of it, `(select m n)`, is
  ;; named `n` too.
  ;; A family too (`(dlambda …)`), as the Rust checker shows one.
  (k-show-comp (subr kbuilds (int k-printing symbol k-shown) k-shown)
    (lambda (t p n st)
      (tagcase (k-get t)
        (ty-lam (bs body)
          (if (null? bs) (k-show-desc body p st) (k-show-comp-named t p n st)))
        (else y (k-show-comp-named t p n st)))))
  (k-show-comp-named (subr kbuilds (int k-printing symbol k-shown) k-shown)
    (lambda (t p n st)
      (let* ((r (k-resolve t))
             (named (k-part-named (extract p 2) r))
             (name (if (null? named) (k-abbrev-by (extract p 3) r) named)))
        (if (or (null? name) (string=? (car name) (symbol->string n)))
            (k-show-body r p st)
            (k-put (car name) st))))))

;; Each of `ts` shown, as printing `path` shows it.
(define k-show-list (subr kbuilds (k-ids k-printing) k-strings)
  (lambda (ts path)
    (if (null? ts)
        nil
        (cons (k-pieces-string (extract (k-show-on (car ts) path k-shown-none) 1))
              (k-show-list (cdr ts) path)))))
;; Whether type `t` is variable `v`.
(define k-type-is-var? (subr (maxeff kreads spin) (int int) bool)
  (lambda (t v) (tagcase (k-get t) (ty-var (w) (= w v)) (else y #f))))
;; The tree of a scope's `define-type`s (`k-atree-of`), kept with the scope
;; it was made of and how many links had been made (`k-links`): made once
;; for the top level, whose types are declared ahead, while what they
;; resolve to stays, not again for each line shown (`k-keep-atree!`).
(define-type k-atree-of-scope (productof (1 k-scope) (2 int) (3 k-atree)))
(define k-atree-kept (ref (listof k-atree-of-scope acyclic) @t) (new nil))
;; Whether `kept` is the tree of the scope now.
(define k-atree-current? (subr kreads ((listof k-atree-of-scope acyclic)) bool)
  (lambda (kept)
    (and (not (null? kept))
         (eq? (extract (car kept) 1) (get k-dscope))
         (= (extract (car kept) 2) (get k-links)))))
;; For the driver of the top level, which may write: the tree of the scope
;; now, if the one kept is not of it.
(define k-keep-atree! (subr (maxeff kreads (write @t) (alloc @t) spin) () unit)
  (lambda ()
    (if (k-atree-current? (get k-atree-kept))
        #u
        (let ((ds (get k-dscope)))
          (begin (set k-links-below (get k-ntys))
                 (set k-atree-kept
                      (list (product (1 ds) (2 (get k-links))
                                     (3 (k-atree-of ds 0 (a-leaf)))))))))))
;; The tree of the scope now: the one kept, if it is of it.
(define k-atree-now (subr kbuilds () k-atree)
  (lambda ()
    (let ((kept (get k-atree-kept)))
      (if (k-atree-current? kept)
          (extract (car kept) 3)
          (k-atree-of (get k-dscope) 0 (a-leaf))))))
;; A type. One `define-type` named prints as its name; any other recursive
;; type as `(mu %d …)`, `%d` naming the cycle.
(define k-show-ty (subr kbuilds (int) string)
  (lambda (t)
    (let* ((trs (the k-atrees (list (k-atree-now))))
           (p (product (1 (the k-ids nil)) (2 (the k-parts nil)) (3 trs))))
      (k-pieces-string (extract (k-show-on t p k-shown-none) 1)))))))

(define k-dvar-string (with check-print-module k-dvar-string))
(define k-region-show (with check-print-module k-region-show))
(define k-globals-atom? (with check-print-module k-globals-atom?))
(define k-show-effect (with check-print-module k-show-effect))
(define k-conv-default (with check-print-module k-conv-default))
(define check-conv-native! (with check-print-module check-conv-native!))
(define k-conv=? (with check-print-module k-conv=?))
(define k-kind-text (with check-print-module k-kind-text))
(define k-kind-word (with check-print-module k-kind-word))
(define k-place? (with check-print-module k-place?))
(define k-size-lit (with check-print-module k-size-lit))
(define k-size-as-lit (with check-print-module k-size-as-lit))
(define k-size-plus (with check-print-module k-size-plus))
(define k-size=? (with check-print-module k-size=?))
(define k-map-find (with check-print-module k-map-find))
(define k-size-var (with check-print-module k-size-var))
(define k-size-add-scaled (with check-print-module k-size-add-scaled))
(define k-coef-of (with check-print-module k-coef-of))
(define-type k-size-fact (select check-print-module k-size-fact))
(define k-size-facts (with check-print-module k-size-facts))
(define k-size-nonneg? (with check-print-module k-size-nonneg?))
(define k-size-eq? (with check-print-module k-size-eq?))
(define k-tail-size (with check-print-module k-tail-size))
(define k-size-le? (with check-print-module k-size-le?))
(define k-subst-size (with check-print-module k-subst-size))
(define k-show-size (with check-print-module k-show-size))
(define k-show-list (with check-print-module k-show-list))
(define k-type-is-var? (with check-print-module k-type-is-var?))
(define k-show-ty (with check-print-module k-show-ty))
(define k-keep-atree! (with check-print-module k-keep-atree!))
(define k-printing-none (with check-print-module k-printing-none))
