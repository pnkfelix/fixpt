;;; The checker, in FX-26: types and effects shown as the Rust checker shows
;;; them; and what a type holds: where a procedure kept in it could reach
;;; itself, and at which polarities a variable occurs in it.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ printing

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-print-module (module
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
;; The names of the globals `e` reads (`op` 0) or writes (1), in order, each
;; after a space.
(define k-globals-shown (subr kreads (k-eff int) string)
  (lambda (e op)
    (if (null? e)
        ""
        (let ((g (tagcase (car e)
                   (a-read (r) (if (= op 0) (k-global-shown r) ""))
                   (a-write (r) (if (= op 1) (k-global-shown r) ""))
                   (else y ""))))
          (string-append g (k-globals-shown (cdr e) op))))))
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
    (cond ((= k 0) "region")
          ((= k 1) "effect")
          ((= k 3) "place")
          ((= k 4) "data")
          ((= k 5) "size")
          ((= k 6) "conv")
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
    (cond ((= k 0) "Region")
          ((= k 1) "Effect")
          ((= k 3) "Place")
          ((= k 4) "Data")
          ((= k 5) "Size")
          ((= k 6) "Conv")
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
;; Whether the character at `i` of `s` is one of `cs`; none past either end.
(define k-char-at-in? (subr (maxeff (read @globals) spin) (string int string) bool)
  (lambda (s i cs)
    (and (>= i 0) (< i (string-length s))
         (>= (k-find-sub cs (substring s i (+ i 1)) 0) 0))))
;; Whether `name` occurs in `s` as a symbol of its own: after a space or
;; `(`, and before a space or `)`. One pass, nothing made but the
;; characters looked at (it is asked of every node of a type printed).
(define k-mentions-token? (subr (maxeff (read @globals) spin) (string string) bool)
  (lambda (s name)
    (letrec ((from (subr (maxeff (read @globals) spin) (int) bool)
                     (lambda (at)
                       (let ((i (k-find-sub s name at)))
                         (cond ((< i 0) #f)
                               ((and (k-char-at-in? s (- i 1) " (")
                                     (k-char-at-in? s (+ i (string-length name)) " )"))
                                #t)
                               (else (from (+ i 1))))))))
      (from 0))))
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
;; What the branches being checked have learned about sizes: `lin = 0`
;; (`#t`) or `lin ≥ 0`, newest first.
(define-type k-size-fact (productof (1 k-size) (2 bool)))
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
;; Fourier–Motzkin, as the Rust checker's `refuted_below` (`src/sizes.rs`),
;; step for step: whether the inequalities in scope, with every size a
;; natural, leave no room for `a ≤ -1`.
(define-type k-lins (listof k-size acyclic))
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
;; `out`, the type a node shows as, as `(mu name out)` if it mentions itself.
(define k-mu-wrap (subr (maxeff (read @globals) spin) (string string) string)
  (lambda (name out) (if (k-mentions-token? out name) (k-cat5 "(mu " name " " out ")") out)))

;; `s`, then region `r`, closing the form `s` opens.
(define k-with-region (subr kreads (string k-region) string)
  (lambda (s r) (k-cat4 s " " (k-region-show r) ")")))
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

;; Where a type is being shown: the path to it from the root, newest first,
;; to name cycles by; and the names a `moduleof`'s descriptions give what
;; they describe, in the components after them, newest first.
(define-type k-printing (productof (1 k-ids) (2 k-parts)))
(define k-printing-none k-printing (product (1 (the k-ids nil)) (2 (the k-parts nil))))
;; `p` with the names of descriptions `ds` too.
(define k-printing-named (subr (maxeff (read @globals) (alloc @t)) (k-printing k-parts)
                                k-printing)
  (lambda (p ds)
    (product (1 (extract p 1)) (2 (k-parts-onto-front ds (extract p 2))))))
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

(define-rec
  (k-show-on (subr kbuilds (int k-printing) string)
    (lambda (t path)
      (let* ((t (k-resolve t))
             (named (k-part-named (extract path 2) t))
             (name (if (null? named) (k-abbrev-in (get k-dscope) (get k-dscope) 0 t) named)))
        (if (null? name) (k-show-body t path) (car name)))))
  (k-show-list (subr kbuilds (k-ids k-printing) k-strings)
    (lambda (ts path)
      (if (null? ts) nil (cons (k-show-on (car ts) path) (k-show-list (cdr ts) path)))))
  ;; ` (label type)`.
  (k-show-part (subr kbuilds ((productof (1 symbol) (2 int)) k-printing) string)
    (lambda (part path)
      (k-cat5 " (" (symbol->string (extract part 1)) " " (k-show-on (extract part 2) path) ")")))
  (k-show-parts (subr kbuilds (k-parts k-printing) string)
    (lambda (ps path)
      (if (null? ps) "" (string-append (k-show-part (car ps) path) (k-show-parts (cdr ps) path)))))
  (k-show-desc (subr kbuilds (k-desc k-printing) string)
    (lambda (d p)
      (tagcase d
        (dt (t) (k-show-on t p))
        (dr (r) (k-region-show r))
        (de (e) (k-show-effect e))
        (dz (z) (k-show-size z))
        (dc (c) (k-conv-show c))
        (df (f) (k-show-on f p)))))
  (k-show-descs (subr kbuilds (k-descs k-printing) k-strings)
    (lambda (ds p)
      (if (null? ds)
          nil
          (let ((x (k-show-desc (car ds) p)))
            (cons x (k-show-descs (cdr ds) p))))))
  ;; A `subr` type.
  (k-show-subr (subr kbuilds (k-eff k-ids int k-conv k-printing) string)
    (lambda (e ps r cv p)
      (let* ((conv (k-conv-prefix cv))
             (effect (k-show-effect e))
             (params (k-join (k-show-list ps p) " ")))
        (k-cat5 (k-cat4 "(subr " conv effect " (") params ") " (k-show-on r p) ")"))))
  ;; `(head a h e r)`: a prompt tag's type, or a composable continuation's.
  (k-show-control (subr kbuilds (string int int k-eff k-region k-printing) string)
    (lambda (head a h e r p)
      (k-cat5 (k-cat4 head (k-show-on a p) " " (k-show-on h p)) " " (k-show-effect e) " "
              (string-append (k-region-show r) ")"))))
  ;; A node met again on the way down is a cycle: named by its depth, and
  ;; written `(mu %d …)` where the cycle starts.
  (k-show-body (subr kbuilds (int k-printing) string)
    (lambda (t path)
      (let ((ids (extract path 1)))
        (if (k-has-id? ids t)
            (string-append "%" (int->string (k-depth-of ids t)))
            (let ((p (product (1 (the k-ids (cons t ids))) (2 (extract path 2)))))
              (k-mu-wrap (string-append "%" (int->string (k-length (extract p 1))))
                         (k-show-node t p)))))))
  ;; What node `t` shows as, `p` the path to it from the root, newest
  ;; first.
  (k-show-node (subr kbuilds (int k-printing) string)
    (lambda (t p)
      (tagcase (k-get t)
        (ty-base (s) (symbol->string s))
        (ty-void () "void")
        (ty-var (v) (k-dvar-string v))
        (ty-link (x) "?")
        (ty-subr (e ps r cv) (k-show-subr e ps r cv p))
        (ty-poly (bs body)
          (let ((binders (k-join (k-show-binders bs) " ")))
            (k-cat5 "(poly (" binders ") " (k-show-on body p) ")")))
        (ty-ref (a r) (k-cat5 "(ref " (k-show-on a p) " " (k-region-show r) ")"))
        (ty-product (ps) (k-cat3 "(productof" (k-show-parts ps p) ")"))
        (ty-sum (ps) (k-cat3 "(sumof" (k-show-parts ps p) ")"))
        (ty-array (a r) (k-cat5 "(arrayof " (k-show-on a p) " " (k-region-show r) ")"))
        (ty-icell (a r) (k-cat5 "(icell " (k-show-on a p) " " (k-region-show r) ")"))
        (ty-place (r) (k-cat3 "(place " (k-region-show r) ")"))
        (ty-pair (a b r)
          (if (= (k-resolve b) t)
              (k-cat5 "(listof " (k-show-on a p) " " (k-region-show r) ")")
              (k-with-region (k-cat4 "(pairof " (k-show-on a p) " " (k-show-on b p)) r)))
        (ty-tag (a h e r) (k-show-control "(prompt-tag " a h e r p))
        (ty-comp (a h e r) (k-show-control "(composable " a h e r p))
        (ty-markkey (a r) (k-cat5 "(mark-key " (k-show-on a p) " " (k-region-show r) ")"))
        (ty-bloblet (fs z r)
          (let ((head (if z "(bloblet (frozen" "(bloblet (fields")) (sep (if (null? fs) "" " ")))
            (k-with-region (k-cat4 head sep (k-join (k-show-list fs p) " ") ")") r)))
        (ty-nlist (e z r)
          (k-cat5 "(nlist " (k-show-on e p) " " (k-show-size z) (k-nlist-end r)))
        (ty-nat (z)
          (tagcase z (sz-finite () "nat") (else y (k-cat3 "(nat " (k-show-size z) ")"))))
        (ty-named (g ds)
          (let ((name (symbol->string (extract (k-gen-of g) 1))))
            (if (null? ds) name (k-cat5 "(" name " " (k-join (k-show-descs ds p) " ") ")"))))
        ;; Each description's name, after it, names what it is.
        (ty-module (abs ds vs)
          (k-cat5 "(moduleof" (k-show-abs abs) (k-show-comps "desc" ds p)
                  (k-show-comps "val" vs (k-printing-named p ds)) ")"))
        (ty-select (m n) (k-cat5 "(select " (symbol->string m) " " (symbol->string n) ")"))
        (ty-param (k n) (k-cat5 "(select $" (int->string (+ k 1)) " " (symbol->string n) ")"))
        (ty-app (g ds) (k-cat5 "(" (k-show-on g p) " " (k-join (k-show-descs ds p) " ") ")"))
        (ty-lam (bs body)
          (k-cat5 "(dlambda (" (k-join (k-show-binders bs) " ") ") " (k-show-desc body p) ")")))))
  ;; A module type's components of kind `what`: ` (what name type)` each.
  ;; A description's name naming it in the components after it.
  (k-show-comps (subr kbuilds (string k-parts k-printing) string)
    (lambda (what ps p)
      (if (null? ps)
          ""
          (let* ((one (k-cat5 " (" what " " (symbol->string (extract (car ps) 1)) " "))
                 (after (if (string=? what "desc") (k-printing-named p (list (car ps))) p))
                 (own (if (string=? what "desc") (extract (car ps) 1) '||)))
            (k-cat4 one (k-show-comp (extract (car ps) 2) p own) ")"
                    (k-show-comps what (cdr ps) after))))))
  ;; A component's type; an effect, a description function of no parameters,
  ;; as the effect. A description shows what it is, not its own name `n` (a
  ;; value's, `||`, no name): a `define-type` alias of it, `(select m n)`, is
  ;; named `n` too.
  (k-show-comp (subr kbuilds (int k-printing symbol) string)
    (lambda (t p n)
      (tagcase (k-get t)
        (ty-lam (bs body) (if (null? bs) (k-show-desc body p) (k-show-on t p)))
        (else y
          (let* ((r (k-resolve t))
                 (named (k-part-named (extract p 2) r))
                 (name (if (null? named) (k-abbrev-in (get k-dscope) (get k-dscope) 0 r) named)))
            (if (or (null? name) (string=? (car name) (symbol->string n)))
                (k-show-body r p)
                (car name))))))))

;; Whether type `t` is variable `v`.
(define k-type-is-var? (subr (maxeff kreads spin) (int int) bool)
  (lambda (t v) (tagcase (k-get t) (ty-var (w) (= w v)) (else y #f))))
;; A type. One `define-type` named prints as its name; any other recursive
;; type as `(mu %d …)`, `%d` naming the cycle.
(define k-show-ty (subr kbuilds (int) string)
  (lambda (t) (k-show-on t k-printing-none)))))

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
(define k-printing-none (with check-print-module k-printing-none))
