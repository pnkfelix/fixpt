;;; The checker, in FX-26: types and effects shown as the Rust checker shows
;;; them; and what a type holds: where a procedure kept in it could reach
;;; itself, and at which polarities a variable occurs in it.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ printing

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
  ;; A kind as it is written: `type`, or `(=> type type)`.
  (k-kind-text (subr (maxeff kreads (alloc @t) spin) (int) string)
    (lambda (k)
      (let ((a (k-arrow-parts k)))
        (if (null? a)
            (k-kind-name k)
            (k-cat5 "(=> " (k-join (k-kinds-text (car (car a))) " ") " " (k-kind-text (cdr (car a)))
                    ")")))))
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

;; The name `define-type` gave `t`, innermost first: each name's innermost
;; binding only.
(define k-abbrev-in (subr kbuilds (k-scope k-names int) k-strings)
  (lambda (ds seen t)
    (if (null? ds)
        nil
        (let ((n (car (car ds))))
          (tagcase (cdr (car ds))
            (ds-rec (d)
              (cond ((k-has-name? seen n) (k-abbrev-in (cdr ds) seen t))
                    ((= (k-resolve d) t) (cons (symbol->string n) nil))
                    (else (k-abbrev-in (cdr ds) (cons n seen) t))))
            (else y (k-abbrev-in (cdr ds) seen t)))))))
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
;; Whether `name` occurs in `s` as a symbol of its own.
(define k-mentions-token? (subr (maxeff (read @globals) spin) (string string) bool)
  (lambda (s name)
    (or (>= (k-find-sub s (k-cat3 " " name " ") 0) 0)
        (or (>= (k-find-sub s (k-cat3 " " name ")") 0) 0)
            (or (>= (k-find-sub s (k-cat3 "(" name " ") 0) 0)
                (>= (k-find-sub s (k-cat3 "(" name ")") 0) 0))))))
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

(define-rec
  (k-show-on (subr kbuilds (int k-ids) string)
    (lambda (t path)
      (let* ((t (k-resolve t)) (name (k-abbrev-in (get k-dscope) nil t)))
        (if (null? name) (k-show-body t path) (car name)))))
  (k-show-list (subr kbuilds (k-ids k-ids) k-strings)
    (lambda (ts path)
      (if (null? ts) nil (cons (k-show-on (car ts) path) (k-show-list (cdr ts) path)))))
  ;; ` (label type)`.
  (k-show-part (subr kbuilds ((productof (1 symbol) (2 int)) k-ids) string)
    (lambda (part path)
      (k-cat5 " (" (symbol->string (extract part 1)) " " (k-show-on (extract part 2) path) ")")))
  (k-show-parts (subr kbuilds (k-parts k-ids) string)
    (lambda (ps path)
      (if (null? ps) "" (string-append (k-show-part (car ps) path) (k-show-parts (cdr ps) path)))))
  (k-show-desc (subr kbuilds (k-desc k-ids) string)
    (lambda (d p)
      (tagcase d
        (dt (t) (k-show-on t p))
        (dr (r) (k-region-show r))
        (de (e) (k-show-effect e))
        (dz (z) (k-show-size z))
        (dc (c) (k-conv-show c))
        (df (f) (k-show-on f p)))))
  (k-show-descs (subr kbuilds (k-descs k-ids) k-strings)
    (lambda (ds p)
      (if (null? ds)
          nil
          (let ((x (k-show-desc (car ds) p)))
            (cons x (k-show-descs (cdr ds) p))))))
  ;; A `subr` type.
  (k-show-subr (subr kbuilds (k-eff k-ids int k-conv k-ids) string)
    (lambda (e ps r cv p)
      (let* ((conv (k-conv-prefix cv))
             (effect (k-show-effect e))
             (params (k-join (k-show-list ps p) " ")))
        (k-cat5 (k-cat4 "(subr " conv effect " (") params ") " (k-show-on r p) ")"))))
  ;; `(head a h e r)`: a prompt tag's type, or a composable continuation's.
  (k-show-control (subr kbuilds (string int int k-eff k-region k-ids) string)
    (lambda (head a h e r p)
      (k-cat5 (k-cat4 head (k-show-on a p) " " (k-show-on h p)) " " (k-show-effect e) " "
              (string-append (k-region-show r) ")"))))
  ;; A node met again on the way down is a cycle: named by its depth, and
  ;; written `(mu %d …)` where the cycle starts.
  (k-show-body (subr kbuilds (int k-ids) string)
    (lambda (t path)
      (if (k-has-id? path t)
          (string-append "%" (int->string (k-depth-of path t)))
          (let ((p (the k-ids (cons t path))))
            (k-mu-wrap (string-append "%" (int->string (k-length p))) (k-show-node t p))))))
  ;; What node `t` shows as, `p` the path to it from the root, newest
  ;; first.
  (k-show-node (subr kbuilds (int k-ids) string)
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
        (ty-module (abs ds vs)
          (k-cat5 "(moduleof" (k-show-abs abs) (k-show-comps "desc" ds p) (k-show-comps "val" vs p)
                  ")"))
        (ty-select (m n) (k-cat5 "(select " (symbol->string m) " " (symbol->string n) ")"))
        (ty-param (k n) (k-cat5 "(select $" (int->string (+ k 1)) " " (symbol->string n) ")"))
        (ty-app (g ds) (k-cat5 "(" (k-show-on g p) " " (k-join (k-show-descs ds p) " ") ")"))
        (ty-lam (bs body)
          (k-cat5 "(dlambda (" (k-join (k-show-binders bs) " ") ") " (k-show-desc body p) ")")))))
  ;; A module type's components of kind `what`: ` (what name type)` each.
  (k-show-comps (subr kbuilds (string k-parts k-ids) string)
    (lambda (what ps p)
      (if (null? ps)
          ""
          (let ((one (k-cat5 " (" what " " (symbol->string (extract (car ps) 1)) " ")))
            (k-cat4 one (k-show-on (extract (car ps) 2) p) ")" (k-show-comps what (cdr ps) p)))))))

;; Whether type `t` is variable `v`.
(define k-type-is-var? (subr (maxeff kreads spin) (int int) bool)
  (lambda (t v) (tagcase (k-get t) (ty-var (w) (= w v)) (else y #f))))
;; A type. One `define-type` named prints as its name; any other recursive
;; type as `(mu %d …)`, `%d` naming the cycle.
(define k-show-ty (subr kbuilds (int) string)
  (lambda (t) (k-show-on t nil)))

;;; ------------------------------------------------------------ what types hold

;; Regions storage is kept in, for `k-knot-in`.
(define-type k-kept (listof k-region acyclic))
;; The types in description `d`, for analyses that look through what a
;; value holds: a type itself, or a `dlambda`'s body's (its parameters
;; standing for what it is given).
(define k-d-types (subr (maxeff kreads spin) (k-desc) k-ids)
  (lambda (d)
    (tagcase d
      (dt (t) (the k-ids (cons t nil)))
      (df (f) (tagcase (k-get f) (ty-lam (bs body) (k-d-types body)) (else y nil)))
      (else y nil))))
;; `xs` before `ys`.
(define k-ids-onto (subr (maxeff (read @globals) (alloc @t)) (k-ids k-ids) k-ids)
  (lambda (xs ys) (if (null? xs) ys (the k-ids (cons (car xs) (k-ids-onto (cdr xs) ys))))))
;; The types in descriptions `ds`, each as `k-d-types` finds them.
(define k-ds-types (subr (maxeff kreads (alloc @t) spin) (k-descs) k-ids)
  (lambda (ds) (if (null? ds) nil (k-ids-onto (k-d-types (car ds)) (k-ds-types (cdr ds))))))
(define k-kept-has? (subr (maxeff kreads spin) (k-kept k-region) bool)
  (lambda (rs r) (and (not (null? rs)) (or (k-region=? (car rs) r) (k-kept-has? (cdr rs) r)))))
(define k-kept-add (subr kbuilds (k-kept k-region) k-kept)
  (lambda (rs r) (if (k-kept-has? rs r) rs (cons r rs))))
;; Whether `r` is the region of frozen data.
(define k-frozen? (subr pure (k-region) bool)
  (lambda (r) (tagcase r (r-frozen (q f) #t) (else y #f))))
;; The regions of everything in `t` that can be written: storage a
;; generative type's representation may keep what it was given in.
(define-rec
  (k-storage-walk (subr (maxeff kstate spin) (int int (ref k-kept @t)) unit)
    (lambda (t seen out)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #u
            (letrec ((add (subr (maxeff kstate spin) (k-region) unit)
                          (lambda (r) (set out (k-kept-add (get out) r))))
                     (walk (subr (maxeff kstate spin) (int) unit)
                           (lambda (x) (k-storage-walk x seen out)))
                     (walks (subr (maxeff kstate spin) (k-ids) unit)
                            (lambda (xs) (k-storage-walks xs seen out))))
              (tagcase (k-get t)
                (ty-ref (a r) (begin (add r) (walk a)))
                (ty-array (a r) (begin (add r) (walk a)))
                (ty-icell (a r) (begin (add r) (walk a)))
                (ty-markkey (a r) (begin (add r) (walk a)))
                (ty-pair (a b r) (begin (if (k-frozen? r) #u (add r)) (walk a) (walk b)))
                (ty-bloblet (fs z r) (begin (if z #u (add r)) (walks fs)))
                (ty-subr (e ps r cv) (begin (walks ps) (walk r)))
                (ty-poly (bs body) (walk body))
                (ty-product (ps) (k-storage-parts ps seen out))
                (ty-sum (ps) (k-storage-parts ps seen out))
                (ty-tag (a h e r) (begin (walk a) (walk h)))
                (ty-comp (b a e r) (begin (walk b) (walk a)))
                (ty-named (g ds) (begin (walk (extract (k-gen-of g) 4)) (walks (k-desc-types ds))))
                (ty-nlist (e z r) (walk e))
                (ty-app (f ds) (walks (k-ds-types ds)))
                (else x #u)))))))
  (k-storage-walks (subr (maxeff kstate spin) (k-ids int (ref k-kept @t)) unit)
    (lambda (ts seen out)
      (if (null? ts)
          #u
          (begin (k-storage-walk (car ts) seen out) (k-storage-walks (cdr ts) seen out)))))
  (k-storage-parts (subr (maxeff kstate spin) (k-parts int (ref k-kept @t)) unit)
    (lambda (ps seen out)
      (if (null? ps)
          #u
          (begin (k-storage-walk (extract (car ps) 2) seen out)
                 (k-storage-parts (cdr ps) seen out))))))
(define k-storage-regions (subr (maxeff kstate spin) (int) k-kept)
  (lambda (t)
    (let ((out (the (ref k-kept @t) (new nil))))
      (begin (k-storage-walk t (k-new-epoch) out) (get out)))))
;; `kept`, and each of `rs` that is not a generative type's parameter nor
;; frozen.
(define k-kept-extend (subr kbuilds (k-kept k-regions) k-kept)
  (lambda (kept rs)
    (cond ((null? rs) kept)
          ((or (k-gen-region? (car rs)) (k-frozen? (car rs))) (k-kept-extend kept (cdr rs)))
          (else (k-kept-extend (k-kept-add kept (car rs)) (cdr rs))))))
(define k-append-regions (subr (maxeff (read @globals) (alloc @t)) (k-regions k-regions) k-regions)
  (lambda (xs ys)
    (if (null? xs) ys (the k-regions (cons (car xs) (k-append-regions (cdr xs) ys))))))
;; Whether `a` reads or awaits a region `kept` has.
;; `@globals` among the regions kept stands for every region (no procedure
;; is kept in globals' bindings).
(define k-reads-in? (subr (maxeff kreads spin) (k-kept k-atom) bool)
  (lambda (kept a)
    (letrec ((in? (subr (maxeff kreads spin) (k-region) bool)
                  (lambda (r)
                    (or (k-kept-has? kept r)
                        (and (k-kept-has? kept (r-globals)) (not (k-frozen? r))
                             (not (k-globals-region? r)))))))
      (tagcase a (a-read (r) (in? r)) (a-await (r) (in? r)) (else y #f)))))
;; The region of the first of `xs` that reads or awaits one `kept` has,
;; alone in a list; none if none does.
(define k-first-read-in (subr kbuilds (k-kept k-eff) k-regions)
  (lambda (kept xs)
    (cond ((null? xs) (the k-regions nil))
          ((k-reads-in? kept (car xs)) (the k-regions (cons (k-atom-region (car xs)) nil)))
          (else (k-first-read-in kept (cdr xs))))))
;; Whether `t` keeps, in storage at some region `r`, a procedure whose
;; latent effect reads or awaits `r` and does not say `spin`: a knot tied
;; through the store, a loop with no recursive call, which only its type can
;; show. The region and the procedure's type, if so.
(define k-reads-kept (subr kbuilds (k-eff k-kept) k-regions)
  (lambda (e kept)
    (if (k-contains? e (a-spin)) (the k-regions nil) (k-first-read-in kept e))))
(define k-kept-same? (subr (maxeff kreads spin) (k-kept k-kept) bool)
  (lambda (x y)
    (letrec ((within (subr (maxeff kreads spin) (k-kept k-kept) bool)
               (lambda (a b) (or (null? a) (and (k-kept-has? b (car a)) (within (cdr a) b))))))
      (and (within x y) (within y x)))))
(define-type k-knot (listof (pairof k-region int @t) acyclic))
;; The types a search for a knot has met, each with what it found kept.
(define-type k-kept-seen (listof (pairof int k-kept @t) acyclic))
(define-type k-kseen (ref k-kept-seen @t))
(define k-kseen-has? (subr (maxeff kreads spin) (k-kept-seen int k-kept) bool)
  (lambda (xs t kept)
    (and (not (null? xs))
         (or (and (= (car (car xs)) t) (k-kept-same? (cdr (car xs)) kept))
             (k-kseen-has? (cdr xs) t kept)))))
(define-rec
  (k-knot-in (subr (maxeff kstate spin) (int k-kept k-kseen) k-knot)
    (lambda (t kept seen)
      (let ((t (k-resolve t)))
        (if (k-kseen-has? (get seen) t kept)
            (the k-knot nil)
            (begin
              (set seen (cons (cons t kept) (get seen)))
              (tagcase (k-get t)
                (ty-ref (a r) (k-knot-in a (k-kept-add kept r) seen))
                (ty-array (a r) (k-knot-in a (k-kept-add kept r) seen))
                (ty-icell (a r) (k-knot-in a (k-kept-add kept r) seen))
                (ty-markkey (a r) (k-knot-in a (k-kept-add kept r) seen))
                (ty-pair (a b r)
                  (let ((k (if (k-frozen? r) kept (k-kept-add kept r))))
                    (k-knot-then (k-knot-in a k seen) b k seen)))
                (ty-bloblet (fs z r) (k-knot-list fs (if z kept (k-kept-add kept r)) seen))
                (ty-product (ps) (k-knot-parts ps kept seen))
                (ty-sum (ps) (k-knot-parts ps kept seen))
                (ty-poly (bs body) (k-knot-in body kept seen))
                ;; A procedure: kept where it is, it may not read there
                ;; unsaid; what it takes and gives is kept nowhere yet.
                (ty-subr (e ps r cv)
                  (let ((found (k-reads-kept e kept)))
                    (if (null? found)
                        (k-knot-then (k-knot-list ps nil seen) r nil seen)
                        (the k-knot (cons (cons (car found) t) nil)))))
                (ty-comp (x a e r)
                  (let ((found (k-reads-kept e kept)))
                    (if (null? found)
                        (k-knot-then (k-knot-in x nil seen) a nil seen)
                        (the k-knot (cons (cons (car found) t) nil)))))
                (ty-tag (a h e r) (k-knot-then (k-knot-in a nil seen) h nil seen))
                (ty-nlist (e z r) (k-knot-in e kept seen))
                ;; Transparent to safety: its representation, and what it
                ;; was given, kept, cautiously, wherever its representation
                ;; keeps anything and in every region it was given.
                (ty-named (g ds)
                  (let* ((rep (extract (k-gen-of g) 4))
                         (held (k-storage-regions rep))
                         (k (k-kept-extend kept (k-append-regions held (k-desc-regions ds))))
                         (x (k-knot-in rep kept seen)))
                    (if (null? x) (k-knot-list (k-desc-types ds) k seen) x)))
                ;; A module's abstract type constructor applied: its
                ;; representation, unseen, may keep what it was given
                ;; anywhere. A `poly`'s variable applied is checked as it is
                ;; instantiated.
                (ty-app (f ds)
                  (let ((anywhere (tagcase (k-get f)
                                    (ty-var (v) (k-has-id? (get k-abstract-funs) v))
                                    (else z #f))))
                    (k-knot-list (k-ds-types ds) (if anywhere (k-kept-add kept (r-globals)) kept)
                                 seen)))
                (else y (the k-knot nil))))))))
  ;; `x`, or, if that is none, the knot in `t`.
  (k-knot-then (subr (maxeff kstate spin) (k-knot int k-kept k-kseen) k-knot)
    (lambda (x t kept seen) (if (null? x) (k-knot-in t kept seen) x)))
  (k-knot-list (subr (maxeff kstate spin) (k-ids k-kept k-kseen) k-knot)
    (lambda (ts kept seen)
      (if (null? ts)
          (the k-knot nil)
          (let ((x (k-knot-in (car ts) kept seen)))
            (if (null? x) (k-knot-list (cdr ts) kept seen) x)))))
  (k-knot-parts (subr (maxeff kstate spin) (k-parts k-kept k-kseen) k-knot)
    (lambda (ps kept seen)
      (if (null? ps)
          (the k-knot nil)
          (let ((x (k-knot-in (extract (car ps) 2) kept seen)))
            (if (null? x) (k-knot-parts (cdr ps) kept seen) x))))))
;; What a procedure kept in region `r` that reads it there says, `t` its
;; type.
(define k-knot-message (subr (read @globals) (string string) string)
  (lambda (r t)
    (k-cat5 "a procedure kept in `" r "` reads `" r
            (string-append "`, so it could reach itself: it must say `spin`, and it is a " t))))
(define k-no-knot (subr (maxeff checks spin) (int int int) unit)
  (lambda (t a b)
    (let ((found (k-knot-in t nil (the k-kseen (new nil)))))
      (if (null? found)
          #u
          (let ((r (k-region-show (car (car found)))))
            (k-fail (k-knot-message r (k-show-ty (cdr (car found)))) a b))))))

;; Each polarity (0 covariant, 1 contravariant, 2 invariant) at which `v`
;; occurs in `t`, reached at polarity `at`.
(define k-flip (subr pure (int) int) (lambda (p) (cond ((= p 0) 1) ((= p 1) 0) (else 2))))
(define k-reg-is? (subr pure (k-region int) bool)
  (lambda (r v) (tagcase r (r-var (x) (= x v)) (r-frozen (x f) (= x v)) (else y #f))))
(define k-eff-var? (subr kreads (k-eff int) bool)
  (lambda (e v) (and (not (null? e)) (or (= (k-atom-var (car e)) v) (k-eff-var? (cdr e) v)))))
(define k-eff-region-var? (subr kreads (k-eff int) bool)
  (lambda (e v)
    (and (not (null? e))
         (or (and (k-has-region? (car e)) (k-reg-is? (k-atom-region (car e)) v))
             (k-eff-region-var? (cdr e) v)))))
(define k-eff-regions-of (subr (read @globals) (k-eff) k-regions)
  (lambda (e)
    (cond ((null? e) nil)
          ((k-has-region? (car e)) (cons (k-atom-region (car e)) (k-eff-regions-of (cdr e))))
          (else (k-eff-regions-of (cdr e))))))
;; The regions a description names outright: a region, an effect's atoms',
;; and a `dlambda`'s body's.
(define k-d-regions (subr (maxeff kreads spin) (k-desc) k-regions)
  (lambda (d)
    (tagcase d
      (dr (r) (the k-regions (cons r nil)))
      (de (e) (k-eff-regions-of e))
      (df (f) (tagcase (k-get f) (ty-lam (bs body) (k-d-regions body)) (else y nil)))
      (else y nil))))
;; The effects a description is or names: an effect, or a `dlambda`'s
;; body's.
(define k-d-effects (subr (maxeff kreads spin) (k-desc) (listof k-eff acyclic))
  (lambda (d)
    (tagcase d
      (de (e) (the (listof k-eff acyclic) (cons e nil)))
      (df (f) (tagcase (k-get f) (ty-lam (bs body) (k-d-effects body)) (else y nil)))
      (else y nil))))
(define k-terms-name? (subr (read @globals) (k-terms int) bool)
  (lambda (ts v) (and (not (null? ts)) (or (= (car (car ts)) v) (k-terms-name? (cdr ts) v)))))
;; Whether an effect application in `e` names variable `v`.
(define-rec
  (k-eff-app-var? (subr (maxeff kreads spin) (k-eff int) bool)
    (lambda (e v)
      (and (not (null? e))
           (or (tagcase (car e) (a-app (h ds) (k-app-mentions? h ds v)) (else y #f))
               (k-eff-app-var? (cdr e) v)))))
  (k-app-mentions? (subr (maxeff kreads spin) (int k-descs int) bool)
    (lambda (h ds v) (or (= h v) (k-eargs-mention? ds v))))
  (k-eargs-mention? (subr (maxeff kreads spin) (k-descs int) bool)
    (lambda (ds v)
      (and (not (null? ds))
           (or (tagcase (car ds)
                 (dr (r) (k-reg-is? r v))
                 (de (e) (or (k-eff-var? e v) (k-eff-region-var? e v) (k-eff-app-var? e v)))
                 (dz (z) (tagcase z (sz-lin (k ts) (k-terms-name? ts v)) (else y #f)))
                 (dc (c) (tagcase c (cv-var (w) (= w v)) (else y #f)))
                 (else y #f))
               (k-eargs-mention? (cdr ds) v))))))
(define k-regions-name? (subr (read @globals) (k-regions int) bool)
  (lambda (rs v) (and (not (null? rs)) (or (k-reg-is? (car rs) v) (k-regions-name? (cdr rs) v)))))
(define k-effs-name? (subr kreads ((listof k-eff acyclic) int) bool)
  (lambda (es v) (and (not (null? es)) (or (k-eff-var? (car es) v) (k-effs-name? (cdr es) v)))))
(define-rec
  ;; The kind of description function `f`, where it is known: -1 for a
  ;; `select` not yet resolved.
  (k-fun-kind (subr (maxeff kstate spin) (int) int)
    (lambda (f)
      (tagcase (k-get f)
        (ty-var (v) (k-dvar-kind v))
        (ty-lam (bs body)
          (let ((r (k-d-kind body))) (if (< r 0) -1 (k-arrow (k-binder-kinds bs) r))))
        ;; A function that gives a function, applied.
        (ty-app (g ds) (k-arrow-result (k-fun-kind g)))
        (else x -1))))
  ;; The kind a description is of, where it is known.
  (k-d-kind (subr (maxeff kstate spin) (k-desc) int)
    (lambda (d)
      (tagcase d
        (dr (r) (if (k-place? r) 3 0))
        (de (e) 1)
        (dt (t) 2)
        (dz (z) 5)
        (dc (c) 6)
        (df (f) (k-fun-kind f))))))
