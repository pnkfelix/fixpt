;;; The compiler from FX-26 to cellular words, in FX-26: what the checker
;;; found of the program being compiled, by expression, in tables: each
;;; datum's layout, each conversion, reshaping, `with`, `stage`, call's
;;; convention and effect summary (`checked-extracts`). Apart from
;;; `compile.fx` since 2026-10-31 (`TODO.md` §188): `compile.fx` makes it, of
;;; the modules it is given, and gives on what it defines.


;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((compile-types (load-module "fx26:compile-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (table-types (load-module "fx26:table-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((layout (select layout-types layout-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (check-env (select check-env-types check-env-sig))
           (tables (select table-types tables-sig))
           ;; The parser's module, for where loaded files' places begin.
           (parser (moduleof (val load-base int))))
    (module
(hide (include compile-types) (include parser-types) (include check-env-types)
      (include check-types-types))
;; The types it uses of the files before it.
(define-type table (select table-types table))
;; What it uses of the modules it is given.
(define load-base (with parser load-base))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include layout) (include check-resolve) (include check-env) (include tables))

;; The checker's facts for the program being compiled.
(define c-facts (ref k-facts @k) (new nil))

;; The same, by expression (`k-at`, an expression's identity): each
;; `extract`'s field. A table, so that a program's facts are not searched
;; from the start for each `extract` compiled.
(define c-int-hash (subr pure (int) int) (lambda (a) a))

(define c-int=? (subr pure (int int) bool) (lambda (a b) (= a b)))

;; How the trees being compiled were numbered (`parser-ids.fx`): for the
;; facts numbered by their place in the walk, reading -1, as the checker
;; written in Rust's are (`rust_facts.rs`), which checks before the text is
;; parsed; mode -1 if there are none (the checker written in FX-26's have
;; the trees' own keys). And the keys the walk gave, by place.
(define c-numbering (ref numbering @k) (new (product (1 -1) (2 0) (3 nil))))
(define c-given (ref (table int (productof (1 int) (2 int)) @k) @k)
  (new (make-table c-int-hash c-int=?)))
(define c-set-numbering! (->* (numbering) unit)
  (lambda (w)
    (letrec ((index (subr (maxeff (alloc @k) (read @globals) spin (read @k) (write @k))
                          ((listof (productof (1 int) (2 int)) acyclic) int) unit)
               (lambda (gs i)
                 (if (null? gs)
                     #u
                     (begin (table-set! (get c-given) i (car gs)) (index (cdr gs) (+ i 1)))))))
      (begin (set c-numbering w)
             (set c-given (make-table c-int-hash c-int=?))
             (index (extract w 3) 0)))))
;; `at`, its key the walk's if it is numbered by its place in the walk: in
;; `path`, that place past those the session walked before; else the key
;; given there.
(define c-absolute-at (->* (k-at) k-at)
  (lambda (at)
    (if (= (extract at 4) -1)
        (let ((a (extract at 1)) (b (extract at 2)) (k (extract at 3)) (w (get c-numbering)))
          (if (= (extract w 1) 0)
              (product (1 a) (2 b) (3 (+ (extract w 2) k)) (4 0))
              (let ((g (table-ref (get c-given) k (product (1 -1) (2 -1)))))
                (product (1 a) (2 b) (3 (extract g 1)) (4 (extract g 2))))))
        at)))

;; `validate` (`docs/research/loads-and-places.md`, "Decided: three keys"):
;; each full key's facts, by a digest of them, as long as the compiler lasts
;; (its front end's), so that a key given again, in this text or another,
;; is found with the same facts, or said not to be (`c-validate-facts!`):
;; the key would leave out something checking reads.
(define c-readings ((proj (load-module "fx26:readings.fx") @s @e @m @c)))
(define c-fold (->* (int int) int)
  (lambda (h x) ((with c-readings fold1) h (bitwise-and x 1099511627775))))
(define-type c-key-digests (listof (productof (1 int) (2 int) (3 int)) acyclic))
(define c-facts-seen (ref (table int c-key-digests @k) @k) (new (make-table c-int-hash c-int=?)))
;; A fact's digest, by its kind's mark, then its parts. A convention's
;; variable is a variable, its number aside: a fresh one, which another
;; check of the same would number otherwise.
(define c-noted-digest (->* (k-noted) int)
  (lambda (n)
    (let ((f c-fold))
      (tagcase n
        (n-datum (d)
          (tagcase d
            (datum-field (i) (f (f 1 10) i)) (datum-blobref-field (i) (f (f 1 11) i))
            (datum-layout (i) (f (f 1 12) i)) (datum-array (m s) (f (f (f 1 13) m) s))
            (datum-fits (i) (f (f 1 14) i))))
        (n-summary (s) (f 2 s))
        (n-conversion (c) (f 3 c))
        (n-apply-shares () 4) (n-frozen-define () 5) (n-plain-fx () 6)
        (n-call (cv)
          (f 7 (tagcase cv (cv-cellular () 0) (cv-native () 1) (cv-fx () 2) (cv-var (v) 3))))
        (n-staged (fresh names rep d)
          ((with c-readings fold-text) ((with c-readings fold-text) (f 8 d) fresh) names))))))
;; One handoff's keys, each its facts' digests summed, as they come in no
;; order: by `k`, and the keys in the order first met.
(define-type c-key-acc (productof (1 (table int c-key-digests @k)) (2 (ref c-key-digests @k))))
(define c-key-add! (->* (c-key-acc k-at int) unit)
  (lambda (acc at d)
    (let* ((k (extract at 3)) (kr (extract at 4)) (tab (extract acc 1))
           (ks (table-ref tab k nil)))
      (letrec ((add (subr (maxeff (alloc @k) (read @globals) spin) (c-key-digests) c-key-digests)
                 (lambda (ks)
                   (cond ((null? ks) nil)
                         ((and (= (extract (car ks) 1) k) (= (extract (car ks) 2) kr))
                          (cons (product (1 k) (2 kr)
                                         (3 (bitwise-and (+ (extract (car ks) 3) d) 1099511627775)))
                                (cdr ks)))
                         (else (cons (car ks) (add (cdr ks))))))))
        (if (null? (c-key-digest-in ks k kr))
            (begin
              (table-set! tab k (the c-key-digests (cons (product (1 k) (2 kr) (3 d)) ks)))
              (set (extract acc 2)
                   (the c-key-digests (cons (product (1 k) (2 kr) (3 0)) (get (extract acc 2))))))
            (table-set! tab k (add ks)))))))
;; A `with`'s and a reshape's, of the names, positions and picks noted.
(define c-names-digest (->* (int (listof symbol acyclic)) int)
  (lambda (h ns)
    (if (null? ns)
        h
        (c-names-digest ((with c-readings fold-run) h 6 (symbol->string (car ns))) (cdr ns)))))
(define c-ints-digest (->* (int (listof int acyclic)) int)
  (lambda (h is) (if (null? is) h (c-ints-digest (c-fold h (car is)) (cdr is)))))
(define c-picks-digest (->* (int k-picks) int)
  (lambda (h ps)
    (if (null? ps)
        h
        (c-picks-digest (tagcase (car ps)
                          (pick-value (k) (c-fold (c-fold h 1) k))
                          (pick-path (k j) (c-fold (c-fold (c-fold h 2) k) j)))
                        (cdr ps)))))
;; The facts `fs`, `with`s `ws` and reshapes `rs` of one handoff (their keys
;; the walk's: `c-absolute-at`), each key's digest checked against what it
;; had before, and kept: "", or why not, the first key whose facts differ.
(define c-validate-facts! (->* (k-facts k-with-list k-reshape-list) string)
  (lambda (fs ws rs)
    (let ((acc (product (1 (the (table int c-key-digests @k) (make-table c-int-hash c-int=?)))
                        (2 (the (ref c-key-digests @k) (new nil))))))
      (letrec ((facts (subr (maxeff (alloc @k) (read @globals) spin (read @k) (write @k))
                            (k-facts) unit)
                 (lambda (fs)
                   (if (null? fs)
                       #u
                       (begin (c-key-add! acc (c-absolute-at (extract (car fs) 1))
                                          (c-noted-digest (extract (car fs) 2)))
                              (facts (cdr fs))))))
               (withs (subr (maxeff (alloc @k) (read @globals) spin (read @k) (write @k))
                            (k-with-list) unit)
                 (lambda (ws)
                   (if (null? ws)
                       #u
                       (begin (c-key-add! acc (c-absolute-at (extract (car ws) 1))
                                          (c-ints-digest (c-names-digest (c-fold 9 0)
                                                                         (extract (car ws) 2))
                                                         (extract (car ws) 3)))
                              (withs (cdr ws))))))
               (reshapes (subr (maxeff (alloc @k) (read @globals) spin (read @k) (write @k))
                               (k-reshape-list) unit)
                 (lambda (rs)
                   (if (null? rs)
                       #u
                       (begin (c-key-add! acc (c-absolute-at (extract (car rs) 1))
                                          (c-picks-digest (c-fold 10 0) (extract (car rs) 2)))
                              (reshapes (cdr rs))))))
               (check (subr (maxeff (alloc @k) (read @globals) spin (read @k) (write @k))
                            (c-key-digests) string)
                 (lambda (ks)
                   (if (null? ks)
                       ""
                       (let* ((k (extract (car ks) 1)) (kr (extract (car ks) 2))
                              (d (car (c-key-digest-in (table-ref (extract acc 1) k nil) k kr)))
                              (seen (table-ref (get c-facts-seen) k nil))
                              (before (c-key-digest-in seen k kr)))
                         (cond ((null? before)
                                (begin (table-set! (get c-facts-seen) k
                                                   (the c-key-digests
                                                        (cons (product (1 k) (2 kr) (3 d)) seen)))
                                       (check (cdr ks))))
                               ((= (car before) d) (check (cdr ks)))
                               (else (c-validate-message k kr (car before) d))))))))
        (begin (facts fs) (withs ws) (reshapes rs) (check (get (extract acc 2))))))))
(define c-key-digest-in (->* (c-key-digests int int) (listof int acyclic))
  (lambda (ks k kr)
    (cond ((null? ks) nil)
          ((and (= (extract (car ks) 1) k) (= (extract (car ks) 2) kr)) (list (extract (car ks) 3)))
          (else (c-key-digest-in (cdr ks) k kr)))))
(define c-validate-message (->* (int int int int) string)
  (lambda (k kr was now)
    (string-append "validate: the full key (" (int->string k) " " (int->string kr)
                   ") has other facts than it had before (their digests "
                   (int->string was) " and " (int->string now)
                   "): it leaves out something checking reads")))

;; An expression's identity, as a table's key: where it starts and ends, and
;; which of the expressions there it is. For tables asked once a lambda or
;; a `letrec`; those asked of every expression are by where it starts
;; (`c-by-at`), so that asking makes nothing.
(define c-span-key (->* (int int int int) k-at)
  (lambda (a b k kr) (product (1 a) (2 b) (3 k) (4 kr))))
(define c-at-hash (subr pure (k-at) int) (lambda (x) (extract x 3)))
(define c-at-is? (->* (k-at int int int int) bool) (lambda (x a b k kr) (k-at-is? x a b k kr)))
(define c-at=? (subr pure (k-at k-at) bool)
  (lambda (x y) (k-at-is? x (extract y 1) (extract y 2) (extract y 3) (extract y 4))))

;; What `t` notes of `a` `b` `k`, the newest; or `none`.
(define c-noted-in
  (->* ((listof c-noted acyclic) int int int int int) int)
  (lambda (ns a b k kr none)
    (cond ((null? ns) none)
          ((k-at-is? (extract (car ns) 1) a b k kr) (extract (car ns) 2))
          (else (c-noted-in (cdr ns) a b k kr none)))))
(define c-noted-at (->* (c-by-at int int int int int) int)
  (lambda (t a b k kr none) (c-noted-in (table-ref t k nil) a b k kr none)))
;; The same of expression `x`: where it ends, and which it is there, found
;; only if something is noted where it starts, as little is.
(define c-noted-of (->* (c-by-at exp int) int)
  (lambda (t x none)
    (let ((ns (table-ref t (exp-kth x) nil)))
      (if (null? ns) none
          (c-noted-in ns (exp-start x) (exp-end x) (exp-kth x) (exp-reading x) none)))))
;; `t` noting `n` of `at`, over what it noted before.
(define c-note! (->* (c-by-at k-at int) unit)
  (lambda (t at n)
    (let ((k (extract at 3)))
      (table-set! t k (the (listof c-noted acyclic)
                        (cons (product (1 at) (2 n)) (table-ref t k nil)))))))
(define c-new-by-at (subr (alloc @k) () c-by-at) (lambda () (make-table c-int-hash c-int=?)))

(define c-fact-table (ref c-datums-at @k) (new (make-table c-int-hash c-int=?)))

;; The procedures lambda-lifted, by index; and, by where each `letrec` is
;; (`c-span-key`), its members' (none if it is not lifted), so that its
;; register code lifts it as its stack code did, with the same words.
(define c-lifts (ref (table int c-lift @k) @k) (new (make-table c-int-hash c-int=?)))

(define c-lift-count (ref int @k) (new 0))

(define c-lifted (ref (table k-at c-lifting @k) @k) (new (make-table c-at-hash c-at=?)))

;; The parameters a lifting added to the lambda about to be compiled.
(define c-lifting-added (ref int @k) (new 0))

;; Each expression's effect summary, the greatest noted of it.
(define c-summary-table (ref c-by-at @k) (new (c-new-by-at)))

;; Each procedure converted to a convention (`k-convert-at`): what
;; `%fx26-convert` is given for it.
(define c-convert-table (ref c-by-at @k) (new (c-new-by-at)))

;; What `%fx26-convert` is given for `x`, if it is converted; or -1.
(define c-conversion-at (->* (exp) int)
  (lambda (x) (c-noted-of (get c-convert-table) x -1)))

;; Each `stage`'s code, few (`n-staged`); what `x` is checked against, if
;; it is one: a list of one.
(define c-staged-texts (ref c-staged-list @k) (new nil))
(define c-staged-at (->* (exp) c-staged-list)
  (lambda (x)
          (c-staged-find (get c-staged-texts) (exp-start x) (exp-end x) (exp-kth x)
                         (exp-reading x))))
(define c-staged-find (->* (c-staged-list int int int int) c-staged-list)
  (lambda (l a b k kr)
    (cond ((null? l) nil)
          ((c-at-is? (extract (car l) 1) a b k kr) (the c-staged-list (cons (car l) nil)))
          (else (c-staged-find (cdr l) a b k kr)))))
;; Each `apply` whose list the checker found at `acyclic` (`n-apply-shares`,
;; `k-note-apply-shares`). Every other `apply` copies its list.
(define c-shares-table (ref c-by-at @k) (new (c-new-by-at)))
;; Each definition's value that is a list nothing writes (`n-frozen-define`,
;; `k-note-frozen-define`).
(define c-frozen-table (ref c-by-at @k) (new (c-new-by-at)))
;; Each `(with #%fx n)` that is the plain `n` (`n-plain-fx`, `k-synth-fx`).
(define c-plain-table (ref c-by-at @k) (new (c-new-by-at)))
(define c-plain-fx-at (->* (int int int int) bool)
  (lambda (a b k kr) (>= (c-noted-at (get c-plain-table) a b k kr -1) 0)))
;; Whether the definition's value `a` `b` `k` is such a list.
(define c-frozen-define-at (->* (int int int int) bool)
  (lambda (a b k kr) (>= (c-noted-at (get c-frozen-table) a b k kr -1) 0)))

;; Whether the `apply` `a` `b` `k` may give its list itself.
(define c-apply-shares-at (->* (int int int int) bool)
  (lambda (a b k kr) (>= (c-noted-at (get c-shares-table) a b k kr -1) 0)))

;; Each call's callee's convention (`n-call`), by where it starts.
(define c-call-table (ref c-convs-at @k) (new (make-table c-int-hash c-int=?)))
(define c-conv-in
  (->* ((listof c-conv-noted acyclic) int int int int) k-conv)
  (lambda (ns a b k kr)
    (cond ((null? ns) (cv-fx))
          ((k-at-is? (extract (car ns) 1) a b k kr) (extract (car ns) 2))
          (else (c-conv-in (cdr ns) a b k kr)))))
;; The convention the call whose operator is `x` is compiled in (noted at
;; the operator, which every place a compiler makes the call has): its
;; callee's, `cellular` or `native`; or `fx`, which looks at the callee's kind, where its type says
;; `fx` or a convention binder, or nothing was noted (Rust's
;; `NodeFacts::call_conv`).
(define c-call-conv-at (->* (int int int int) k-conv)
  (lambda (a b k kr)
    (let ((ns (table-ref (get c-call-table) k nil)))
      (if (null? ns)
          (cv-fx)
          (tagcase (c-conv-in ns a b k kr)
            (cv-cellular () (cv-cellular)) (cv-native () (cv-native)) (else y (cv-fx)))))))
(define c-call-conv (->* (exp) k-conv)
  (lambda (x) (c-call-conv-at (exp-start x) (exp-end x) (exp-kth x) (exp-reading x))))
;; What the checker found the operation `a` `b` `k` takes (`k-datum`), in a
;; list of one; none if nothing.
(define c-datum-in
  (->* ((listof c-datum-noted acyclic) int int int int) k-datums)
  (lambda (ns a b k kr)
    (cond ((null? ns) nil)
          ((k-at-is? (extract (car ns) 1) a b k kr) (the k-datums (cons (extract (car ns) 2) nil)))
          (else (c-datum-in (cdr ns) a b k kr)))))
(define c-datum-at (->* (int int int int) k-datums)
  (lambda (a b k kr) (c-datum-in (table-ref (get c-fact-table) k nil) a b k kr)))
;; The same of an operation that holds `got`, if any: a form kept to be
;; inlined holds it (`c-resolve-extracts`).
(define c-datum-of (->* (k-datums int int int int) k-datums)
  (lambda (got a b k kr) (if (null? got) (c-datum-at a b k kr) got)))

;; Each `with` the checker saw (its `k-with-vals`, as `c-set-facts!` took
;; them), by expression: its module's values' names, in order, and their
;; positions in the module.
;; And each module reshaped (`k-reshapes`), as `c-set-facts!` took them, by
;; expression: the positions of the values it keeps. A module given through
;; a signature is reshaped, so there are many, and every expression is asked
;; after (`c-changed?`).
(define c-reshape-index (ref c-reshape-table @k) (new (make-table c-int-hash c-int=?)))
(define c-index-reshapes! (->* (k-reshape-list) unit)
  (lambda (rs)
    (if (null? rs)
        #u
        (let* ((r (car rs)) (at (c-absolute-at (extract r 1))) (k (extract at 3))
               (r (product (1 at) (2 (extract r 2)))))
          (begin (c-index-reshapes! (cdr rs))
                 (table-set! (get c-reshape-index) k
                             (the k-reshape-list
                               (cons r (table-ref (get c-reshape-index) k nil)))))))))
(define c-with-index (ref c-with-table @k) (new (make-table c-int-hash c-int=?)))
(define c-index-withs! (->* (k-with-list) unit)
  (lambda (ws)
    (if (null? ws)
        #u
        (let* ((w (car ws)) (at (c-absolute-at (extract w 1))) (k (extract at 3))
               (w (product (1 at) (2 (extract w 2)) (3 (extract w 3)))))
          (begin (c-index-withs! (cdr ws))
                 (table-set! (get c-with-index) k
                             (the k-with-list
                               (cons w (table-ref (get c-with-index) k nil)))))))))
;; The `with` `a` `b` `k`, in a list of one; none if the checker did not see
;; it.
(define c-with-in
  (->* (k-with-list int int int int) k-with-list)
  (lambda (ws a b k kr)
    (cond ((null? ws) nil)
          ((k-at-is? (extract (car ws) 1) a b k kr) ws)
          (else (c-with-in (cdr ws) a b k kr)))))
;; Its module's values' names, in a list of one; none if it was not seen.
(define c-with-at
  (->* (int int int int) c-with-names)
  (lambda (a b k kr)
    (let ((ws (c-with-in (table-ref (get c-with-index) k nil) a b k kr)))
      (if (null? ws) nil (the c-with-names (cons (extract (car ws) 2) nil))))))
;; Their positions in the module, likewise.
(define c-with-places-at
  (->* (int int int int) (listof k-ids @k))
  (lambda (a b k kr)
    (let ((ws (c-with-in (table-ref (get c-with-index) k nil) a b k kr)))
      (if (null? ws) nil (the (listof k-ids @k) (cons (extract (car ws) 3) nil))))))
;; Module `x` reshaped, in a list of one; none if it is not.
(define c-reshape-in
  (->* (k-reshape-list int int int int) k-reshape-list)
  (lambda (rs a b k kr)
    (cond ((null? rs) nil)
          ((k-at-is? (extract (car rs) 1) a b k kr) rs)
          (else (c-reshape-in (cdr rs) a b k kr)))))
(define c-reshape-of (->* (exp) k-reshape-list)
  (lambda (x)
    (let* ((k (exp-kth x)) (kr (exp-reading x)) (rs (table-ref (get c-reshape-index) k nil)))
      (if (null? rs) rs (c-reshape-in rs (exp-start x) (exp-end x) k kr)))))
;; The positions of the values the module `x` reshaped keeps, in a list of
;; one; none if it is not reshaped.
(define c-reshape-at (->* (exp) (listof k-picks @k))
  (lambda (x)
    (let ((rs (c-reshape-of x)))
      (if (null? rs) nil (the (listof k-picks @k) (cons (extract (car rs) 2) nil))))))
;; Whether the module `x` is reshaped.
(define c-reshaped-at? (->* (exp) bool)
  (lambda (x) (not (null? (c-reshape-of x)))))
;; Whether `x`'s value is changed as it is given: converted to a
;; convention, or a module reshaped.
(define c-changed? (->* (exp) bool)
  (lambda (x)
    (or (>= (c-conversion-at x) 0) (c-reshaped-at? x) (not (null? (c-staged-at x)))))))))
