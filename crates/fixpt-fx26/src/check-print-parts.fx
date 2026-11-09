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
    ;; Part of it in a file of its own (`check-sizes.fx`), made of what it is
    ;; given.
    (let ((check-sizes
           ((load-input "fx26:check-sizes.fx")
            check-types check-effects check-env)))
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
        (a-stage () "stage")
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
;; driver says otherwise (a `nativecc` machine).
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
;; Whether a type has parts, so that a name abbreviates it: not a base
;; type, a variable, `nil`, `false` or `void`, each a word already
;; (`Checker::abbreviates`).
(define k-abbreviates? (->* (int) bool)
  (lambda (t)
    (tagcase (k-get t)
      (ty-base (s) #f) (ty-var (v) #f) (ty-nil () #f) (ty-false () #f) (ty-void () #f)
      (else y #t))))
;; Whether two effects have the same atoms.
(define k-eff-same? (->* (k-eff k-eff) bool)
  (lambda (e f)
    (letrec ((in? (subr (maxeff (read @globals) spin) (k-atom k-eff) bool)
                  (lambda (a g) (and (not (null? g)) (or (k-atom=? a (car g)) (in? a (cdr g))))))
             (all-in? (subr (maxeff (read @globals) spin) (k-eff k-eff) bool)
                      (lambda (x g) (or (null? x) (and (in? (car x) g) (all-in? (cdr x) g))))))
      (and (all-in? e f) (all-in? f e)))))
;; Whether `a` and `b` are one type by structure, following links: the same
;; kind of node, the same regions, effects and sizes, and parts the same in
;; order; a node of a kind not compared so only itself. A pair met again is
;; the same (`seen`). As `Checker::same_ty`.
(define-rec
  (k-same-shape? (->* (int int k-pairs) bool)
    (lambda (a0 b0 seen)
      (let ((a (k-resolve a0)) (b (k-resolve b0)))
        (or (= a b) (k-pair-in? a b seen)
            (let ((s (the k-pairs (cons (cons a b) seen))))
              (tagcase (k-get a)
                (ty-base (x) (tagcase (k-get b) (ty-base (y) (symbol=? x y)) (else z #f)))
                (ty-var (v) (tagcase (k-get b) (ty-var (w) (= v w)) (else z #f)))
                (ty-nil () (tagcase (k-get b) (ty-nil () #t) (else z #f)))
                (ty-false () (tagcase (k-get b) (ty-false () #t) (else z #f)))
                (ty-void () (tagcase (k-get b) (ty-void () #t) (else z #f)))
                (ty-nat (m) (tagcase (k-get b) (ty-nat (n) (k-size=? m n)) (else z #f)))
                (ty-subr (e ps r cv spc)
                  (tagcase (k-get b)
                    (ty-subr (f qs q dv tpc)
                      (and (null? spc) (null? tpc) (k-conv=? cv dv) (k-eff-same? e f)
                           (k-same-shapes? ps qs s) (k-same-shape? r q s)))
                    (else z #f)))
                (ty-poly (bs x)
                  (tagcase (k-get b)
                    (ty-poly (cs y) (and (k-binders-same? bs cs) (k-same-shape? x y s)))
                    (else z #f)))
                (ty-ref (x r)
                  (tagcase (k-get b)
                    (ty-ref (y q) (and (k-region=? r q) (k-same-shape? x y s)))
                    (else z #f)))
                (ty-pair (x xt r nl)
                  (tagcase (k-get b)
                    (ty-pair (y yt q nm)
                      (and (k-region=? r q) (bool=? nl nm) (k-same-shape? x y s)
                           (k-same-shape? xt yt s)))
                    (else z #f)))
                (ty-product (ps)
                  (tagcase (k-get b) (ty-product (qs) (k-same-parts? ps qs s)) (else z #f)))
                (ty-sum (ps) (tagcase (k-get b) (ty-sum (qs) (k-same-parts? ps qs s)) (else z #f)))
                (ty-array (x m r)
                  (tagcase (k-get b)
                    (ty-array (y n q) (and (k-size=? m n) (k-region=? r q) (k-same-shape? x y s)))
                    (else z #f)))
                (ty-nlist (x m r)
                  (tagcase (k-get b)
                    (ty-nlist (y n q) (and (k-size=? m n) (k-region=? r q) (k-same-shape? x y s)))
                    (else z #f)))
                (ty-named (g xs)
                  (tagcase (k-get b)
                    (ty-named (h ys) (and (= g h) (k-same-descs? xs ys s)))
                    (else z #f)))
                (ty-union (ms)
                  (tagcase (k-get b) (ty-union (ns) (k-same-shapes? ms ns s)) (else z #f)))
                (else z #f)))))))
  (k-same-shapes? (->* (k-ids k-ids k-pairs) bool)
    (lambda (xs ys s)
      (cond ((null? xs) (null? ys))
            ((null? ys) #f)
            (else (and (k-same-shape? (car xs) (car ys) s) (k-same-shapes? (cdr xs) (cdr ys) s))))))
  (k-same-parts? (->* (k-parts k-parts k-pairs) bool)
    (lambda (ps qs s)
      (cond ((null? ps) (null? qs))
            ((null? qs) #f)
            (else (and (symbol=? (extract (car ps) 1) (extract (car qs) 1))
                       (k-same-shape? (extract (car ps) 2) (extract (car qs) 2) s)
                       (k-same-parts? (cdr ps) (cdr qs) s))))))
  (k-same-descs? (->* (k-descs k-descs k-pairs) bool)
    (lambda (xs ys s)
      (cond ((null? xs) (null? ys))
            ((null? ys) #f)
            (else
             (and (tagcase (car xs)
                    (dt (x) (tagcase (car ys) (dt (y) (k-same-shape? x y s)) (else z #f)))
                    (df (x) (tagcase (car ys) (df (y) (k-same-shape? x y s)) (else z #f)))
                    (dr (r) (tagcase (car ys) (dr (q) (k-region=? r q)) (else z #f)))
                    (de (e) (tagcase (car ys) (de (f) (k-eff-same? e f)) (else z #f)))
                    (dz (m) (tagcase (car ys) (dz (n) (k-size=? m n)) (else z #f)))
                    (dc (c) (tagcase (car ys) (dc (d) (k-conv=? c d)) (else z #f))))
                  (k-same-descs? (cdr xs) (cdr ys) s)))))))
(define-type k-pairs (listof (pairof int int acyclic) acyclic))
(define k-pair-in? (->* (int int k-pairs) bool)
  (lambda (a b ps)
    (and (not (null? ps))
         (or (and (= (car (car ps)) a) (= (cdr (car ps)) b)) (k-pair-in? a b (cdr ps))))))
(define k-binders-same? (->* (k-binders k-binders) bool)
  (lambda (bs cs)
    (cond ((null? bs) (null? cs))
          ((null? cs) #f)
          (else (and (= (extract (car bs) 1) (extract (car cs) 1))
                     (= (extract (car bs) 2) (extract (car cs) 2))
                     (k-binders-same? (cdr bs) (cdr cs)))))))
;; Whether a name of type `d` abbreviates `t` (`Checker::abbreviation`'s
;; `fits`): `t` is its type, and has parts.
(define k-fits? (->* (int int) bool)
  (lambda (d t) (and (k-abbreviates? d) (k-same-shape? d t nil))))
(define k-same-type? (->* (int int) bool)
  (lambda (a b) (k-same-shape? a b nil)))

;; Shapes at run time (`check-unions.fx` uses them; here, for a union's
;; former, as shown). The shapes, by number in `check.rs`'s `SHAPES` order:
;; 0 int, 1 f64, 2 f32, 3 char, 4 bool, 5 nil, 6 pair, 7 string, 8 symbol,
;; 9 procedure, 10 bloblet, 11 box, 12 sum, 13 product, 14 vector, 15
;; bytevector, 16 keyword. A type's shapes are a mask, bit `k` shape `k`'s,
;; or -1 if they are not known.
(define k-base-shape (->* (symbol) int)
  (lambda (s)
    (case (symbol->string s)
      (("int" "i8" "u8" "i32" "u32" "i64" "u64") 0)
      (("f64") 1) (("f32") 2) (("char") 3) (("bool") 4)
      (("string") 7)
      ;; `unit` is the symbol `#u` at run time.
      (("symbol" "unit") 8)
      (("vector") 14) (("bytevector") 15) (("keyword") 16)
      (else -1))))
;; Shape `k`'s bit, or -1 for none known.
(define k-shape-bit (->* (int) int)
  (lambda (k) (if (< k 0) -1 (arithmetic-shift 1 k))))
(define-rec
  ;; The shapes a value of type `t` may have at run time: what its tag
  ;; says, and for a bloblet its kind. Not known for a variable, or an
  ;; abstract or generative type: no union may have a member of one.
  ;; `seen`, the unions met on the way down: one met again is its own
  ;; member, whose shape is not known.
  (k-run-shape-in (->* (int k-ids) int)
    (lambda (t0 seen)
      (let ((t (k-resolve t0)))
      (tagcase (k-get t)
        (ty-base (s) (k-shape-bit (k-base-shape s)))
        (ty-nat (z) 1)
        (ty-nil () 32)
        (ty-false () 16)
        (ty-pair (a b r nl) (if nl 96 64))
        (ty-nlist (e z r) 96)
        (ty-subr (e ps r cv spc) 512)
        (ty-comp (a h e r once) 512)
        ;; An array is a bloblet as `(bloblet …)` is, of the same kind.
        (ty-array (a nz r) 1024)
        (ty-bloblet (fs z r) 1024)
        (ty-ref (a r) 2048)
        (ty-sum (ps) 4096)
        (ty-product (ps) 8192)
        (ty-union (ms)
          (if (k-has-id? seen t) -1 (k-run-shapes ms (the k-ids (cons t seen)))))
        (ty-allof (ms)
          (if (k-has-id? seen t) -1 (k-run-shapes ms (the k-ids (cons t seen)))))
        (ty-void () 0)
        (else y -1)))))
  (k-run-shapes (->* (k-ids k-ids) int)
    (lambda (ms seen)
      (if (null? ms)
          0
          (let ((s (k-run-shape-in (car ms) seen)) (rest (k-run-shapes (cdr ms) seen)))
            (if (or (< s 0) (< rest 0)) -1 (bitwise-ior s rest)))))))
;; The same, from the top.
(define k-run-shape (->* (int) int)
  (lambda (t) (k-run-shape-in t nil)))
;; Whether no two of `ms` share a known shape: a union shown as `oneof`,
;; else `anyof` (`logical-types.md` §8.5). As `Checker::members_apart`.
(define k-members-apart? (->* (k-ids) bool)
  (lambda (ms)
    (letrec ((shape (->* (int) int) (lambda (m) (let ((s (k-run-shape m))) (if (< s 0) 0 s))))
             (apart (->* (int k-ids) bool)
               (lambda (s ns)
                 (or (null? ns) (and (= (bitwise-and s (shape (car ns))) 0) (apart s (cdr ns)))))))
      (or (null? ms) (and (apart (shape (car ms)) (cdr ms)) (k-members-apart? (cdr ms)))))))
;; A hash of type `t`'s shape, two nodes down: two types `k-same-shape?`
;; finds one hash the same (a node of a kind not compared so, its id).
(define k-shape-hash (->* (int int) int)
  (lambda (t0 depth)
    (let ((t (k-resolve t0)))
      (if (= depth 0)
          0
          (let ((h (lambda ((x int)) (k-shape-hash x (- depth 1))))
                (mix (lambda ((a int) (b int)) (modulo (+ (* a 31) b) 65521))))
            (tagcase (k-get t)
              (ty-base (s) (mix 1 (string-length (symbol->string s))))
              (ty-var (v) (mix 2 v)) (ty-nil () 3) (ty-false () 4) (ty-void () 5) (ty-nat (m) 6)
              (ty-subr (e ps r cv spc) (mix (mix 7 (k-length ps)) (h r)))
              (ty-poly (bs x) (mix 8 (h x)))
              (ty-ref (x r) (mix 9 (h x)))
              (ty-pair (x y r nl) (mix (mix 10 (h x)) (h y)))
              (ty-product (ps) (mix 11 (k-length ps)))
              (ty-sum (ps) (mix 12 (k-length ps)))
              (ty-array (x m r) (mix 13 (h x)))
              (ty-nlist (x m r) (mix 14 (h x)))
              (ty-named (g xs) (mix 15 g))
              (ty-union (ms) (mix 16 (k-length ms)))
              (ty-allof (ms) (mix 19 (k-length ms)))
              (else y (mix 17 t))))))))
;; Whether `n` is a name the machinery gives a type for a step, not one a
;; program wrote (`%stage-type` and its kin, `stage.rs`): no type is shown
;; by it.
(define k-own-name? (->* (symbol) bool)
  (lambda (n)
    (let ((s (symbol->string n)))
      (and (> (string-length s) 0) (char=? (string-ref s 0) #\%)))))
(define k-abbrev-in (->* (k-scope k-scope int int) k-strings)
  (lambda (all ds i t)
    (if (null? ds)
        nil
        (let ((n (car (car ds))))
          (tagcase (cdr (car ds))
            (ds-rec (d)
              (if (and (not (k-own-name? n)) (k-fits? d t) (not (k-rec-named-within? all i n)))
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
              (k-atree-of (cdr ds) (+ i 1)
                          (if (and (k-abbreviates? t) (not (k-own-name? (car (car ds)))))
                              (k-atree-put tr (k-shape-hash t 2) t (car (car ds)) i)
                              tr))))
          (else y (k-atree-of (cdr ds) (+ i 1) tr))))))
;; Scope `ds` from binding `i` on.
(define k-scope-from (->* (k-scope int) k-scope)
  (lambda (ds i) (if (or (<= i 0) (null? ds)) ds (k-scope-from (cdr ds) (- i 1)))))
;; The name `define-type` gave `t`, as `k-abbrev-in` finds it, by tree `trs`
;; if there is one.
;; Whether a type shown may be named: not while one is shown for a checker
;; of another program (`k-show-ty-whole`).
(define k-naming (ref bool @t) (new #t))
(define k-naming! (->* (bool) unit) (lambda (on) (set k-naming on)))
(define k-abbrev-by (->* (k-atrees int) k-strings)
  (lambda (trs t)
    (let ((all (get k-dscope)))
      (if (not (get k-naming))
          nil
      (if (null? trs)
          (k-abbrev-in all all 0 t)
          ;; Of those of its shape's hash, the innermost that fits, not
          ;; shadowed (`k-abbrev-in`'s).
          (if (not (k-abbreviates? t))
              nil
              (let ((best (k-atree-best (car trs) (k-shape-hash t 2) t all -1 '|()|)))
                (if (< (car best) 0)
                    nil
                    (the k-strings (list (symbol->string (cdr best))))))))))))
;; A binding's number and name, the best found.
(define-type k-best (pairof int symbol acyclic))
;; Of the entries of `tr` of hash `h`, the innermost (least binding number)
;; whose type fits `t` and whose name is not shadowed in scope `all`; with
;; `bi`/`bn`, the best so far (-1 if none).
(define-rec
  (k-atree-best (->* (k-atree int int k-scope int symbol) k-best)
    (lambda (tr h t all bi bn)
      (tagcase tr
        (a-leaf () (the k-best (cons bi bn)))
        (a-node (h2 t2 n2 i2 l r)
          (cond ((< h h2) (k-atree-best l h t all bi bn))
                ((> h h2) (k-atree-best r h t all bi bn))
                (else
                 (let* ((here (if (and (or (< bi 0) (< i2 bi)) (k-fits? t2 t)
                                       (not (k-rec-named-within? all i2 n2)))
                                  (the k-best (cons i2 n2))
                                  (the k-best (cons bi bn))))
                        (left (k-atree-best l h t all (car here) (cdr here))))
                   (k-atree-best r h t all (car left) (cdr left))))))))))
;; Binder `v` of kind `kind`: `(name kind)`, or `(name region bound)`.
(define k-binder-show (->* (int int) string)
  (lambda (v kind)
    (let* ((b (k-bound-of v)) (named (k-cat3 (k-dvar-text v "b") " " (k-kind-text kind)))
           (d (if (k-distinct-var? v) " distinct)" ")")))
      (cond ((not (null? b)) (k-cat5 "(" named " " (k-region-show (car b)) d))
            ;; An effect binder's bound (`TODO.md` §226).
            ((not (null? (k-effect-bound-of v)))
             (k-cat5 "(" named " (within " (k-show-effect (car (k-effect-bound-of v))) "))"))
            (else (k-cat3 "(" named d))))))
(define k-show-binders (->* (k-binders) k-strings)
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((b (car bs)))
          (cons (k-binder-show (extract b 1) (extract b 2)) (k-show-binders (cdr bs)))))))

;; How deep `t` is in `path`, newest first: its place from the root, from 1.
(define k-depth-of (->* (k-ids int) int)
  (lambda (path t) (if (= (car path) t) (k-length path) (k-depth-of (cdr path) t))))
;; Given on, all `check-sizes.fx` defines.
(import check-sizes k-size-lit k-size-as-lit k-size-plus k-term=? k-terms=? k-size=? k-map-find
        k-size-var k-term-cons k-terms-add k-size-add-scaled k-coef-of k-size-replace k-size-facts
        k-unit-terms k-apply-fact k-reduced k-coefs-nonneg? k-plainly-nonneg? k-nonneg-by-fact?
        k-gcd k-abs k-terms-gcd k-terms-div k-tightened k-var-into k-terms-vars k-lins-vars
        k-lins-append k-lins-of-vars k-coef-in k-sign k-lins-signed k-lins-cancel k-lins-combined
        k-lins-count k-lins-contradict? k-fm-eliminate k-fact-lins k-refuted-below? k-size-nonneg?
        k-size-zero? k-size-eq? k-tail-size k-size-le? k-size-given k-subst-size)

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
          ((k-fits? (extract (car ps) 2) t)
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
;; The variables free in `ss`, printed with `k-show-marks` on, in order: what
;; a staged check is given the evidence of (`docs/research/eval.md`).
(define k-free-shown (->* (k-strings) k-ids)
  (lambda (ss) (let ((ms (k-marks-all ss))) (k-free-marks ms ms nil))))
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
))))
