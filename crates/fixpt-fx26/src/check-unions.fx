;;; The checker, in FX-26: unions (`docs/research/logical-types.md`, L1),
;;; as `check.rs` has them: the shapes a value may have at run time, a
;;; union's members made normal, and what a test of a shape narrows.
;;; After `check-print.fx`, which shows a member in an error; part of the
;;; checker, `check-types.fx` first.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-unions-module (module
;; The shapes, by number in `check.rs`'s `SHAPES` order: 0 int, 1 f64,
;; 2 f32, 3 char, 4 bool, 5 nil, 6 pair, 7 string, 8 symbol, 9 procedure,
;; 10 bloblet, 11 box, 12 sum, 13 product. A type's shapes are a mask, bit
;; `k` shape `k`'s, or -1 if they are not known.
(define k-shape-count int 14)
(define k-shape-nil int 5)
(define k-shape-pair int 6)
;; The standard predicate that tests for shape `k`.
(define k-shape-predicate (subr pure (int) string)
  (lambda (k)
    (case k
      ((0) "int?") ((1) "f64?") ((2) "f32?") ((3) "char?") ((4) "bool?") ((5) "null?")
      ((6) "pair?") ((7) "string?") ((8) "symbol?") ((9) "procedure?") ((10) "array?")
      ((11) "ref?") ((12) "sum?") (else "product?"))))
(define k-base-shape (subr (read @globals) (symbol) int)
  (lambda (s)
    (case (symbol->string s)
      (("int" "i32" "u32" "i64" "u64") 0) (("f64") 1) (("f32") 2) (("char") 3) (("bool") 4)
      (("string") 7)
      ;; `unit` is the symbol `#u` at run time.
      (("symbol" "unit") 8)
      (else -1))))
;; Shape `k`'s bit, or -1 for none known.
(define k-shape-bit (subr pure (int) int)
  (lambda (k) (if (< k 0) -1 (arithmetic-shift 1 k))))
(define k-one-id (subr (alloc @t) (int) k-ids)
  (lambda (m) (the k-ids (cons m nil))))
(define k-ids-append (subr (maxeff (read @globals) (alloc @t)) (k-ids k-ids) k-ids)
  (lambda (xs ys) (if (null? xs) ys (the k-ids (cons (car xs) (k-ids-append (cdr xs) ys))))))
(define-rec
  ;; The shapes a value of type `t` may have at run time: what its tag
  ;; says, and for a bloblet its kind. Not known for a variable, an
  ;; abstract or generative type, `datum`: no union may have a member of
  ;; one. `seen`, the unions met on the way down: one met again is its own
  ;; member, whose shape is not known.
  (k-run-shape-in (subr (maxeff kreads (alloc @t) spin) (int k-ids) int)
    (lambda (t0 seen)
      (let ((t (k-resolve t0)))
      (tagcase (k-get t)
        (ty-base (s) (k-shape-bit (k-base-shape s)))
        (ty-nat (z) 1)
        (ty-nil () 32)
        (ty-proving (t e) 16)
        (ty-false () 16)
        (ty-pair (a b r nl) (if nl 96 64))
        (ty-nlist (e z r) 96)
        (ty-subr (e ps r cv) 512)
        (ty-comp (a h e r) 512)
        ;; An array is a bloblet as `(bloblet …)` is, of the same kind.
        (ty-array (a r) 1024)
        (ty-bloblet (fs z r) 1024)
        (ty-ref (a r) 2048)
        (ty-sum (ps) 4096)
        (ty-product (ps) 8192)
        (ty-union (ms)
          (if (k-has-id? seen t) -1 (k-run-shapes ms (the k-ids (cons t seen)))))
        (ty-void () 0)
        (else y -1)))))
  (k-run-shapes (subr (maxeff kreads (alloc @t) spin) (k-ids k-ids) int)
    (lambda (ms seen)
      (if (null? ms)
          0
          (let ((s (k-run-shape-in (car ms) seen)) (rest (k-run-shapes (cdr ms) seen)))
            (if (or (< s 0) (< rest 0)) -1 (bitwise-ior s rest)))))))
;; The same, from the top.
(define k-run-shape (subr (maxeff kreads (alloc @t) spin) (int) int)
  (lambda (t) (k-run-shape-in t nil)))
(define k-shape-known? (subr (maxeff kreads (alloc @t) spin) (int) bool)
  (lambda (t) (>= (k-run-shape t) 0)))
;; Whether two masks share a shape; whether all of `s`'s are `u`'s.
(define k-shapes-meet? (subr pure (int int) bool)
  (lambda (s u) (not (= (bitwise-and s u) 0))))
(define k-shapes-within? (subr pure (int int) bool)
  (lambda (s u) (= (bitwise-and s u) s)))
;; Whether `t` and `u` have known shapes, none of them shared.
(define k-shapes-miss? (subr (maxeff kreads (alloc @t) spin) (int int) bool)
  (lambda (t u)
    (let ((s (k-run-shape t)) (v (k-run-shape u)))
      (and (>= s 0) (>= v 0) (not (k-shapes-meet? s v))))))
;; Whether `t` and `u` have the same known shapes.
(define k-same-shape? (subr (maxeff kreads (alloc @t) spin) (int int) bool)
  (lambda (t u)
    (let ((s (k-run-shape t))) (and (>= s 0) (= s (k-run-shape u))))))

;; The first of `ys` with `x`'s shapes, known, or -1.
(define k-same-shape-in (subr (maxeff kreads (alloc @t) spin) (int k-ids) int)
  (lambda (x ys)
    (cond ((null? ys) -1)
          ((k-same-shape? (car ys) x) (car ys))
          (else (k-same-shape-in x (cdr ys))))))

(define k-holding-in (subr (maxeff kreads (alloc @t) spin) (int k-ids) int)
  (lambda (s ys)
    (cond ((null? ys) -1)
          ((k-shapes-within? s (k-run-shape (car ys))) (car ys))
          (else (k-holding-in s (cdr ys))))))
;; The first of `ys` whose shapes hold `x`'s, known and some, or -1.
(define k-member-holding (subr (maxeff kreads (alloc @t) spin) (int k-ids) int)
  (lambda (x ys)
    (let ((s (k-run-shape x)))
      (if (<= s 0) -1 (k-holding-in s ys)))))

;; Whether `t` is `false`, or a union with it.
(define k-false-member? (subr (maxeff kreads spin) (k-ids) bool)
  (lambda (ms)
    (and (not (null? ms))
         (or (tagcase (k-get (car ms)) (ty-false () #t) (else y #f)) (k-false-member? (cdr ms))))))
(define k-false-expected? (subr (maxeff kreads spin) (int) bool)
  (lambda (t)
    (tagcase (k-get t) (ty-false () #t) (ty-union (ms) (k-false-member? ms)) (else y #f))))

;; `ms`, resolved, a union among them its members.
(define k-union-flat (subr (maxeff kreads (alloc @t) spin) (k-ids) k-ids)
  (lambda (ms)
    (if (null? ms)
        nil
        (let ((m (k-resolve (car ms))) (rest (k-union-flat (cdr ms))))
          (tagcase (k-get m)
            (ty-union (xs) (k-ids-append (k-union-flat xs) rest))
            (else y (the k-ids (cons m rest))))))))
(define k-count-pairs (subr (maxeff kreads spin) (k-ids) int)
  (lambda (ms)
    (if (null? ms)
        0
        (+ (tagcase (k-get (car ms)) (ty-pair (a b r nl) 1) (else y 0)) (k-count-pairs (cdr ms))))))
(define k-has-nil? (subr (maxeff kreads spin) (k-ids) bool)
  (lambda (ms)
    (and (not (null? ms))
         (or (tagcase (k-get (car ms)) (ty-nil () #t) (else y #f)) (k-has-nil? (cdr ms))))))
;; `ms` with its first `nil` gone and its pair one that may be `nil`.
(define k-merge-nil (subr (maxeff kstate spin) (k-ids bool) k-ids)
  (lambda (ms dropped)
    (if (null? ms)
        nil
        (let ((m (car ms)))
          (tagcase (k-get m)
            (ty-nil ()
              (if dropped (the k-ids (cons m (k-merge-nil (cdr ms) #t))) (k-merge-nil (cdr ms) #t)))
            (ty-pair (a b r nl)
              (let ((p (if nl m (k-ty-new (ty-pair a b r #t)))))
                (the k-ids (cons p (k-merge-nil (cdr ms) dropped)))))
            (else y (the k-ids (cons m (k-merge-nil (cdr ms) dropped)))))))))
;; `nil` beside a pair: the pair that may be `nil`.
(define k-union-merged (subr (maxeff kstate spin) (k-ids) k-ids)
  (lambda (flat)
    (if (and (k-has-nil? flat) (= (k-count-pairs flat) 1)) (k-merge-nil flat #f) flat)))
(define k-union-build (subr (maxeff kstate spin) (k-ids) int)
  (lambda (ms)
    (cond ((null? ms) k-void)
          ((null? (cdr ms)) (car ms))
          (else (k-ty-new (ty-union ms))))))
;; The first member whose shape is not known, or -1.
(define k-unknown-member (subr (maxeff kreads (alloc @t) spin) (k-ids) int)
  (lambda (ms)
    (cond ((null? ms) -1)
          ((k-shape-known? (car ms)) (k-unknown-member (cdr ms)))
          (else (car ms)))))
;; A member after the first of `ms` that shares a shape with `m`, or -1.
(define k-overlap-with (subr (maxeff kreads (alloc @t) spin) (int k-ids) int)
  (lambda (m ms)
    (cond ((null? ms) -1)
          ((k-shapes-meet? (k-run-shape m) (k-run-shape (car ms))) (car ms))
          (else (k-overlap-with m (cdr ms))))))
(define k-union-overlap (subr (maxeff checks spin) (k-ids int int) unit)
  (lambda (ms start end)
    (if (null? ms)
        #u
        (let ((o (k-overlap-with (car ms) (cdr ms))))
          (if (< o 0)
              (k-union-overlap (cdr ms) start end)
              (k-fail (k-cat5 "a union's members must differ in shape at run time: a "
                              (k-show-ty (car ms)) " and a " (k-show-ty o) " do not")
                      start end))))))
(define-type k-pending (productof (1 int) (2 int) (3 int)))
(define k-pendings-append
  (subr (maxeff (read @globals) (alloc @t)) (k-pendings k-pending) k-pendings)
  (lambda (ps p)
    (if (null? ps)
        (the k-pendings (cons p nil))
        (the k-pendings (cons (car ps) (k-pendings-append (cdr ps) p))))))
(define k-union-known (subr (maxeff checks spin) (k-ids int int) unit)
  (lambda (ms start end)
    (let ((unknown (k-unknown-member ms)))
      (if (>= unknown 0)
          (k-fail (k-cat3 "a " (k-show-ty unknown)
                          " cannot be in a union: its shape at run time is not known")
                  start end)
          #u))))
;; Whether a member is not yet known: a recursive type's own name, read
;; before its definition is.
(define k-open-member? (subr (maxeff kreads spin) (int) bool)
  (lambda (m) (tagcase (k-get m) (ty-link (x) (null? x)) (else y #f))))
(define k-any-open? (subr (maxeff kreads spin) (k-ids) bool)
  (lambda (ms) (and (not (null? ms)) (or (k-open-member? (car ms)) (k-any-open? (cdr ms))))))
;; The union of `members`, normalized: unions in it flattened, `nil` and a
;; pair that is not `nil` made the pair that may be, and one member
;; itself. Each member must have a known shape, and no two the same; one
;; not yet known, the union checked once it is (`k-check-pending-unions`).
(define k-union-of (subr (maxeff checks spin) (k-ids int int) int)
  (lambda (members start end)
    (let* ((flat (k-union-flat members)) (pending (k-any-open? flat)))
      (begin
        (if pending #u (k-union-known flat start end))
        (let ((merged (k-union-merged flat)))
          (if pending
              (let ((u (k-ty-new (ty-union merged))))
                (begin (set k-pending-unions
                            (k-pendings-append (get k-pending-unions)
                                               (product (1 u) (2 start) (3 end))))
                       u))
              (begin (k-union-overlap merged start end) (k-union-build merged))))))))
;; The unions read before what they name was, each whose members are all
;; known now checked as `k-union-of` would have.
(define k-check-pending-unions (subr (maxeff checks spin) () unit)
  (lambda () (set k-pending-unions (k-check-pendings (get k-pending-unions)))))
(define k-check-pendings (subr (maxeff checks spin) (k-pendings) k-pendings)
  (lambda (ps)
    (if (null? ps)
        nil
        (let* ((p (car ps))
               (ms (tagcase (k-get (extract p 1)) (ty-union (ms) ms) (else y (the k-ids nil)))))
          (if (k-any-open? ms)
              (the k-pendings (cons p (k-check-pendings (cdr ps))))
              (begin (k-union-known ms (extract p 2) (extract p 3))
                     (k-union-overlap ms (extract p 2) (extract p 3))
                     (k-check-pendings (cdr ps))))))))

;; A pair that may be `nil`, tested for either, is two members here.
(define k-member-parts (subr (maxeff kstate spin) (int int) k-ids)
  (lambda (m k)
    (tagcase (k-get m)
      (ty-pair (a b r nl)
        (if (and nl (or (= k 5) (= k 6)))
            (the k-ids (cons (k-ty-new (ty-nil)) (k-one-id (k-ty-new (ty-pair a b r #f)))))
            (k-one-id m)))
      (else y (k-one-id m)))))
(define-type k-sides (pairof k-ids k-ids @t))
;; Members `ps` to the side where shape `k` is found, or not, or both.
(define k-sort-parts (subr (maxeff kstate spin) (k-ids int k-sides) k-sides)
  (lambda (ps k acc)
    (if (null? ps)
        acc
        (let* ((p (car ps)) (s (k-run-shape p)) (mask (k-shape-bit k))
               (in (k-shapes-within? s mask)) (out (not (k-shapes-meet? s mask)))
               (inside (if out (car acc) (the k-ids (cons p (car acc)))))
               (outside (if in (cdr acc) (the k-ids (cons p (cdr acc))))))
          (k-sort-parts (cdr ps) k (cons inside outside))))))
(define k-reverse-ids (subr (maxeff (read @globals) (alloc @t)) (k-ids k-ids) k-ids)
  (lambda (xs acc) (if (null? xs) acc (k-reverse-ids (cdr xs) (the k-ids (cons (car xs) acc))))))
(define k-split-into (subr (maxeff kstate spin) (k-ids int k-sides) k-sides)
  (lambda (ms k acc)
    (if (null? ms)
        acc
        (k-split-into (cdr ms) k (k-sort-parts (k-member-parts (k-resolve (car ms)) k) k acc)))))
(define k-split-members (subr (maxeff kstate spin) (k-ids int) k-sides)
  (lambda (ms k)
    (let ((sides (k-split-into ms k (cons nil nil))))
      (cons (k-reverse-ids (car sides) nil) (k-reverse-ids (cdr sides) nil)))))
;; Type `t` where a value of it is found of shape `k`, and where not, -1
;; for no narrowing: a union's members of that shape, and the rest; a pair
;; that may be `nil`, the pair that is not, where `null?` does not hold or
;; `pair?` does. Nothing else is narrowed (a list found `nil` stays a list,
;; which is what `cons` onto it wants).
(define-type k-split (productof (1 int) (2 int)))
(define k-narrowed-by (subr (maxeff kstate spin) (int int) k-split)
  (lambda (t k)
    (let ((none (product (1 -1) (2 -1))))
      (tagcase (k-get t)
        (ty-pair (a b r nl)
          (if nl
              (let ((not-nil (k-ty-new (ty-pair a b r #f))))
                (cond ((= k 5) (product (1 -1) (2 not-nil)))
                      ((= k 6) (product (1 not-nil) (2 -1)))
                      (else none)))
              none))
        (ty-union (ms)
          (let ((parts (k-split-members ms k)))
            (product (1 (k-union-build (k-union-merged (car parts))))
                     (2 (k-union-build (k-union-merged (cdr parts)))))))
        (else y none)))))
))

(define k-shape-count (with check-unions-module k-shape-count))
(define k-shape-nil (with check-unions-module k-shape-nil))
(define k-shape-pair (with check-unions-module k-shape-pair))
(define k-shape-predicate (with check-unions-module k-shape-predicate))
(define k-run-shape (with check-unions-module k-run-shape))
(define k-same-shape? (with check-unions-module k-same-shape?))
(define k-shapes-miss? (with check-unions-module k-shapes-miss?))
(define k-same-shape-in (with check-unions-module k-same-shape-in))
(define k-member-holding (with check-unions-module k-member-holding))
(define k-union-of (with check-unions-module k-union-of))
(define k-false-expected? (with check-unions-module k-false-expected?))
(define k-check-pending-unions (with check-unions-module k-check-pending-unions))
(define-type k-split (select check-unions-module k-split))
(define k-narrowed-by (with check-unions-module k-narrowed-by))
