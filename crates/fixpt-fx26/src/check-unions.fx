;;; The checker, in FX-26: unions (`docs/research/logical-types.md`, L1),
;;; as `check.rs` has them: the shapes a value may have at run time, a
;;; union's members made normal, and what a test of a shape narrows.
;;; After `check-print.fx`, which shows a member in an error; part of the
;;; checker, `check-types.fx` first.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
;; Its types (`check-unions-types.fx`), loaded before the module so that they are not
;; among its values; the module names what it uses of them.
(let* ((check-unions-types (load-module "fx26:check-unions-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-print (select check-print-types check-print-sig))
           (check-env (select check-env-types check-env-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module
(hide (include check-unions-types) (include check-types-types))
;; The types it uses of the files before it.
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-print) (include check-env))
(import check-print-parts k-same-type? k-shape-bit k-run-shape)

;; The shapes, by number in `check.rs`'s `SHAPES` order (`k-run-shape`,
;; `check-print-parts.fx`): a mask, bit `k` shape `k`'s, or -1 if they are
;; not known.
(define k-shape-count int 17)
(define k-shape-nil int 5)
(define k-shape-pair int 6)
;; The standard predicate that tests for shape `k`.
(define k-shape-predicate (->* (int) string)
  (lambda (k)
    (case k
      ((0) "int?") ((1) "f64?") ((2) "f32?") ((3) "char?") ((4) "bool?") ((5) "null?")
      ((6) "pair?") ((7) "string?") ((8) "symbol?") ((9) "procedure?") ((10) "array?")
      ((11) "ref?") ((12) "sum?") ((13) "product?") ((14) "vector?") ((15) "bytevector?")
      (else "keyword?"))))
(define k-one-id (->* (int) k-ids)
  (lambda (m) (the k-ids (cons m nil))))
(define k-ids-append (->* (k-ids k-ids) k-ids)
  (lambda (xs ys) (if (null? xs) ys (the k-ids (cons (car xs) (k-ids-append (cdr xs) ys))))))
(define k-shape-known? (->* (int) bool)
  (lambda (t) (>= (k-run-shape t) 0)))
;; Whether two masks share a shape; whether all of `s`'s are `u`'s.
(define k-shapes-meet? (->* (int int) bool)
  (lambda (s u) (not (= (bitwise-and s u) 0))))
(define k-shapes-within? (->* (int int) bool)
  (lambda (s u) (= (bitwise-and s u) s)))
;; Whether `t` and `u` have known shapes, none of them shared.
(define k-shapes-miss? (->* (int int) bool)
  (lambda (t u)
    (let ((s (k-run-shape t)) (v (k-run-shape u)))
      (and (>= s 0) (>= v 0) (not (k-shapes-meet? s v))))))
;; Whether `t` and `u` have the same known shapes.
(define k-same-shape? (->* (int int) bool)
  (lambda (t u)
    (let ((s (k-run-shape t))) (and (>= s 0) (= s (k-run-shape u))))))

;; Those of `ys` with `x`'s shapes, known (an `anyof`'s members may share
;; one; `k-greatest-of` chooses).
(define k-same-shape-in (->* (int k-ids) k-ids)
  (lambda (x ys)
    (cond ((null? ys) nil)
          ((k-same-shape? (car ys) x) (the k-ids (cons (car ys) (k-same-shape-in x (cdr ys)))))
          (else (k-same-shape-in x (cdr ys))))))
(define k-holding-in (->* (int k-ids) k-ids)
  (lambda (s ys)
    (cond ((null? ys) nil)
          ((k-shapes-within? s (k-run-shape (car ys)))
           (the k-ids (cons (car ys) (k-holding-in s (cdr ys)))))
          (else (k-holding-in s (cdr ys))))))
;; Those of `ys` whose shapes hold `x`'s, known and some.
(define k-member-holding (->* (int k-ids) k-ids)
  (lambda (x ys)
    (let ((s (k-run-shape x)))
      (if (<= s 0) nil (k-holding-in s ys)))))

;; Whether `t` is `false`, or a union with it.
(define k-false-member? (->* (k-ids) bool)
  (lambda (ms)
    (and (not (null? ms))
         (or (tagcase (k-get (car ms)) (ty-false () #t) (else y #f)) (k-false-member? (cdr ms))))))
(define k-false-expected? (->* (int) bool)
  (lambda (t)
    (tagcase (k-get t) (ty-false () #t) (ty-union (ms) (k-false-member? ms)) (else y #f))))

;; `ms`, resolved, a union among them its members.
(define k-union-flat (->* (k-ids) k-ids)
  (lambda (ms)
    (if (null? ms)
        nil
        (let ((m (k-resolve (car ms))) (rest (k-union-flat (cdr ms))))
          (tagcase (k-get m)
            (ty-union (xs) (k-ids-append (k-union-flat xs) rest))
            (else y (the k-ids (cons m rest))))))))
(define k-count-pairs (->* (k-ids) int)
  (lambda (ms)
    (if (null? ms)
        0
        (+ (tagcase (k-get (car ms)) (ty-pair (a b r nl) 1) (else y 0)) (k-count-pairs (cdr ms))))))
(define k-has-nil? (->* (k-ids) bool)
  (lambda (ms)
    (and (not (null? ms))
         (or (tagcase (k-get (car ms)) (ty-nil () #t) (else y #f)) (k-has-nil? (cdr ms))))))
;; `ms` with its first `nil` gone and its pair one that may be `nil`.
(define k-merge-nil (->* (k-ids bool) k-ids)
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
(define k-union-merged (->* (k-ids) k-ids)
  (lambda (flat)
    (if (and (k-has-nil? flat) (= (k-count-pairs flat) 1)) (k-merge-nil flat #f) flat)))
(define k-union-build (->* (k-ids) int)
  (lambda (ms)
    (cond ((null? ms) k-void)
          ((null? (cdr ms)) (car ms))
          (else (k-ty-new (ty-union ms))))))
;; The first member whose shape is not known, or -1.
(define k-unknown-member (->* (k-ids) int)
  (lambda (ms)
    (cond ((null? ms) -1)
          ((k-shape-known? (car ms)) (k-unknown-member (cdr ms)))
          (else (car ms)))))
;; `m`'s tags, if it is a sum, as a list of one.
(define k-sum-parts-of (->* (int) (listof k-parts acyclic))
  (lambda (m) (tagcase (k-get (k-resolve m)) (ty-sum (ps) (list ps)) (else y nil))))
(define k-both-sums? (->* (int int) bool)
  (lambda (m o) (and (not (null? (k-sum-parts-of m))) (not (null? (k-sum-parts-of o))))))
;; A tag of `a`'s that `b` has too, as a list of one.
(define k-shared-tag (->* (k-parts k-parts) (listof symbol acyclic))
  (lambda (a b)
    (cond ((null? a) nil)
          ((>= (k-part-find b (extract (car a) 1)) 0) (list (extract (car a) 1)))
          (else (k-shared-tag (cdr a) b)))))
(define k-sums-share (->* (int int) (listof symbol acyclic))
  (lambda (m o) (k-shared-tag (car (k-sum-parts-of m)) (car (k-sum-parts-of o)))))
;; A member after the first of `ms` that a run-time test does not tell from
;; `m`, or -1: one sharing a shape, but for two sums with no tag in common.
(define k-overlap-with (->* (int k-ids) int)
  (lambda (m ms)
    (cond ((null? ms) -1)
          ((k-both-sums? m (car ms))
           (if (null? (k-sums-share m (car ms))) (k-overlap-with m (cdr ms)) (car ms)))
          ((k-shapes-meet? (k-run-shape m) (k-run-shape (car ms))) (car ms))
          (else (k-overlap-with m (cdr ms))))))
(define k-union-overlap (->* (k-ids int int) unit)
  (lambda (ms start end)
    (if (null? ms)
        #u
        (let* ((m (car ms)) (o (k-overlap-with m (cdr ms))))
          (cond ((< o 0) (k-union-overlap (cdr ms) start end))
                ((k-both-sums? m o)
                 (k-fail (k-cat5 "a `oneof`'s sums must have no tag in common: a " (k-show-ty m)
                                 " and a " (k-show-ty o)
                                 (k-cat3 " both have `" (symbol->string (car (k-sums-share m o)))
                                         "`"))
                         start end))
                (else
                 (k-fail (k-cat5 "a `oneof`'s members must be told apart at run time: a "
                                 (k-show-ty m) " and a " (k-show-ty o) " cannot be")
                         start end)))))))
(define k-count-sums (->* (k-ids) int)
  (lambda (ms)
    (if (null? ms) 0 (+ (if (null? (k-sum-parts-of (car ms))) 0 1) (k-count-sums (cdr ms))))))
;; The tags of `ms`'s sums, in order.
(define k-all-sum-parts (->* (k-ids) k-parts)
  (lambda (ms)
    (if (null? ms)
        nil
        (let ((p (k-sum-parts-of (car ms))) (rest (k-all-sum-parts (cdr ms))))
          (if (null? p) rest (append (car p) rest))))))
;; `ms` with its first sum `sum`, its other sums gone.
(define k-sums-replaced (->* (k-ids int bool) k-ids)
  (lambda (ms sum done)
    (cond ((null? ms) nil)
          ((null? (k-sum-parts-of (car ms)))
           (the k-ids (cons (car ms) (k-sums-replaced (cdr ms) sum done))))
          (done (k-sums-replaced (cdr ms) sum done))
          (else (the k-ids (cons sum (k-sums-replaced (cdr ms) sum #t)))))))
;; `ms`'s sums, whose tags `k-union-overlap` found apart, made one: the
;; same values, which `tagcase` takes apart. As Rust's `union_sums_merged`.
(define k-union-sums-merged (->* (k-ids) k-ids)
  (lambda (ms)
    (if (< (k-count-sums ms) 2)
        ms
        (k-sums-replaced ms (k-ty-new (ty-sum (k-all-sum-parts ms))) #f))))
(define k-pendings-append
  (->* (k-pendings k-pending) k-pendings)
  (lambda (ps p)
    (if (null? ps)
        (the k-pendings (cons p nil))
        (the k-pendings (cons (car ps) (k-pendings-append (cdr ps) p))))))
(define k-former (->* (bool) string) (lambda (any) (if any "anyof" "oneof")))
(define k-union-known (->* (k-ids int int bool) unit)
  (lambda (ms start end any)
    (let ((unknown (k-unknown-member ms)))
      (if (>= unknown 0)
          (k-fail (k-cat5 "a " (k-show-ty unknown) " cannot be in a `" (k-former any)
                          "`: its shape at run time is not known")
                  start end)
          #u))))
;; Whether a member is not yet known: a recursive type's own name, read
;; before its definition is.
(define k-open-member? (->* (int) bool)
  (lambda (m) (tagcase (k-get m) (ty-link (x) (null? x)) (else y #f))))
(define k-any-open? (->* (k-ids) bool)
  (lambda (ms) (and (not (null? ms)) (or (k-open-member? (car ms)) (k-any-open? (cdr ms))))))
;; The union of `members`, `(oneof …)`, normalized: unions in it
;; flattened, `nil` and a pair that is not `nil` made the pair that may be,
;; sums made one, and one member itself. Each member must have a known
;; shape, and no two the same but sums with no tag in common; one not yet
;; known, the union checked once it is (`k-check-pending-unions`).
(define k-union-of (->* (k-ids int int) int)
  (lambda (members start end) (k-union-formed members start end #f)))
;; The true union of `members`, `(anyof …)` (`logical-types.md` §8.5, U2),
;; normalized as `k-union-of` does, but members may overlap: `void` and a
;; member the same as one before it dropped, and sums made one with a tag
;; in several the union of its payloads. Only a member that may be written
;; must still be told apart from every other. As Rust's `anyof_of`.
(define k-anyof-of (->* (k-ids int int) int)
  (lambda (members start end) (k-union-formed members start end #t)))
(define k-union-formed (->* (k-ids int int bool) int)
  (lambda (members start end any)
    (let* ((flat0 (k-union-flat members))
           (flat (if any (k-anyof-trimmed flat0 nil) flat0))
           (pending (k-any-open? flat)))
      (begin
        (if pending #u (k-union-known flat start end any))
        (let ((merged (k-union-merged flat)))
          (cond (pending
                 (let ((u (k-ty-new (ty-union merged))))
                   (begin (set k-pending-unions
                               (k-pendings-append (get k-pending-unions)
                                                  (product (1 u) (2 start) (3 end) (4 any))))
                          u)))
                ;; Its sums kept as written: their head form made where one
                ;; sum is needed (`k-sum-head`), which must be one, checked now.
                (any (begin (k-sums-joined-of merged start end)
                            (k-anyof-written-apart merged start end)
                            (k-union-build merged)))
                (else (begin (k-union-overlap merged start end)
                             (k-union-build (k-union-sums-merged merged))))))))))
;; `ms` without `void`, and without a member the same as one before it
;; (`kept`, reversed).
(define k-anyof-trimmed (->* (k-ids k-ids) k-ids)
  (lambda (ms kept)
    (cond ((null? ms) (k-reverse-ids kept nil))
          ((or (tagcase (k-get (car ms)) (ty-void () #t) (else y #f)) (k-same-in? (car ms) kept))
           (k-anyof-trimmed (cdr ms) kept))
          (else (k-anyof-trimmed (cdr ms) (the k-ids (cons (car ms) kept)))))))
(define k-same-in? (->* (int k-ids) bool)
  (lambda (m ks) (and (not (null? ks)) (or (k-same-type? (car ks) m) (k-same-in? m (cdr ks))))))
;; `sums` made one: each tag once, its payload the `anyof` of its payloads
;; in them (the same values: a sum's representation names its tag, not its
;; type's tags). An `anyof`'s sums are kept as written; this is their head
;; form (`logical-types.md` §8.8), made where one sum is needed. As Rust's
;; `sums_joined`.
(define k-sums-joined (->* (k-ids int int) int)
  (lambda (sums start end)
    (let ((all (k-all-sum-parts sums))) (k-ty-new (ty-sum (k-tags-joined all all nil start end))))))
;; The sums of `ms`, if two or more, made one; -1 if not.
(define k-sums-joined-of (->* (k-ids int int) int)
  (lambda (ms start end)
    (let ((sums (k-sums-among ms)))
      (if (or (null? sums) (null? (cdr sums))) -1 (k-sums-joined sums start end)))))
(define k-sums-among (->* (k-ids) k-ids)
  (lambda (ms)
    (cond ((null? ms) nil)
          ((null? (k-sum-parts-of (car ms))) (k-sums-among (cdr ms)))
          (else (the k-ids (cons (car ms) (k-sums-among (cdr ms))))))))
;; The sums of `ms`, if two or more, made one as `k-sums-joined` makes them,
;; but each payload of several the union of those not the same, unchecked:
;; what subtyping compares with, which may not fail; -1 if not. As Rust's
;; `sums_joined_raw`.
(define k-sums-joined-raw (->* (k-ids) int)
  (lambda (ms)
    (let ((sums (k-sums-among ms)))
      (if (or (null? sums) (null? (cdr sums)))
          -1
          (let ((all (k-all-sum-parts sums))) (k-ty-new (ty-sum (k-tags-raw all all nil))))))))
(define k-tags-raw (->* (k-parts k-parts (listof symbol acyclic)) k-parts)
  (lambda (ps all seen)
    (cond ((null? ps) nil)
          ((k-symbol-in? (extract (car ps) 1) seen) (k-tags-raw (cdr ps) all seen))
          (else
           (let* ((l (extract (car ps) 1)) (ts (k-payloads-of l all))
                  (t (if (null? (cdr ts)) (car ts) (k-union-build (k-anyof-trimmed ts nil)))))
             (the k-parts
                  (cons (product (1 l) (2 t))
                        (k-tags-raw (cdr ps) all (the (listof symbol acyclic) (cons l seen))))))))))
;; Of a union whose members are all sums, its head form: the one sum they
;; are together (`tagcase` takes that apart); else `t`. As Rust's
;; `sum_head`.
(define k-sum-head (->* (int) int)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-union (ms)
        (if (= (k-length (k-sums-among ms)) (k-length ms)) (k-sums-joined-or ms t) t))
      (else y t))))
;; `sums` made one, or `t` if they cannot be.
(define k-sums-joined-or (->* (k-ids int) int)
  (lambda (sums t)
    (let ((r (let* ((k-at-now (k-now))
                    (k-caught (prompt k-tag (k-done (k-te (k-sums-joined sums 0 0) nil))
                                (lambda (r) r))))
               (k-now-back k-at-now k-caught))))
      (tagcase r (k-done (te) (extract te 1)) (else y t)))))
;; Each tag of `ps` once, at its first place, its payload the `anyof` of
;; every payload `ps` has for it (`all`, the whole; `seen`, tags placed).
(define k-tags-joined (->* (k-parts k-parts (listof symbol acyclic) int int) k-parts)
  (lambda (ps all seen start end)
    (cond ((null? ps) nil)
          ((k-symbol-in? (extract (car ps) 1) seen) (k-tags-joined (cdr ps) all seen start end))
          (else
           (let* ((l (extract (car ps) 1)) (ts (k-payloads-of l all))
                  (t (if (null? (cdr ts)) (car ts) (k-anyof-of ts start end))))
             (the k-parts
                  (cons (product (1 l) (2 t))
                        (k-tags-joined (cdr ps) all (the (listof symbol acyclic) (cons l seen))
                                       start end))))))))
(define k-symbol-in? (->* (symbol (listof symbol acyclic)) bool)
  (lambda (l ls) (and (not (null? ls)) (or (symbol=? (car ls) l) (k-symbol-in? l (cdr ls))))))
(define k-payloads-of (->* (symbol k-parts) k-ids)
  (lambda (l ps)
    (cond ((null? ps) nil)
          ((symbol=? (extract (car ps) 1) l)
           (the k-ids (cons (extract (car ps) 2) (k-payloads-of l (cdr ps)))))
          (else (k-payloads-of l (cdr ps))))))
;; Whether a value of `t` may be written: a cell, an array, a bloblet, or a
;; pair or list not frozen.
(define k-may-be-written? (->* (int) bool)
  (lambda (t)
    (letrec ((thawed? (subr pure (k-region) bool)
               (lambda (r) (tagcase r (r-frozen (p f) #f) (else y #t)))))
      (tagcase (k-get (k-resolve t))
        (ty-ref (a r) #t) (ty-array (a z r) #t) (ty-bloblet (fs z r) #t)
        (ty-icell (a r) #t) (ty-markkey (a r) #t) (ty-place (r) #t)
        (ty-pair (a b r nl) (thawed? r))
        (ty-nlist (e z r) (thawed? r))
        (else y #f)))))
;; An `anyof`'s members that may be written each told apart from every
;; other at run time (`logical-types.md` §9.2, question 14: a union of
;; cells, refused until a program needs it).
(define k-anyof-written-apart (->* (k-ids int int) unit)
  (lambda (ms start end)
    (if (null? ms)
        #u
        (let ((o (k-written-overlap (car ms) (cdr ms))))
          (if (< o 0)
              (k-anyof-written-apart (cdr ms) start end)
              (k-fail (k-cat5 (string-append "an `anyof`'s members that may be written must be "
                                             "told apart at run time: a ")
                              (k-show-ty (car ms)) " and a " (k-show-ty o) " cannot be")
                      start end))))))
(define k-shape-or-none (->* (int) int)
  (lambda (t) (let ((s (k-run-shape t))) (if (< s 0) 0 s))))
(define k-written-overlap (->* (int k-ids) int)
  (lambda (m ms)
    (cond ((null? ms) -1)
          ((and (or (k-may-be-written? m) (k-may-be-written? (car ms)))
                (k-shapes-meet? (k-shape-or-none m) (k-shape-or-none (car ms))))
           (car ms))
          (else (k-written-overlap m (cdr ms))))))
;; The unions read before what they name was, each whose members are all
;; known now checked as `k-union-of` would have.
(define k-check-pending-unions (->* () unit)
  (lambda () (set k-pending-unions (k-check-pendings (get k-pending-unions)))))
(define k-check-pendings (->* (k-pendings) k-pendings)
  (lambda (ps)
    (if (null? ps)
        nil
        (let* ((p (car ps))
               (ms (tagcase (k-get (extract p 1)) (ty-union (ms) ms) (else y (the k-ids nil)))))
          (if (k-any-open? ms)
              (the k-pendings (cons p (k-check-pendings (cdr ps))))
              (begin (k-union-known ms (extract p 2) (extract p 3) (extract p 4))
                     (if (extract p 4)
                         (begin (k-anyof-written-apart ms (extract p 2) (extract p 3))
                                (k-sums-joined-of ms (extract p 2) (extract p 3))
                                #u)
                         (begin (k-union-overlap ms (extract p 2) (extract p 3))
                                ;; Made already, its sums cannot be made one now.
                                (if (> (k-count-sums ms) 1)
                                    (k-fail (string-append
                                             "a `oneof` of sums with a member not yet "
                                             "defined: write the sums as one `sumof`")
                                            (extract p 2) (extract p 3))
                                    #u)))
                     (k-check-pendings (cdr ps))))))))

;; What `k-split-below` (`check-subtype.fx`) splits, and how: a type below
;; a union that no member takes whole, at a field (`logical-types.md` §8.8).
;; Of union members `ns`, those that may hold an `a`: of its shapes, or
;; either's not known.
(define k-shaped-like (->* (int k-ids) k-ids)
  (lambda (a ns)
    (let ((s (k-run-shape a)))
      (cond ((null? ns) nil)
            ((let ((n (k-run-shape (car ns))))
               (or (< s 0) (< n 0) (not (= (bitwise-and s n) 0))))
             (the k-ids (cons (car ns) (k-shaped-like a (cdr ns)))))
            (else (k-shaped-like a (cdr ns)))))))
;; The fields of `a` that `k-split-below` may split, in order, as a list of
;; one: a product's or a sum's, a frozen pair's head and tail.
(define k-split-fields (->* (int) k-idss)
  (lambda (a)
    (tagcase (k-get (k-resolve a))
      (ty-product (ps) (list (k-part-tys ps)))
      (ty-sum (ps) (list (k-part-tys ps)))
      (ty-pair (x y r nl)
        (if (and (not nl) (tagcase r (r-frozen (p f) #t) (else z #f)))
            (list (the k-ids (cons x (k-one-ty y))))
            nil))
      (else z nil))))
(define k-one-ty (->* (int) k-ids) (lambda (t) (the k-ids (cons t nil))))
(define k-part-tys (->* (k-parts) k-ids)
  (lambda (ps) (if (null? ps) nil (the k-ids (cons (extract (car ps) 2) (k-part-tys (cdr ps)))))))
;; The fields of each of `ns` of `a`'s kind matching `a`'s: of a product of
;; the same labels, of a sum with each of `a`'s tags, of a pair.
(define k-kin-fields (->* (int k-ids) k-idss)
  (lambda (a ns)
    (if (null? ns)
        nil
        (let ((k (k-kin-of (k-get (k-resolve a)) (k-get (k-resolve (car ns)))))
              (rest (k-kin-fields a (cdr ns))))
          (if (null? k) rest (the k-idss (cons (car k) rest)))))))
(define k-kin-of (->* (k-ty k-ty) k-idss)
  (lambda (ta tn)
    (tagcase ta
      (ty-product (ps)
        (tagcase tn
          (ty-product (qs) (if (k-same-labels-in-order? ps qs) (list (k-part-tys qs)) nil))
          (else z nil)))
      (ty-sum (ps)
        (tagcase tn (ty-sum (qs) (k-tags-payloads ps qs)) (else z nil)))
      (ty-pair (x y r nl)
        (tagcase tn (ty-pair (u v s m) (list (the k-ids (cons u (k-one-ty v))))) (else z nil)))
      (else z nil))))
(define k-same-labels-in-order? (->* (k-parts k-parts) bool)
  (lambda (ps qs)
    (cond ((null? ps) (null? qs))
          ((null? qs) #f)
          (else (and (symbol=? (extract (car ps) 1) (extract (car qs) 1))
                     (k-same-labels-in-order? (cdr ps) (cdr qs)))))))
;; `qs`'s payloads for each of `ps`'s tags, as a list of one; none if one
;; is missing.
(define k-tags-payloads (->* (k-parts k-parts) k-idss)
  (lambda (ps qs)
    (if (null? ps)
        (list (the k-ids nil))
        (let ((t (k-part-find qs (extract (car ps) 1))) (rest (k-tags-payloads (cdr ps) qs)))
          (if (or (< t 0) (null? rest)) nil (list (the k-ids (cons t (car rest)))))))))
(define k-union-ty? (->* (int) bool)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-union (ms) #t) (else z #f))))
(define k-members-of (->* (int) k-ids)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-union (ms) ms) (else z (k-one-ty t)))))
;; Whether every field list of `kin` has the same type at `i`.
(define k-kin-agree? (->* (k-idss int) bool)
  (lambda (kin i)
    (let ((first (k-nth-id (car kin) i)))
      (letrec ((all? (->* (k-idss) bool)
                 (lambda (ks)
                   (or (null? ks)
                       (and (k-same-type? (k-nth-id (car ks) i) first) (all? (cdr ks)))))))
        (all? (cdr kin))))))
(define k-nth-id (->* (k-ids int) int)
  (lambda (xs i) (if (= i 0) (car xs) (k-nth-id (cdr xs) (- i 1)))))
;; `a` with its `i`th field (`k-split-fields`) of type `m`.
(define k-with-field (->* (int int int) int)
  (lambda (a i m)
    (tagcase (k-get (k-resolve a))
      (ty-product (ps) (k-ty-new (ty-product (k-part-at ps i m))))
      (ty-sum (ps) (k-ty-new (ty-sum (k-part-at ps i m))))
      (ty-pair (x y r nl)
        (k-ty-new (if (= i 0) (ty-pair m y r nl) (ty-pair x m r nl))))
      (else z a))))
(define k-part-at (->* (k-parts int int) k-parts)
  (lambda (ps i m)
    (if (= i 0)
        (the k-parts (cons (product (1 (extract (car ps) 1)) (2 m)) (cdr ps)))
        (the k-parts (cons (car ps) (k-part-at (cdr ps) (- i 1) m))))))
;; A pair that may be `nil`, tested for either, is two members here.
(define k-member-parts (->* (int int) k-ids)
  (lambda (m k)
    (tagcase (k-get m)
      (ty-pair (a b r nl)
        (if (and nl (or (= k 5) (= k 6)))
            (the k-ids (cons (k-ty-new (ty-nil)) (k-one-id (k-ty-new (ty-pair a b r #f)))))
            (k-one-id m)))
      (else y (k-one-id m)))))
;; Members `ps` to the side where shape `k` is found, or not, or both.
(define k-sort-parts (->* (k-ids int k-sides) k-sides)
  (lambda (ps k acc)
    (if (null? ps)
        acc
        (let* ((p (car ps)) (s (k-run-shape p)) (mask (k-shape-bit k))
               (in (k-shapes-within? s mask)) (out (not (k-shapes-meet? s mask)))
               (inside (if out (car acc) (the k-ids (cons p (car acc)))))
               (outside (if in (cdr acc) (the k-ids (cons p (cdr acc))))))
          (k-sort-parts (cdr ps) k (cons inside outside))))))
(define k-reverse-ids (->* (k-ids k-ids) k-ids)
  (lambda (xs acc) (if (null? xs) acc (k-reverse-ids (cdr xs) (the k-ids (cons (car xs) acc))))))
(define k-split-into (->* (k-ids int k-sides) k-sides)
  (lambda (ms k acc)
    (if (null? ms)
        acc
        (k-split-into (cdr ms) k (k-sort-parts (k-member-parts (k-resolve (car ms)) k) k acc)))))
(define k-split-members (->* (k-ids int) k-sides)
  (lambda (ms k)
    (let ((sides (k-split-into ms k (cons nil nil))))
      (cons (k-reverse-ids (car sides) nil) (k-reverse-ids (cdr sides) nil)))))
(define k-narrowed-by (->* (int int) k-split)
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
        (else y none))))))))
