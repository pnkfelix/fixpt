;;; The checker, in FX-26: `allof`, one procedure with each member's type
;;; (`docs/research/logical-types.md` §8.5, U1), the Rust checker's
;;; `check_allof_lambda`, `synth_allof_call` and `meet`, rule for rule and
;;; in its words. A `lambda` is checked against each member: a `tagcase`
;;; arm a member's type rules out is skipped there (`k-arm-dead?`), and is
;;; an error only if every member skips it; what the compilers read of its
;;; body must be found alike under every member, since it is compiled once.
;;; A call takes every member it fits, its result the meet of theirs. And
;;; a call taking a union argument apart member by member (rule 5, U3), the
;;; Rust checker's `synth_app_split`, by the same means.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-subtype-types (load-module "fx26:check-subtype-types.fx"))
       (check-synth-types (load-module "fx26:check-synth-types.fx"))
       (check-expect-types (load-module "fx26:check-expect-types.fx"))
       (check-errors-types (load-module "fx26:check-errors-types.fx"))
       (check-allof-types (load-module "fx26:check-allof-types.fx"))
       (check-unions-types (load-module "fx26:check-unions-types.fx"))
       (check-calls-types (load-module "fx26:check-calls-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-env (select check-env-types check-env-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (check-print (select check-print-types check-print-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-subtype (select check-subtype-types check-subtype-sig))
           (check-synth (select check-synth-types check-synth-sig))
           (check-expect (select check-expect-types check-expect-sig))
           (check-errors (select check-errors-types check-errors-sig))
           (check-unions (select check-unions-types check-unions-sig))
           (check-calls (select check-calls-types check-calls-sig)))
    (module

;; The types it uses of the files before it.
(hide (include check-types-types) (include check-env-types) (include check-allof-types))
(import check-synth-types (type k-done k-nars))
(import check-subtype-types (type k-checking))
(import check-resolve-types (type k-typed-params))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-env) (include check-print) (include check-print-parts)
      (include check-effects) (include check-subtype))
(import check-resolve k-start k-end k-kth k-reading k-keys-onto k-at-of k-regions-in
        k-has-region-in?)
(import check-synth k-note-call k-te-masked)
(import check-calls k-callee-name)
(import check-expect k-rewriting k-expect k-conversion)
(import check-errors k-argument-error k-fail-no-part)
(import check-unions k-anyof-of)

;;; ------------------------------------------------------------ the type

;; `t`'s members, if it is an `allof`.
(define k-allof-members-of (->* (int) k-ids)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-allof (ms) ms) (else y nil))))
(define k-allof-type? (->* (int) bool)
  (lambda (t) (not (null? (k-allof-members-of t)))))

;;; ------------------------------------------------------------ dead arms

;; The arm for `tag`, whose body is `body`, of a `tagcase` whose subject is
;; a `st` without it: skipped (#t) while a `lambda` is checked against a
;; member of an `allof`, and noted (`k-dead-arms`), with the numbers of
;; what is in it (`k-keys-onto`); else an error.
(define k-arm-dead? (->* (int symbol kx) bool)
  (lambda (st tag body)
    (let
     ((fs (get k-dead-arms)) (a (k-start body)) (b (k-end body)) (k (k-kth body))
                             (kr (k-reading body)))
      (if (null? fs)
          (begin (k-fail-no-part st " has no tag " tag a b) #f)
          (let* ((f (car fs)) (arms (k-dead-counted (extract f 1) st tag a b k kr))
                 (now (k-keys-onto body (extract f 2))))
            (begin (set k-dead-arms (cons (product (1 arms) (2 now) (3 (extract f 3))
                                                   (4 (extract f 4)) (5 (extract f 5)))
                                          (cdr fs)))
                   #t))))))
;; `arms` with the one whose body is `k` (at `a`..`b`) counted once more,
;; its error's type `st`.
(define k-dead-counted (->* ((listof k-dead-arm acyclic) int symbol int int int int)
                            (listof k-dead-arm acyclic))
  (lambda (arms st tag a b k kr)
    (cond ((null? arms) (list (product (1 a) (2 b) (3 1) (4 st) (5 tag) (6 k))))
          ((= (extract (car arms) 6) k)
           (cons (product (1 a) (2 b) (3 (+ 1 (extract (car arms) 3))) (4 st) (5 tag) (6 k))
                 (cdr arms)))
          (else (cons (car arms) (k-dead-counted (cdr arms) st tag a b k kr))))))
;; Of `arms`, the first by place skipped `n` times, or `best`, as a list.
(define k-dead-in-all (->* ((listof k-dead-arm acyclic) int (listof k-dead-arm acyclic))
                           (listof k-dead-arm acyclic))
  (lambda (arms n best)
    (cond ((null? arms) best)
          ((and (= (extract (car arms) 3) n)
                (or (null? best)
                    (< (extract (car arms) 1) (extract (car best) 1))
                    (and (= (extract (car arms) 1) (extract (car best) 1))
                         (< (extract (car arms) 2) (extract (car best) 2)))))
           (k-dead-in-all (cdr arms) n (list (car arms))))
          (else (k-dead-in-all (cdr arms) n best)))))

;; Whether an `if`'s branch `x` is skipped: checked against a member of an
;; `allof`, the test narrows a variable to `void` there (`ns`, its
;; narrowing), so it cannot run (rule 2, as a `tagcase`'s arm), unless
;; every member but this last one skipped it; noted. Rust's `dead_branch`.
(define k-dead-branch? (->* (k-nars kx) bool)
  (lambda (ns x)
    (let ((fs (get k-dead-arms)) (key (k-at-of x)))
      (if (or (null? fs) (not (k-nars-void? ns)))
          #f
          (let* ((f (car fs)) (at (extract f 4))
                 (skipped (k-branch-skipped (extract f 5) key)))
            (if (and (= (+ at 1) (extract f 3)) (k-all-below? skipped at))
                #f
                (begin
                  (set k-dead-arms
                       (cons (product (1 (extract f 1))
                                      (2 (k-keys-onto x (extract f 2)))
                                      (3 (extract f 3)) (4 at)
                                      (5 (k-branch-noted (extract f 5) key at)))
                             (cdr fs)))
                  #t)))))))
(define k-nars-void? (->* (k-nars) bool)
  (lambda (ns)
    (and (not (null? ns))
         (or (= (k-resolve (extract (car ns) 5)) k-void) (k-nars-void? (cdr ns))))))
;; The members that skipped the branch `key`.
(define k-branch-skipped (->* ((listof k-dead-branch acyclic) k-at) (listof int acyclic))
  (lambda (bs key)
    (cond ((null? bs) nil)
          ((k-at=? (extract (car bs) 1) key) (extract (car bs) 2))
          (else (k-branch-skipped (cdr bs) key)))))
(define k-branch-noted (->* ((listof k-dead-branch acyclic) k-at int)
                            (listof k-dead-branch acyclic))
  (lambda (bs key at)
    (cond ((null? bs) (list (product (1 key) (2 (list at)))))
          ((k-at=? (extract (car bs) 1) key)
           (cons (product (1 key) (2 (cons at (extract (car bs) 2)))) (cdr bs)))
          (else (cons (car bs) (k-branch-noted (cdr bs) key at))))))
;; Whether every member before `at` is among `ms`.
(define k-all-below? (->* ((listof int acyclic) int) bool)
  (lambda (ms at)
    (or (= at 0) (and (k-int-in? ms (- at 1)) (k-all-below? ms (- at 1))))))
(define k-int-in? (->* ((listof int acyclic) int) bool)
  (lambda (ms i) (and (not (null? ms)) (or (= (car ms) i) (k-int-in? (cdr ms) i)))))
;; An `if`'s branch `x`, found or checked against `expected`, or skipped
;; (`k-dead-branch?`), of type `void`.
(define k-branch-synth (->* (kx k-nars k-synth-fn) k-te)
  (lambda (x ns synth) (if (k-dead-branch? ns x) (k-te k-void nil) (synth x))))
(define k-branch-check (->* (kx int k-nars k-check-fn) k-eff)
  (lambda (x expected ns check) (if (k-dead-branch? ns x) nil (check x expected))))

;;; ------------------------------------------------------------ facts

;; What the compilers read of the expressions checked, as it is now: its
;; facts, `with`s' values and reshapes, and the reshapes' bases.
(define-type k-code (productof (1 k-facts) (2 k-with-list) (3 k-reshape-list)
                               (4 k-reshape-base-list)))
(define k-code-now (->* () k-code)
  (lambda ()
    (product (1 (get k-extracts)) (2 (get k-with-vals)) (3 (get k-reshapes))
             (4 (get k-reshape-bases)))))
(define k-code-put-back (->* (k-code) unit)
  (lambda (c)
    (begin (set k-extracts (extract c 1)) (set k-with-vals (extract c 2))
           (set k-reshapes (extract c 3)) (set k-reshape-bases (extract c 4)))))
;; The first `n` of `l`: what was noted since, the rest being as it was.
(define k-first-facts (->* (k-facts int) k-facts)
  (lambda (l n) (if (= n 0) nil (cons (car l) (k-first-facts (cdr l) (- n 1))))))
(define k-first-withs (->* (k-with-list int) k-with-list)
  (lambda (l n) (if (= n 0) nil (cons (car l) (k-first-withs (cdr l) (- n 1))))))
(define k-first-reshapes (->* (k-reshape-list int) k-reshape-list)
  (lambda (l n) (if (= n 0) nil (cons (car l) (k-first-reshapes (cdr l) (- n 1))))))
;; One member's: what it noted, and where it checked nothing.
(define-type k-found (productof (1 k-facts) (2 k-with-list) (3 k-reshape-list) (4 k-spans)))
(define k-found-since (->* (k-code k-spans) k-found)
  (lambda (c skipped)
    (product (1 (k-first-facts (get k-extracts)
                               (- (k-length (get k-extracts)) (k-length (extract c 1)))))
             (2 (k-first-withs (get k-with-vals)
                               (- (k-length (get k-with-vals)) (k-length (extract c 2)))))
             (3 (k-first-reshapes (get k-reshapes)
                                  (- (k-length (get k-reshapes)) (k-length (extract c 3)))))
             (4 skipped))))

(define k-at=? (->* (k-at k-at) bool)
  (lambda (x y) (and (= (extract x 3) (extract y 3)) (= (extract x 4) (extract y 4)))))
;; Whether `at` is one of `keys`, the keys of what is in each skipped
;; (`k-keys-onto`): by the trees' structure, not by where it is written, nor
;; by its keys' values, which a mode makes digests.
(define k-skipped? (->* (k-at k-spans) bool)
  (lambda (at keys)
    (and (not (null? keys))
         (or (and (= (extract at 3) (extract (car keys) 1))
                  (= (extract at 4) (extract (car keys) 2)))
             (k-skipped? at (cdr keys))))))
(define k-datum=? (->* (k-datum k-datum) bool)
  (lambda (d e)
    (tagcase d
      (datum-field (i) (tagcase e (datum-field (j) (= i j)) (else z #f)))
      (datum-blobref-field (i) (tagcase e (datum-blobref-field (j) (= i j)) (else z #f)))
      (datum-layout (i) (tagcase e (datum-layout (j) (= i j)) (else z #f)))
      (datum-array (n s) (tagcase e (datum-array (m t) (and (= n m) (= s t))) (else z #f)))
      (datum-fits (i) (tagcase e (datum-fits (j) (= i j)) (else z #f))))))
;; Whether `x` and `y` are the same fact; and whether they are of a kind.
(define k-noted=? (->* (k-noted k-noted) bool)
  (lambda (x y)
    (tagcase x
      (n-datum (d) (tagcase y (n-datum (e) (k-datum=? d e)) (else z #f)))
      (n-summary (s) (tagcase y (n-summary (t) (= s t)) (else z #f)))
      (n-conversion (k) (tagcase y (n-conversion (l) (= k l)) (else z #f)))
      (n-apply-shares () (tagcase y (n-apply-shares () #t) (else z #f)))
      (n-frozen-define () (tagcase y (n-frozen-define () #t) (else z #f)))
      (n-plain-fx () (tagcase y (n-plain-fx () #t) (else z #f)))
      (n-call (c) (tagcase y (n-call (d) (k-conv=? c d)) (else z #f)))
      (n-staged (f n r d) (tagcase y (n-staged (g m s e) (and (string=? f g) (string=? n m)))
                          (else z #f))))))
(define k-noted-kind (->* (k-noted) int)
  (lambda (x)
    (tagcase x
      (n-datum (d) 0) (n-summary (s) 1) (n-conversion (k) 2) (n-apply-shares () 3)
      (n-frozen-define () 4) (n-plain-fx () 5) (n-call (c) 6) (n-staged (f n r d) 7))))
;; Whether each of `xs` not skipped is in `ys` alike, of its place and kind;
;; a `stage`'s, which the Rust checker does not compare, aside.
(define k-facts-in? (->* (k-facts k-facts k-spans) bool)
  (lambda (xs ys skip)
    (or (null? xs)
        (and (or (k-skipped? (extract (car xs) 1) skip) (= (k-noted-kind (extract (car xs) 2)) 7)
                 (k-fact-among? (car xs) ys))
             (k-facts-in? (cdr xs) ys skip)))))
(define k-fact-among? (->* (k-fact k-facts) bool)
  (lambda (x ys)
    (and (not (null? ys))
         (if (and (k-at=? (extract x 1) (extract (car ys) 1))
                  (= (k-noted-kind (extract x 2)) (k-noted-kind (extract (car ys) 2))))
             (k-noted=? (extract x 2) (extract (car ys) 2))
             (k-fact-among? x (cdr ys))))))
(define k-names=? (->* (k-names k-names) bool)
  (lambda (x y)
    (if (null? x)
        (null? y)
        (and (not (null? y)) (symbol=? (car x) (car y)) (k-names=? (cdr x) (cdr y))))))
(define k-ints=? (->* (k-ids k-ids) bool)
  (lambda (x y)
    (if (null? x) (null? y) (and (not (null? y)) (= (car x) (car y)) (k-ints=? (cdr x) (cdr y))))))
(define k-withs-in? (->* (k-with-list k-with-list k-spans) bool)
  (lambda (xs ys skip)
    (or (null? xs)
        (and (or (k-skipped? (extract (car xs) 1) skip) (k-with-among? (car xs) ys))
             (k-withs-in? (cdr xs) ys skip)))))
(define k-with-among? (->* (k-with-noted k-with-list) bool)
  (lambda (x ys)
    (and (not (null? ys))
         (if (k-at=? (extract x 1) (extract (car ys) 1))
             (and (k-names=? (extract x 2) (extract (car ys) 2))
                  (k-ints=? (extract x 3) (extract (car ys) 3)))
             (k-with-among? x (cdr ys))))))
(define k-picks=? (->* (k-picks k-picks) bool)
  (lambda (x y)
    (if (null? x)
        (null? y)
        (and (not (null? y))
             (tagcase (car x)
               (pick-value (i) (tagcase (car y) (pick-value (j) (= i j)) (else z #f)))
               (pick-path (k i) (tagcase (car y) (pick-path (l j) (and (= k l) (= i j)))
                                  (else z #f))))
             (k-picks=? (cdr x) (cdr y))))))
(define k-reshapes-in? (->* (k-reshape-list k-reshape-list k-spans) bool)
  (lambda (xs ys skip)
    (or (null? xs)
        (and (or (k-skipped? (extract (car xs) 1) skip) (k-reshape-among? (car xs) ys))
             (k-reshapes-in? (cdr xs) ys skip)))))
(define k-reshape-among? (->* (k-reshaped k-reshape-list) bool)
  (lambda (x ys)
    (and (not (null? ys))
         (if (k-at=? (extract x 1) (extract (car ys) 1))
             (k-picks=? (extract x 2) (extract (car ys) 2))
             (k-reshape-among? x (cdr ys))))))
;; Whether two members found the same where both checked.
(define k-found-alike? (->* (k-found k-found) bool)
  (lambda (x y)
    (let ((skip (append (extract x 4) (extract y 4))))
      (and (k-facts-in? (extract x 1) (extract y 1) skip)
           (k-facts-in? (extract y 1) (extract x 1) skip)
           (k-withs-in? (extract x 2) (extract y 2) skip)
           (k-withs-in? (extract y 2) (extract x 2) skip)
           (k-reshapes-in? (extract x 3) (extract y 3) skip)
           (k-reshapes-in? (extract y 3) (extract x 3) skip)))))

;;; ------------------------------------------------------------ a lambda

;; `lambda` `x` checked against each member of `t`, an `allof`
;; (`logical-types.md` §8.5): its effect.
(define k-allof-lambda (->* (kx int k-check-fn) k-eff)
  (lambda (x t check)
    (let* ((n (k-length (k-allof-members-of t)))
           (pushed (set k-dead-arms (cons (product (1 nil) (2 nil) (3 n) (4 0) (5 nil))
                                          (get k-dead-arms))))
           (r (let* ((k-at-now (k-now))
                     (k-caught (prompt k-tag (k-done (k-allof-run x (k-allof-members-of t) check))
                                 (lambda (r) r))))
                (k-now-back k-at-now k-caught)))
           (popped (set k-dead-arms (cdr (get k-dead-arms)))))
      (tagcase r
        (k-done (te) (extract te 2))
        (k-err (m a b ok or) (k-fail-found m a b ok or))
        (k-ok (xs) (k-fail "k-ok inside" (k-start x) (k-end x)))))))
(define k-allof-run (->* (kx k-ids k-check-fn) k-te)
  (lambda (x ms check)
    (let* ((saved (k-code-now))
           (found (k-allof-each x ms check saved 0))
           (dead (k-dead-in-all (extract (car (get k-dead-arms)) 1) (k-length ms) nil)))
      (begin
        (if (null? dead)
            #u
            (let ((d (car dead)))
              (k-fail-no-part (extract d 4) " has no tag " (extract d 5) (extract d 1)
                              (extract d 2))))
        (k-found-agree x ms (extract found 1) 1)
        ;; What every member found, together.
        (k-code-put-back saved)
        (k-found-onto (extract found 1))
        (k-te -1 (extract found 2))))))
;; Each member checked, from the facts as they were (`saved`): what each
;; found, in order, and the effect.
(define k-allof-each (->* (kx k-ids k-check-fn k-code int)
                          (productof (1 (listof k-found acyclic)) (2 k-eff)))
  (lambda (x ms check saved at)
    (if (null? ms)
        (product (1 (the (listof k-found acyclic) nil)) (2 (the k-eff nil)))
        (let* ((reset (begin (k-code-put-back saved)
                             (let ((f (car (get k-dead-arms))))
                               (set k-dead-arms
                                    (cons (product (1 (extract f 1)) (2 (the k-spans nil))
                                                   (3 (extract f 3)) (4 at) (5 (extract f 5)))
                                          (cdr (get k-dead-arms)))))))
               (e (check x (car ms)))
               (f (k-found-since saved (extract (car (get k-dead-arms)) 2)))
               (rest (k-allof-each x (cdr ms) check saved (+ at 1))))
          (product (1 (cons f (extract rest 1))) (2 e))))))
;; Each two members' found alike (`j` from 1), or an error.
(define k-found-agree (->* (kx k-ids (listof k-found acyclic) int) unit)
  (lambda (x ms found j)
    (if (>= j (k-length found))
        #u
        (begin (k-found-agree-with x ms found 0 j) (k-found-agree x ms found (+ j 1))))))
(define k-found-agree-with (->* (kx k-ids (listof k-found acyclic) int int) unit)
  (lambda (x ms found i j)
    (cond ((>= i j) #u)
          ((k-found-alike? (k-nth-found found i) (k-nth-found found j))
           (k-found-agree-with x ms found (+ i 1) j))
          (else
           (k-fail (k-cat5 "one body cannot be each member of this `allof`: checked as a "
                           (k-show-ty (k-nth-id ms i)) " and as a " (k-show-ty (k-nth-id ms j))
                           ", it would be compiled differently")
                   (k-start x) (k-end x))))))
(define k-nth-found (->* ((listof k-found acyclic) int) k-found)
  (lambda (l i) (if (= i 0) (car l) (k-nth-found (cdr l) (- i 1)))))
(define k-nth-id (->* (k-ids int) int)
  (lambda (l i) (if (= i 0) (car l) (k-nth-id (cdr l) (- i 1)))))
;; Each member's facts put with those as they were.
(define k-found-onto (->* ((listof k-found acyclic)) unit)
  (lambda (found)
    (if (null? found)
        #u
        (let ((f (car found)))
          (begin (set k-extracts (append (extract f 1) (get k-extracts)))
                 (set k-with-vals (append (extract f 2) (get k-with-vals)))
                 (set k-reshapes (append (extract f 3) (get k-reshapes)))
                 (k-found-onto (cdr found)))))))

;;; ------------------------------------------------------------ a call

;; What argument `i`, `a`, is found to be by `f`; an error at it reported as
;; that argument.
(define k-as-argument (->* (k-checking kx int) k-te)
  (lambda (f a i)
    (k-rewriting f (k-start a) (k-end a) (lambda (m want got) (k-argument-error i got want)))))
;; Each of `args`' type and effect: as `done` holds it, or synthesized; but a
;; `lambda` with a parameter of no type, which has no type of its own, -1:
;; it fits a member whose parameter is a procedure of its arity, and is
;; checked once the members are known (`k-allof-lambda-args`).
(define k-allof-args (->* (kxs int k-done k-synth-fn) (listof k-te acyclic))
  (lambda (args i done synth)
    (if (null? args)
        nil
        (let* ((t (array-ref (extract done 1) i))
               (te (cond ((>= t 0) (k-te t (array-ref (extract done 2) i)))
                         ((>= (k-untyped-lambda (car args)) 0) (k-te -1 nil))
                         (else (k-as-argument (lambda () (synth (car args))) (car args) i)))))
          (cons te (k-allof-args (cdr args) (+ i 1) done synth))))))
;; Of `x`, a `lambda` with a parameter of no type: its arity; else -1.
(define k-untyped-lambda (->* (kx) int)
  (lambda (x)
    (tagcase x
      (x-lambda (ps body a b abk abkr) (if (k-any-untyped? ps) (k-length ps) -1))
      (else y -1))))
(define k-any-untyped? (->* (k-typed-params) bool)
  (lambda (ps) (and (not (null? ps)) (or (null? (extract (car ps) 2)) (k-any-untyped? (cdr ps))))))
;; Whether a `t` is taken as a `p` only converted (its procedure to another
;; convention) or reshaped (a module).
(define k-adaptable? (->* (int int) bool)
  (lambda (t p) (or (not (null? (k-conversion t p))) (not (null? (k-reshape (k-resolve t) p))))))
;; Each argument of `args`, of types `ts`, from the `i`th, converted or
;; reshaped for a member of `fits`: one value made once, so only where every
;; member it fits takes the same there.
(define k-allof-adapted (->* (kxs (listof k-te acyclic) int k-ids) unit)
  (lambda (args ts i fits)
    (if (null? args)
        #u
        (let ((t (extract (car ts) 1)) (ps (k-params-at fits i)))
          (begin
            (if (and (>= t 0) (k-any-not-below? t ps))
                (let ((p (k-first-unlike-type (car ps) ps)))
                  (if (>= p 0)
                      (k-fail (string-append
                               (k-cat5 "argument " (int->string (+ i 1)) " is a " (k-show-ty t)
                                       ", made a ")
                               (k-cat5 (k-show-ty (car ps)) " for one member this call fits and a "
                                       (k-show-ty p) " for another: one value cannot be both" ""))
                              (k-start (car args)) (k-end (car args)))
                      (k-expect (car args) t (car ps))))
                #u)
            (k-allof-adapted (cdr args) (cdr ts) (+ i 1) fits))))))
(define k-any-not-below? (->* (int k-ids) bool)
  (lambda (t ps)
    (and (not (null? ps)) (or (not (k-subtype t (car ps))) (k-any-not-below? t (cdr ps))))))
(define k-first-unlike-type (->* (int k-ids) int)
  (lambda (t0 ps)
    (cond ((null? ps) -1)
          ((k-same-type? t0 (car ps)) (k-first-unlike-type t0 (cdr ps)))
          (else (car ps)))))
;; The arity of a procedure of type `t`, a `subr` or an `allof` of them; -1.
(define k-procedure-arity (->* (int) int)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-subr (e ps r cv spc) (k-length ps))
      (ty-allof (ms) (k-procedure-arity (car ms)))
      (else y -1))))
(define k-tes-effect (->* ((listof k-te acyclic) k-eff) k-eff)
  (lambda (ts e) (if (null? ts) e (k-tes-effect (cdr ts) (k-union e (extract (car ts) 2))))))
(define k-tes-below? (->* ((listof k-te acyclic) kxs k-ids) bool)
  (lambda (ts args ps)
    (if (null? ts)
        (null? ps)
        (and (not (null? ps))
             (let ((t (extract (car ts) 1)))
               (if (>= t 0)
                   (or (k-subtype t (car ps)) (k-adaptable? t (car ps)))
                   (= (k-procedure-arity (car ps)) (k-untyped-lambda (car args)))))
             (k-tes-below? (cdr ts) (cdr args) (cdr ps))))))
;; The members of `ms` arguments `args`, of types `ts`, fit.
(define k-allof-fits (->* (k-ids (listof k-te acyclic) kxs) k-ids)
  (lambda (ms ts args)
    (if (null? ms)
        nil
        (let ((rest (k-allof-fits (cdr ms) ts args)))
          (tagcase (k-get (k-resolve (car ms)))
            (ty-subr (e ps r cv spc)
              (if (k-tes-below? ts args ps) (the k-ids (cons (car ms) rest)) rest))
            (else y rest))))))
;; Each `lambda` of `args` with a parameter of no type (`ts` -1), from the
;; `i`th, checked against what the members `fits` take there, their `allof`
;; where they differ: its effect, onto `e`.
(define k-allof-lambda-args (->* (kxs (listof k-te acyclic) int k-ids k-check-fn k-eff) k-eff)
  (lambda (args ts i fits check e)
    (if (null? args)
        e
        (let ((more (lambda ((e2 k-eff))
                      (k-allof-lambda-args (cdr args) (cdr ts) (+ i 1) fits check e2))))
          (if (>= (extract (car ts) 1) 0)
              (more e)
              (let* ((ps (k-params-at fits i))
                     (want (if (k-all-same? (car ps) ps)
                               (car ps)
                               (k-allof-made (k-allof-flat ps) (car args))))
                     (a (car args))
                     (te (k-as-argument (lambda () (k-te want (check a want))) a i)))
                (more (k-union e (extract te 2)))))))))
(define k-params-at (->* (k-ids int) k-ids)
  (lambda (ms i)
    (if (null? ms)
        nil
        (the k-ids (cons (k-nth (k-subr-params (car ms)) i) (k-params-at (cdr ms) i))))))
(define k-all-same? (->* (int k-ids) bool)
  (lambda (t0 ts) (or (null? ts) (and (k-same-type? t0 (car ts)) (k-all-same? t0 (cdr ts))))))
(define k-allof-flat (->* (k-ids) k-ids)
  (lambda (ts)
    (if (null? ts)
        nil
        (let ((t (k-resolve (car ts))))
          (tagcase (k-get t)
            (ty-allof (ms) (append ms (k-allof-flat (cdr ts))))
            (else y (the k-ids (cons t (k-allof-flat (cdr ts))))))))))
;; The `allof` of `subr`s `ms`, of one convention, else refused at `x`.
(define k-allof-made (->* (k-ids kx) int)
  (lambda (ms x)
    (let ((other (k-other-conv ms (k-subr-conv-of (car ms)))))
      (if (< other 0)
          (k-ty-new (ty-allof ms))
          (k-fail (k-cat5 "an `allof`'s members have one convention: a " (k-show-ty (car ms))
                          " and a " (k-show-ty other) " do not")
                  (k-start x) (k-end x))))))
(define k-other-conv (->* (k-ids k-conv) int)
  (lambda (ms c)
    (cond ((null? ms) -1)
          ((k-conv=? (k-subr-conv-of (car ms)) c) (k-other-conv (cdr ms) c))
          (else (car ms)))))
(define k-tes-shown (->* ((listof k-te acyclic)) string)
  (lambda (ts)
    (if (null? ts)
        ""
        (string-append (if (< (extract (car ts) 1) 0)
                           "a `lambda` with a parameter of no type"
                           (string-append "a " (k-show-ty (extract (car ts) 1))))
                       (if (null? (cdr ts)) "" ", ") (k-tes-shown (cdr ts))))))
(define k-subr-latent (->* (int) k-eff)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-subr (e ps r cv spc) e) (else y nil))))
(define k-subr-result (->* (int) int)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-subr (e ps r cv spc) r) (else y -1))))
(define k-subr-params (->* (int) k-ids)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-subr (e ps r cv spc) ps) (else y nil))))
;; Of `fits`, the first whose latent effect is within every other's, or the
;; first's: any one member's typing is sound alone.
(define k-least-latent (->* (k-ids k-ids) k-eff)
  (lambda (ls fits)
    (cond ((null? ls) (k-subr-latent (car fits)))
          ((k-latent-within-all? (k-subr-latent (car ls)) fits) (k-subr-latent (car ls)))
          (else (k-least-latent (cdr ls) fits)))))
(define k-latent-within-all? (->* (k-eff k-ids) bool)
  (lambda (l fits)
    (or (null? fits)
        (and (k-within? l (k-subr-latent (car fits))) (k-latent-within-all? l (cdr fits))))))
;; Where a member of `fits` allocates, but not frozen data, onto `out`.
(define k-fresh-of (->* (k-ids k-regions) k-regions)
  (lambda (fits out)
    (letrec ((atoms (->* (k-eff k-regions) k-regions)
                    (lambda (as out)
                      (if (null? as)
                          out
                          (atoms (cdr as)
                                 (tagcase (car as)
                                   (a-alloc (r)
                                     (tagcase r
                                       (r-frozen (p f) out)
                                       (else y (if (k-has-region-in? out r) out (cons r out)))))
                                   (else y out)))))))
      (if (null? fits) out (k-fresh-of (cdr fits) (atoms (k-subr-latent (car fits)) out))))))
;; The meet of the results of `fits` after the first, onto `result`; none
;; where a procedure kept may hold a cell made under each member as
;; another type (`fresh`, `k-meet`), which a meet with none fresh tells.
(define k-results-met (->* (kx int k-ids int k-regions) int)
  (lambda (x m0 fits result fresh)
    (if (null? fits)
        result
        (let ((met (k-meet result (k-subr-result (car fits)) fresh)))
          (if (< met 0)
              (k-fail (k-cat5 "this call fits a " (k-show-ty m0) " and a " (k-show-ty (car fits))
                              (if (< (k-meet result (k-subr-result (car fits)) nil) 0)
                                  ", whose results have no meet"
                                  (string-append ", whose results are procedures that may"
                                                 " keep what the call allocates:"
                                                 " one value would be both")))
                      (k-start x) (k-end x))
              (k-results-met x m0 (cdr fits) met fresh))))))
;; A call `x` of `f`, of type `ft`, an `allof` (`logical-types.md` §8.5,
;; rule 4): each argument synthesized once, and every member whose
;; parameters take them fits; the call's result is the meet of theirs, its
;; latent effect the least of theirs if one is, else the first's.
(define k-allof-call (->* (kx kx int kxs k-done k-te k-synth-fn k-result-fn k-check-fn) k-te)
  (lambda (x f ft args done rf synth result check)
    (let* ((ts (k-allof-args args 0 done synth))
           (fits (k-allof-fits (k-allof-members-of ft) ts args)))
      (if (null? fits)
          (k-fail (k-cat4 "this call fits no member of a " (k-show-ty ft) ": its arguments are "
                          (k-tes-shown ts))
                  (k-start x) (k-end x))
          (let* ((m0 (car fits))
                 (noted (k-note-call x f m0 (k-subr-params m0)))
                 (adapted (k-allof-adapted args ts 0 fits))
                 (fe (k-allof-lambda-args args ts 0 fits check (extract rf 2)))
                 (res (k-results-met x m0 (cdr fits) (k-subr-result m0) (k-fresh-of fits nil)))
                 (own (k-own-member-spins f)))
            (if (null? own)
                (result x f ft args (k-tes-effect ts fe) (k-least-latent fits fits) res)
                ;; A call of its own recursive group, judged member by
                ;; member: `spin` if a member it fits may not end; the `spin`
                ;; naming the callee says, the call's.
                (let* ((e (k-union (k-tes-effect ts (k-without-spin fe))
                                   (k-least-latent fits fits)))
                       (spins (k-fits-spin? (k-allof-members-of ft) fits own)))
                  (k-te-masked x res (if spins (k-insert (a-spin) e) e)))))))))
;; Of the callee `f`, if it is a binding of a recursive group noted member by
;; member (`k-member-spins`), each member's whether it may not end; else none.
(define k-own-member-spins (->* (kx) (listof bool acyclic))
  (lambda (f)
    (let* ((s (k-callee-name f)) (t (if (null? s) -1 (k-lookup (car s)))))
      (if (and (>= t 0) (k-named-has? (get k-recursive) (car s) t))
          (k-member-spins-of (car s) t)
          nil))))
;; Whether a member of `ms` among `fits` may not end, by `own`, in order.
(define k-fits-spin? (->* (k-ids k-ids (listof bool acyclic)) bool)
  (lambda (ms fits own)
    (and (not (null? ms))
         (or (and (k-has-id? fits (car ms)) (or (null? own) (car own)))
             (k-fits-spin? (cdr ms) fits (if (null? own) own (cdr own)))))))
(define k-without-spin (->* (k-eff) k-eff)
  (lambda (e)
    (cond ((null? e) e)
          ((tagcase (car e) (a-spin () #t) (else y #f)) (k-without-spin (cdr e)))
          (else (the k-eff (cons (car e) (k-without-spin (cdr e))))))))

;;; ------------------------------------------------------------ rule 5

;; A call `x` of `f` to `args`, by `app` (`k-synth-app`), or, where it fails
;; whole, union elimination at an argument (`logical-types.md` §8.5, rule
;; 5; U3): the first argument that is a variable of a union, and with which
;; each member makes the call check, is taken as each member in turn. The
;; call's type is the `anyof` of what each gives, its effect theirs
;; together; what the compilers read of it alike under every member. As
;; Rust's `synth_app_split`.
(define k-split-app (->* (kx kx kxs int k-app-fn k-synth-fn) k-te)
  (lambda (x f args expected app synth)
    (let ((r (let* ((k-at-now (k-now))
                    (k-caught (prompt k-tag (k-done (app x f args expected)) (lambda (r) r))))
               (k-now-back k-at-now k-caught))))
      (tagcase r
        ;; Checks, but not as what is expected: as its members, if their
        ;; union is (`swap` of an `(anyof expr op)` an `(anyof expr op)`);
        ;; else as it is, for the expectation to refuse.
        (k-done (te)
          (let ((tried (if (or (< expected 0) (k-subtype (extract te 1) expected))
                           nil
                           (k-split-candidates args 0 synth))))
            (if (null? tried)
                te
                (k-split-or-whole x f args expected app tried te))))
        (k-err (m a b ok or)
          ;; An error found inside an argument that is not a variable is that
          ;; argument's, which no member of another makes go away. Inside by
          ;; structure, not by place: a macro's expansion may give its nodes
          ;; one place, and an argument it copies the place of another's.
          (let ((tried (if (k-err-in-arg? args ok or) nil (k-split-candidates args 0 synth))))
            (if (null? tried)
                (k-fail-found m a b ok or)
                (k-split-tries x f args expected app (k-code-but (k-start x) (k-end x)) tried
                               m a b ok or))))
        (k-ok (xs) (k-fail "k-ok inside" (k-start x) (k-end x)))))))
;; Whether the expression of walk number `ok` and reading `or` is in one of
;; `args` that is not a variable.
(define k-err-in-arg? (->* (kxs int int) bool)
  (lambda (args ok or)
    (and (not (null? args))
         (or (and (tagcase (car args) (x-var (v xa xb abk abkr) #f) (else y #t))
                  (k-skipped? (product (1 0) (2 0) (3 ok) (4 or)) (k-keys-onto (car args) nil)))
             (k-err-in-arg? (cdr args) ok or)))))
;; Each of `args`, from the `i`th, whose type is a union, in order, as it is
;; taken apart: a variable, by its name and binding (`k-narrowed`; 4 is -1);
;; any other, by its place (`k-pinned`), its type synthesized (4 is its
;; index); and its members. As Rust's `union_arguments`.
(define-type k-split (productof (1 symbol) (2 int) (3 k-ids) (4 int)))
(define k-split-candidates (->* (kxs int k-synth-fn) (listof k-split acyclic))
  (lambda (args i synth)
    (if (null? args)
        nil
        (let* ((a (car args))
               (here (tagcase a
                       (x-var (v xa xb abk abkr)
                         (let ((t (k-lookup v)))
                           (if (< t 0)
                               nil
                               (tagcase (k-get (k-resolve t))
                                 (ty-union (ms)
                                   (the (listof k-split acyclic)
                                        (list (product (1 v) (2 (k-name-depth v)) (3 ms) (4 -1)))))
                                 (else y nil)))))
                       (else y
                         (let ((r (let* ((k-at-now (k-now))
                                         (k-caught
                                          (prompt k-tag (k-done (synth a)) (lambda (r) r))))
                                    (k-now-back k-at-now k-caught))))
                           (tagcase r
                             (k-done (te)
                               (tagcase (k-get (k-resolve (extract te 1)))
                                 (ty-union (ms)
                                   (the (listof k-split acyclic)
                                        (list (product (1 '||) (2 -1) (3 ms) (4 i)))))
                                 (else z nil)))
                             (else z nil))))))
               (rest (k-split-candidates (cdr args) (+ i 1) synth)))
          (if (null? here) rest (cons (car here) rest))))))
;; What the compilers read now, but of what is at `a`..`b`: the failed
;; try's.
(define k-code-but (->* (int int) k-code)
  (lambda (a b)
    (letrec ((in? (->* (k-at) bool) (lambda (at) (and (>= (extract at 1) a) (<= (extract at 2) b))))
             (facts (->* (k-facts) k-facts)
               (lambda (l) (cond ((null? l) nil) ((in? (extract (car l) 1)) (facts (cdr l)))
                                 (else (cons (car l) (facts (cdr l)))))))
             (withs (->* (k-with-list) k-with-list)
               (lambda (l) (cond ((null? l) nil) ((in? (extract (car l) 1)) (withs (cdr l)))
                                 (else (cons (car l) (withs (cdr l)))))))
             (reshapes (->* (k-reshape-list) k-reshape-list)
               (lambda (l) (cond ((null? l) nil) ((in? (extract (car l) 1)) (reshapes (cdr l)))
                                 (else (cons (car l) (reshapes (cdr l)))))))
             (bases (->* (k-reshape-base-list) k-reshape-base-list)
               (lambda (l) (cond ((null? l) nil) ((in? (extract (car l) 1)) (bases (cdr l)))
                                 (else (cons (car l) (bases (cdr l))))))))
      (product (1 (facts (get k-extracts))) (2 (withs (get k-with-vals)))
               (3 (reshapes (get k-reshapes))) (4 (bases (get k-reshape-bases)))))))
;; The call taken apart by `tried` if that checks and is as `expected` is,
;; else `te`, what the call found whole, and its facts.
(define k-split-or-whole (->* (kx kx kxs int k-app-fn (listof k-split acyclic) k-te) k-te)
  (lambda (x f args expected app tried te)
    (let* ((whole (k-code-now))
           (inside (k-code-but (k-start x) (k-end x)))
           (r (let* ((k-at-now (k-now))
                     (k-caught (prompt k-tag
                                 (k-done (k-split-tries x f args expected app inside tried
                                                        "" 0 0 -1 -1))
                                 (lambda (r) r))))
                (k-now-back k-at-now k-caught))))
      (tagcase r
        (k-done (u) (if (k-subtype (extract u 1) expected) u (begin (k-code-put-back whole) te)))
        (else y (begin (k-code-put-back whole) te))))))
;; Each of `tried` in turn, until one whose every member checks; none, the
;; error `m` at `a`..`b`, found in `ok` of reading `or`.
(define k-split-tries
  (->* (kx kx kxs int k-app-fn k-code (listof k-split acyclic) string int int int int) k-te)
  (lambda (x f args expected app saved tried m a b ok or)
    (if (null? tried)
        (k-fail-found m a b ok or)
        (let ((runs (k-split-runs x f args expected app saved (car tried) (extract (car tried) 3))))
          (if (null? runs)
              (k-split-tries x f args expected app saved (cdr tried) m a b ok or)
              (k-split-joined x saved (car tried) (car runs)))))))
;; One member's: what it found, and the call's type and effect with it.
(define-type k-run (productof (1 k-found) (2 k-te)))
;; The call with the variable of `s` each of `ms`: what each found, as a
;; list of one; none, if one does not check.
(define k-split-runs (->* (kx kx kxs int k-app-fn k-code k-split k-ids)
                          (listof (listof k-run acyclic) acyclic))
  (lambda (x f args expected app saved s ms)
    (if (null? ms)
        (list nil)
        (let* ((reset (k-code-put-back saved))
               (outer (get k-narrowed))
               (pins (get k-pinned))
               (i (extract s 4))
               (narrow (product (1 (extract s 1)) (2 (extract s 2)) (3 (car ms))))
               (pushed (if (< i 0)
                           (set k-narrowed (cons narrow outer))
                           (let ((pin (product (1 (k-at-of (k-nth args i))) (2 (car ms)))))
                             (set k-pinned (cons pin pins)))))
               (r (let* ((k-at-now (k-now))
                         (k-caught (prompt k-tag (k-done (app x f args expected)) (lambda (r) r))))
                    (k-now-back k-at-now k-caught)))
               (popped (begin (set k-narrowed outer) (set k-pinned pins))))
          (tagcase r
            (k-done (te)
              (let ((run (product (1 (k-found-since saved nil)) (2 te)))
                    (rest (k-split-runs x f args expected app saved s (cdr ms))))
                (if (null? rest) nil (list (cons run (car rest))))))
            (else y nil))))))
;; The runs alike, put together: the `anyof` of their types.
(define k-split-joined (->* (kx k-code k-split (listof k-run acyclic)) k-te)
  (lambda (x saved s runs)
    (begin
      (k-runs-agree x s runs (cdr runs) 1)
      (k-code-put-back saved)
      (k-found-onto (k-runs-found runs))
      (k-te (k-anyof-of (k-runs-types runs) (k-start x) (k-end x)) (k-runs-effect runs)))))
(define k-runs-agree (->* (kx k-split (listof k-run acyclic) (listof k-run acyclic) int) unit)
  (lambda (x s runs rest j)
    (cond ((null? rest) #u)
          ((k-found-alike? (extract (car runs) 1) (extract (car rest) 1))
           (k-runs-agree x s runs (cdr rest) (+ j 1)))
          (else
           (k-fail (k-cat5 (k-cat3 "this call, taken apart by "
                                   (if (< (extract s 4) 0)
                                       (k-cat3 "`" (symbol->string (extract s 1)) "`'s")
                                       (k-cat3 "argument " (int->string (+ (extract s 4) 1)) "'s"))
                                   " members, would be compiled differently with a ")
                           (k-show-ty (car (extract s 3))) " and with a "
                           (k-show-ty (k-nth-id (extract s 3) j)) "")
                   (k-start x) (k-end x))))))
(define k-runs-found (->* ((listof k-run acyclic)) (listof k-found acyclic))
  (lambda (rs) (if (null? rs) nil (cons (extract (car rs) 1) (k-runs-found (cdr rs))))))
(define k-runs-types (->* ((listof k-run acyclic)) k-ids)
  (lambda (rs)
    (if (null? rs)
        nil
        (the k-ids (cons (extract (extract (car rs) 2) 1) (k-runs-types (cdr rs)))))))
(define k-runs-effect (->* ((listof k-run acyclic)) k-eff)
  (lambda (rs)
    (if (null? rs) nil (k-union (extract (extract (car rs) 2) 2) (k-runs-effect (cdr rs))))))

;;; ------------------------------------------------------------ the meet

;; `t`'s procedure types: its own, a `subr`'s; its members, an `allof`'s.
(define k-procs-of (->* (int) k-ids)
  (lambda (t)
    (tagcase (k-get t)
      (ty-subr (e ps r cv spc) (the k-ids (cons t nil)))
      (ty-allof (ms) ms)
      (else y nil))))
(define k-subr-conv-of (->* (int) k-conv)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-subr (e ps r cv spc) cv) (else y (cv-fx)))))
;; The tags of `xs` that `ys` has too, their payloads met; none, if one
;; does not meet.
(define k-meet-sums (->* (k-parts k-parts k-regions) (listof k-parts acyclic))
  (lambda (xs ys fresh)
    (if (null? xs)
        (list (the k-parts nil))
        (let ((rest (k-meet-sums (cdr xs) ys fresh)) (u (k-part-find ys (extract (car xs) 1))))
          (cond ((null? rest) nil)
                ((< u 0) rest)
                (else
                 (let ((m (k-meet (extract (car xs) 2) u fresh)))
                   (if (< m 0)
                       nil
                       (list (the k-parts (cons (product (1 (extract (car xs) 1)) (2 m))
                                                (car rest))))))))))))
;; Field by field, of the same labels; none, if one does not meet.
(define k-meet-fields (->* (k-parts k-parts k-regions) (listof k-parts acyclic))
  (lambda (xs ys fresh)
    (cond ((and (null? xs) (null? ys)) (list (the k-parts nil)))
          ((or (null? xs) (null? ys)
               (not (symbol=? (extract (car xs) 1) (extract (car ys) 1))))
           nil)
          (else
           (let ((m (k-meet (extract (car xs) 2) (extract (car ys) 2) fresh))
                 (rest (k-meet-fields (cdr xs) (cdr ys) fresh)))
             (if (or (< m 0) (null? rest))
                 nil
                 (list (the k-parts (cons (product (1 (extract (car xs) 1)) (2 m))
                                          (car rest))))))))))
;; Whether `named` has a region of `fresh`.
(define k-names-fresh? (->* (k-regions k-regions) bool)
  (lambda (named fresh)
    (and (not (null? fresh))
         (or (k-has-region-in? named (car fresh)) (k-names-fresh? named (cdr fresh))))))
;; The meet of `a` and `b`, the values both are, where that is a type
;; exactly and soundly (`logical-types.md` §8.5, rule 4); -1 where not. As
;; Rust's `Checker::meet`: no two procedure types that name a region of
;; `fresh`, where the call allocates, since a cell made there under each
;; member may be another type under each, and a procedure kept read or
;; write it as either.
(define k-meet (->* (int int k-regions) int)
  (lambda (a0 b0 fresh)
    (let ((a (k-resolve a0)) (b (k-resolve b0)))
      (cond ((k-subtype a b) a)
            ((k-subtype b a) b)
            ((and (not (null? (k-procs-of a))) (not (null? (k-procs-of b))))
             (if (k-conv=? (k-subr-conv-of (car (k-procs-of a)))
                           (k-subr-conv-of (car (k-procs-of b))))
                 (if (k-names-fresh? (append (k-regions-in a) (k-regions-in b)) fresh)
                     -1
                     (k-ty-new (ty-allof (append (k-procs-of a) (k-procs-of b)))))
                 -1))
            (else
             (tagcase (k-get a)
               (ty-sum (xs)
                 (tagcase (k-get b)
                   (ty-sum (ys)
                     (let ((ps (k-meet-sums xs ys fresh)))
                       (cond ((null? ps) -1)
                             ((null? (car ps)) k-void)
                             (else (k-ty-new (ty-sum (car ps)))))))
                   (else z -1)))
               (ty-product (xs)
                 (tagcase (k-get b)
                   (ty-product (ys)
                     (let ((ps (k-meet-fields xs ys fresh)))
                       (if (null? ps) -1 (k-ty-new (ty-product (car ps))))))
                   (else z -1)))
               (else z -1))))))))))
