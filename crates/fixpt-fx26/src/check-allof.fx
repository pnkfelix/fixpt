;;; The checker, in FX-26: `allof`, one procedure with each member's type
;;; (`docs/research/logical-types.md` §8.5, U1), the Rust checker's
;;; `check_allof_lambda`, `synth_allof_call` and `meet`, rule for rule and
;;; in its words. A `lambda` is checked against each member: a `tagcase`
;;; arm a member's type rules out is skipped there (`k-arm-dead?`), and is
;;; an error only if every member skips it; what the compilers read of its
;;; body must be found alike under every member, since it is compiled once.
;;; A call takes every member it fits, its result the meet of theirs.

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
       (check-allof-types (load-module "fx26:check-allof-types.fx")))
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
           (check-errors (select check-errors-types check-errors-sig)))
    (module

;; The types it uses of the files before it.
(hide (include check-types-types) (include check-env-types) (include check-allof-types))
(import check-synth-types (type k-done))
(import check-subtype-types (type k-checking))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-env) (include check-print) (include check-print-parts)
      (include check-effects) (include check-subtype))
(import check-resolve k-start k-end k-at-of)
(import check-synth k-note-call)
(import check-expect k-rewriting)
(import check-errors k-argument-error k-fail-no-part)

;;; ------------------------------------------------------------ the type

;; `t`'s members, if it is an `allof`.
(define k-allof-members-of (->* (int) k-ids)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-allof (ms) ms) (else y nil))))
(define k-allof-type? (->* (int) bool)
  (lambda (t) (not (null? (k-allof-members-of t)))))

;;; ------------------------------------------------------------ dead arms

;; The arm for `tag`, whose body is at `a`..`b`, of a `tagcase` whose
;; subject is a `st` without it: skipped (#t) while a `lambda` is checked
;; against a member of an `allof`, and noted (`k-dead-arms`); else an error.
(define k-arm-dead? (->* (int symbol int int) bool)
  (lambda (st tag a b)
    (let ((fs (get k-dead-arms)))
      (if (null? fs)
          (begin (k-fail-no-part st " has no tag " tag a b) #f)
          (let* ((f (car fs)) (arms (k-dead-counted (extract f 1) st tag a b))
                 (now (the k-spans (cons (product (1 a) (2 b)) (extract f 2)))))
            (begin (set k-dead-arms (cons (product (1 arms) (2 now)) (cdr fs))) #t))))))
;; `arms` with the one at `a`..`b` counted once more, its error's type `st`.
(define k-dead-counted (->* ((listof k-dead-arm acyclic) int symbol int int)
                            (listof k-dead-arm acyclic))
  (lambda (arms st tag a b)
    (cond ((null? arms) (list (product (1 a) (2 b) (3 1) (4 st) (5 tag))))
          ((and (= (extract (car arms) 1) a) (= (extract (car arms) 2) b))
           (cons (product (1 a) (2 b) (3 (+ 1 (extract (car arms) 3))) (4 st) (5 tag)) (cdr arms)))
          (else (cons (car arms) (k-dead-counted (cdr arms) st tag a b))))))
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
  (lambda (x y)
    (and (= (extract x 1) (extract y 1)) (= (extract x 2) (extract y 2))
         (= (extract x 3) (extract y 3)))))
;; Whether `at` is within one of `spans`.
(define k-skipped? (->* (k-at k-spans) bool)
  (lambda (at spans)
    (and (not (null? spans))
         (or (and (>= (extract at 1) (extract (car spans) 1))
                  (<= (extract at 2) (extract (car spans) 2)))
             (k-skipped? at (cdr spans))))))
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
      (n-staged (f n r) (tagcase y (n-staged (g m s) (and (string=? f g) (string=? n m)))
                          (else z #f))))))
(define k-noted-kind (->* (k-noted) int)
  (lambda (x)
    (tagcase x
      (n-datum (d) 0) (n-summary (s) 1) (n-conversion (k) 2) (n-apply-shares () 3)
      (n-frozen-define () 4) (n-plain-fx () 5) (n-call (c) 6) (n-staged (f n r) 7))))
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
    (let* ((pushed (set k-dead-arms (cons (product (1 nil) (2 nil)) (get k-dead-arms))))
           (r (prompt k-tag (k-done (k-allof-run x (k-allof-members-of t) check))
                      (lambda (r) r)))
           (popped (set k-dead-arms (cdr (get k-dead-arms)))))
      (tagcase r
        (k-done (te) (extract te 2))
        (k-err (m a b) (k-fail m a b))
        (k-ok (xs) (k-fail "k-ok inside" (k-start x) (k-end x)))))))
(define k-allof-run (->* (kx k-ids k-check-fn) k-te)
  (lambda (x ms check)
    (let* ((saved (k-code-now))
           (found (k-allof-each x ms check saved))
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
(define k-allof-each (->* (kx k-ids k-check-fn k-code)
                          (productof (1 (listof k-found acyclic)) (2 k-eff)))
  (lambda (x ms check saved)
    (if (null? ms)
        (product (1 (the (listof k-found acyclic) nil)) (2 (the k-eff nil)))
        (let* ((reset (begin (k-code-put-back saved)
                             (set k-dead-arms (cons (product (1 (extract (car (get k-dead-arms)) 1))
                                                             (2 (the k-spans nil)))
                                                    (cdr (get k-dead-arms))))))
               (e (check x (car ms)))
               (f (k-found-since saved (extract (car (get k-dead-arms)) 2)))
               (rest (k-allof-each x (cdr ms) check saved)))
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
;; Each of `args`' type and effect: as `done` holds it, or synthesized.
(define k-allof-args (->* (kxs int k-done k-synth-fn) (listof k-te acyclic))
  (lambda (args i done synth)
    (if (null? args)
        nil
        (let* ((t (array-ref (extract done 1) i))
               (te (if (>= t 0)
                       (k-te t (array-ref (extract done 2) i))
                       (k-as-argument (lambda () (synth (car args))) (car args) i))))
          (cons te (k-allof-args (cdr args) (+ i 1) done synth))))))
(define k-tes-effect (->* ((listof k-te acyclic) k-eff) k-eff)
  (lambda (ts e) (if (null? ts) e (k-tes-effect (cdr ts) (k-union e (extract (car ts) 2))))))
(define k-tes-below? (->* ((listof k-te acyclic) k-ids) bool)
  (lambda (ts ps)
    (if (null? ts)
        (null? ps)
        (and (not (null? ps)) (k-subtype (extract (car ts) 1) (car ps))
             (k-tes-below? (cdr ts) (cdr ps))))))
;; The members of `ms` arguments `ts` fit.
(define k-allof-fits (->* (k-ids (listof k-te acyclic)) k-ids)
  (lambda (ms ts)
    (if (null? ms)
        nil
        (let ((rest (k-allof-fits (cdr ms) ts)))
          (tagcase (k-get (k-resolve (car ms)))
            (ty-subr (e ps r cv spc)
              (if (k-tes-below? ts ps) (the k-ids (cons (car ms) rest)) rest))
            (else y rest))))))
(define k-tes-shown (->* ((listof k-te acyclic)) string)
  (lambda (ts)
    (if (null? ts)
        ""
        (string-append "a " (k-show-ty (extract (car ts) 1))
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
;; The meet of the results of `fits` after the first, onto `result`.
(define k-results-met (->* (kx int k-ids int) int)
  (lambda (x m0 fits result)
    (if (null? fits)
        result
        (let ((met (k-meet result (k-subr-result (car fits)))))
          (if (< met 0)
              (k-fail (k-cat5 "this call fits a " (k-show-ty m0) " and a " (k-show-ty (car fits))
                              ", whose results have no meet")
                      (k-start x) (k-end x))
              (k-results-met x m0 (cdr fits) met))))))
;; A call `x` of `f`, of type `ft`, an `allof` (`logical-types.md` §8.5,
;; rule 4): each argument synthesized once, and every member whose
;; parameters take them fits; the call's result is the meet of theirs, its
;; latent effect the least of theirs if one is, else the first's.
(define k-allof-call (->* (kx kx int kxs k-done k-eff k-synth-fn k-result-fn) k-te)
  (lambda (x f ft args done fe synth result)
    (let* ((ts (k-allof-args args 0 done synth))
           (fits (k-allof-fits (k-allof-members-of ft) ts)))
      (if (null? fits)
          (k-fail (k-cat4 "this call fits no member of a " (k-show-ty ft) ": its arguments are "
                          (k-tes-shown ts))
                  (k-start x) (k-end x))
          (let* ((m0 (car fits))
                 (noted (k-note-call x f m0 (k-subr-params m0)))
                 (res (k-results-met x m0 (cdr fits) (k-subr-result m0))))
            (result x f ft args (k-tes-effect ts fe) (k-least-latent fits fits) res))))))

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
(define k-meet-sums (->* (k-parts k-parts) (listof k-parts acyclic))
  (lambda (xs ys)
    (if (null? xs)
        (list (the k-parts nil))
        (let ((rest (k-meet-sums (cdr xs) ys)) (u (k-part-find ys (extract (car xs) 1))))
          (cond ((null? rest) nil)
                ((< u 0) rest)
                (else
                 (let ((m (k-meet (extract (car xs) 2) u)))
                   (if (< m 0)
                       nil
                       (list (the k-parts (cons (product (1 (extract (car xs) 1)) (2 m))
                                                (car rest))))))))))))
;; Field by field, of the same labels; none, if one does not meet.
(define k-meet-fields (->* (k-parts k-parts) (listof k-parts acyclic))
  (lambda (xs ys)
    (cond ((and (null? xs) (null? ys)) (list (the k-parts nil)))
          ((or (null? xs) (null? ys)
               (not (symbol=? (extract (car xs) 1) (extract (car ys) 1))))
           nil)
          (else
           (let ((m (k-meet (extract (car xs) 2) (extract (car ys) 2)))
                 (rest (k-meet-fields (cdr xs) (cdr ys))))
             (if (or (< m 0) (null? rest))
                 nil
                 (list (the k-parts (cons (product (1 (extract (car xs) 1)) (2 m))
                                          (car rest))))))))))
;; The meet of `a` and `b`, the values both are, where that is a type
;; exactly and soundly (`logical-types.md` §8.5, rule 4); -1 where not. As
;; Rust's `Checker::meet`.
(define k-meet (->* (int int) int)
  (lambda (a0 b0)
    (let ((a (k-resolve a0)) (b (k-resolve b0)))
      (cond ((k-subtype a b) a)
            ((k-subtype b a) b)
            ((and (not (null? (k-procs-of a))) (not (null? (k-procs-of b))))
             (if (k-conv=? (k-subr-conv-of (car (k-procs-of a)))
                           (k-subr-conv-of (car (k-procs-of b))))
                 (k-ty-new (ty-allof (append (k-procs-of a) (k-procs-of b))))
                 -1))
            (else
             (tagcase (k-get a)
               (ty-sum (xs)
                 (tagcase (k-get b)
                   (ty-sum (ys)
                     (let ((ps (k-meet-sums xs ys)))
                       (cond ((null? ps) -1)
                             ((null? (car ps)) k-void)
                             (else (k-ty-new (ty-sum (car ps)))))))
                   (else z -1)))
               (ty-product (xs)
                 (tagcase (k-get b)
                   (ty-product (ys)
                     (let ((ps (k-meet-fields xs ys)))
                       (if (null? ps) -1 (k-ty-new (ty-product (car ps))))))
                   (else z -1)))
               (else z -1))))))))))
