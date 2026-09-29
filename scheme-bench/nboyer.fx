;;; NBOYER -- Logic programming benchmark, originally written by Bob Boyer.
;;; Fairly CONS intensive.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/nboyer.scm),
;;; ported to FX-26. Larceny's input: 1 iteration of
;;; (setup-boyer) (test-boyer alist term 5). Answer: 51507739 (rewrites).
;;;
;;; File:         nboyer.sch
;;; Description:  The Boyer benchmark
;;; Author:       Bob Boyer
;;; Created:      5-Apr-85
;;; Modified:     10-Apr-85 14:52:20 (Bob Shaw)
;;;               22-Jul-87 (Will Clinger)
;;;               2-Jul-88 (Will Clinger -- distinguished #f and the empty list)
;;;               13-Feb-97 (Will Clinger -- fixed bugs in unifier and rules,
;;;                          rewrote to eliminate property lists, and added
;;;                          a scaling parameter suggested by Bob Boyer)
;;;               19-Mar-99 (Will Clinger -- cleaned up comments)
;;;               24-Nov-07 (Will Clinger -- converted to R6RS)
;;; Language:     Scheme
;;; Status:       Public Domain
;;;
;;; What the port changes, and why:
;;; - Terms are a `define-datatype`: `(var sym)`, `(num n)`, and `(app rec
;;;   args)`, where Scheme has a symbol, a number, or a pair of a
;;;   symbol-record and the argument list. `(car term)` and `(cdr term)` of
;;;   a pair are the `app`'s members; `(pair? term)` is a `tagcase`.
;;; - The quoted data (the lemmas, `alist`, `term`) are untranslated terms,
;;;   another datatype, `raw` (`rv`, `rn`, `ra`: a variable, a number, a
;;;   symbol applied to raw terms), written as constructor expressions and
;;;   built once when the program is loaded, as Scheme's quoted constants
;;;   are. `translate-term` makes a new `var` or `num` of an atom where
;;;   Scheme returns the atom itself (setup only).
;;; - A symbol-record is a bloblet of the symbol and its lemmas. FX-26 has
;;;   no `eq?` on mutable data, so `symbol-record-equal?` compares the
;;;   records' symbols (`symbol=?`), which is the same test, since each
;;;   symbol has one record.
;;; - Association lists hold pairs, and `assq`'s #f is `nil`. Scheme's
;;;   `assq` of a number in `unify-subst` (whose keys are all symbols) walks
;;;   the list and fails; the port goes straight to the number case.
;;; - `rewrite-count`, `unify-subst`, `*symbol-records-alist*`,
;;;   `if-constructor`, `false-term` and `true-term` are refs.
;;; - `add-lemma`'s `(error …)` for a lemma not of the form `(equal (f …)
;;;   …)` does nothing here; every lemma is of that form.
;;; - `test-boyer` gives -1 where Scheme gives #f (not a tautology).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Note:  The version of this benchmark that appears in Dick Gabriel's book
;;; contained several bugs that are corrected here.  These bugs are discussed
;;; by Henry Baker, "The Boyer Benchmark Meets Linear Logic", ACM SIGPLAN Lisp
;;; Pointers 6(4), October-December 1993, pages 3-10.  The fixed bugs are:
;;;
;;;    The benchmark now returns a boolean result.
;;;    FALSEP and TRUEP use TERM-MEMBER? rather than MEMV (which is called MEMBER
;;;         in Common Lisp)
;;;    ONE-WAY-UNIFY1 now treats numbers correctly
;;;    ONE-WAY-UNIFY1-LST now treats empty lists correctly
;;;    Rule 19 has been corrected (this rule was not touched by the original
;;;         benchmark, but is used by this version)
;;;    Rules 84 and 101 have been corrected (but these rules are never touched
;;;         by the benchmark)
;;;
;;; According to Baker, these bug fixes make the benchmark 10-25% slower.
;;; Please do not compare the timings from this benchmark against those of
;;; the original benchmark.
;;;
;;; This version of the benchmark also prints the number of rewrites as a sanity
;;; check, because it is too easy for a buggy version to return the correct
;;; boolean result.  The correct number of rewrites is
;;;
;;;     n      rewrites       peak live storage (approximate, in bytes)
;;;     0         95024           520,000
;;;     1        591777         2,085,000
;;;     2       1813975         5,175,000
;;;     3       5375678
;;;     4      16445406
;;;     5      51507739
;;;
;;; Nboyer is a 2-phase benchmark.
;;; The first phase attaches lemmas to symbols.  This phase is not timed,
;;; but it accounts for very little of the runtime anyway.
;;; The second phase creates the test problem, and tests to see
;;; whether it is implied by the lemmas.

(define-effect mutates (maxeff (read @heap) (write @heap) (alloc @heap) spin))

;; A symbol-record is represented as a bloblet with two fields:
;; the symbol (for debugging) and
;; the list of lemmas associated with the symbol.
;; (A `define-type` cannot name a type defined after it, so the record's
;; type is written out in `term`, then named.)
(define-datatype term (var symbol) (num int) (app (bloblet (fields symbol (listof term @heap)) @heap) (listof term @heap)))
(define-type symrec (bloblet (fields symbol (listof term @heap)) @heap))
(define-type terms (listof term @heap))

;; Quoted, untranslated terms.
(define-datatype raw (rv symbol) (rn int) (ra symbol (listof raw @heap)))
(define-type raws (listof raw @heap))
(define* r0 (subr (alloc @heap) (symbol) raw) (lambda (f) (ra f nil)))
(define* r1 (subr (alloc @heap) (symbol raw) raw) (lambda (f x) (ra f (cons x nil))))
(define* r2 (subr (alloc @heap) (symbol raw raw) raw) (lambda (f x y) (ra f (cons x (cons y nil)))))
(define* r3 (subr (alloc @heap) (symbol raw raw raw) raw) (lambda (f x y z) (ra f (cons x (cons y (cons z nil))))))

(define alist (listof (pairof symbol raw @heap) @heap)
  (cons (cons 'x (r1 'f (r2 'plus (r2 'plus (rv 'a) (rv 'b)) (r2 'plus (rv 'c) (r0 'zero)))))
  (cons (cons 'y (r1 'f (r2 'times (r2 'times (rv 'a) (rv 'b)) (r2 'plus (rv 'c) (rv 'd)))))
  (cons (cons 'z (r1 'f (r1 'reverse (r2 'append (r2 'append (rv 'a) (rv 'b)) (r0 'nil)))))
  (cons (cons 'u (r2 'equal (r2 'plus (rv 'a) (rv 'b)) (r2 'difference (rv 'x) (rv 'y))))
  (cons (cons 'w (r2 'lessp (r2 'remainder (rv 'a) (rv 'b)) (r2 'member (rv 'a) (r1 'length (rv 'b)))))
  nil))))))

(define term raw
  (r2 'implies (r2 'and (r2 'implies (rv 'x) (rv 'y)) (r2 'and (r2 'implies (rv 'y) (rv 'z)) (r2 'and (r2 'implies (rv 'z) (rv 'u)) (r2 'implies (rv 'u) (rv 'w))))) (r2 'implies (rv 'x) (rv 'w))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; The first phase.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; In the original benchmark, it stored a list of lemmas on the
; property lists of symbols.
; In the new benchmark, it maintains an association list of
; symbols and symbol-records, and stores the list of lemmas
; within the symbol-records.

(define lemmas raws
   (cons (r2 'equal (r1 'compile (rv 'form))
                  (r1 'reverse (r2 'codegen (r1 'optimize (rv 'form)) (r0 'nil))))
   (cons (r2 'equal (r2 'eqp (rv 'x) (rv 'y))
                  (r2 'equal (r1 'fix (rv 'x)) (r1 'fix (rv 'y))))
   (cons (r2 'equal (r2 'greaterp (rv 'x) (rv 'y))
                  (r2 'lessp (rv 'y) (rv 'x)))
   (cons (r2 'equal (r2 'lesseqp (rv 'x) (rv 'y))
                  (r1 'not (r2 'lessp (rv 'y) (rv 'x))))
   (cons (r2 'equal (r2 'greatereqp (rv 'x) (rv 'y))
                  (r1 'not (r2 'lessp (rv 'x) (rv 'y))))
   (cons (r2 'equal (r1 'boolean (rv 'x))
                  (r2 'or (r2 'equal (rv 'x) (r0 't)) (r2 'equal (rv 'x) (r0 'f))))
   (cons (r2 'equal (r2 'iff (rv 'x) (rv 'y))
                  (r2 'and (r2 'implies (rv 'x) (rv 'y)) (r2 'implies (rv 'y) (rv 'x))))
   (cons (r2 'equal (r1 'even1 (rv 'x))
                  (r3 'if (r1 'zerop (rv 'x)) (r0 't) (r1 'odd (r1 '_1- (rv 'x)))))
   (cons (r2 'equal (r2 'countps- (rv 'l) (rv 'pred))
                  (r3 'countps-loop (rv 'l) (rv 'pred) (r0 'zero)))
   (cons (r2 'equal (r1 'fact- (rv 'i))
                  (r2 'fact-loop (rv 'i) (rn 1)))
   (cons (r2 'equal (r1 'reverse- (rv 'x))
                  (r2 'reverse-loop (rv 'x) (r0 'nil)))
   (cons (r2 'equal (r2 'divides (rv 'x) (rv 'y))
                  (r1 'zerop (r2 'remainder (rv 'y) (rv 'x))))
   (cons (r2 'equal (r2 'assume-true (rv 'var) (rv 'alist))
                  (r2 'cons (r2 'cons (rv 'var) (r0 't)) (rv 'alist)))
   (cons (r2 'equal (r2 'assume-false (rv 'var) (rv 'alist))
                  (r2 'cons (r2 'cons (rv 'var) (r0 'f)) (rv 'alist)))
   (cons (r2 'equal (r1 'tautology-checker (rv 'x))
                  (r2 'tautologyp (r1 'normalize (rv 'x)) (r0 'nil)))
   (cons (r2 'equal (r1 'falsify (rv 'x))
                  (r2 'falsify1 (r1 'normalize (rv 'x)) (r0 'nil)))
   (cons (r2 'equal (r1 'prime (rv 'x))
                  (r3 'and (r1 'not (r1 'zerop (rv 'x))) (r1 'not (r2 'equal (rv 'x) (r1 'add1 (r0 'zero)))) (r2 'prime1 (rv 'x) (r1 '_1- (rv 'x)))))
   (cons (r2 'equal (r2 'and (rv 'p) (rv 'q))
                  (r3 'if (rv 'p) (r3 'if (rv 'q) (r0 't) (r0 'f)) (r0 'f)))
   (cons (r2 'equal (r2 'or (rv 'p) (rv 'q))
                  (r3 'if (rv 'p) (r0 't) (r3 'if (rv 'q) (r0 't) (r0 'f))))
   (cons (r2 'equal (r1 'not (rv 'p))
                  (r3 'if (rv 'p) (r0 'f) (r0 't)))
   (cons (r2 'equal (r2 'implies (rv 'p) (rv 'q))
                  (r3 'if (rv 'p) (r3 'if (rv 'q) (r0 't) (r0 'f)) (r0 't)))
   (cons (r2 'equal (r1 'fix (rv 'x))
                  (r3 'if (r1 'numberp (rv 'x)) (rv 'x) (r0 'zero)))
   (cons (r2 'equal (r3 'if (r3 'if (rv 'a) (rv 'b) (rv 'c)) (rv 'd) (rv 'e))
                  (r3 'if (rv 'a) (r3 'if (rv 'b) (rv 'd) (rv 'e)) (r3 'if (rv 'c) (rv 'd) (rv 'e))))
   (cons (r2 'equal (r1 'zerop (rv 'x))
                  (r2 'or (r2 'equal (rv 'x) (r0 'zero)) (r1 'not (r1 'numberp (rv 'x)))))
   (cons (r2 'equal (r2 'plus (r2 'plus (rv 'x) (rv 'y)) (rv 'z))
                  (r2 'plus (rv 'x) (r2 'plus (rv 'y) (rv 'z))))
   (cons (r2 'equal (r2 'equal (r2 'plus (rv 'a) (rv 'b)) (r0 'zero))
                  (r2 'and (r1 'zerop (rv 'a)) (r1 'zerop (rv 'b))))
   (cons (r2 'equal (r2 'difference (rv 'x) (rv 'x))
                  (r0 'zero))
   (cons (r2 'equal (r2 'equal (r2 'plus (rv 'a) (rv 'b)) (r2 'plus (rv 'a) (rv 'c)))
                  (r2 'equal (r1 'fix (rv 'b)) (r1 'fix (rv 'c))))
   (cons (r2 'equal (r2 'equal (r0 'zero) (r2 'difference (rv 'x) (rv 'y)))
                  (r1 'not (r2 'lessp (rv 'y) (rv 'x))))
   (cons (r2 'equal (r2 'equal (rv 'x) (r2 'difference (rv 'x) (rv 'y)))
                  (r2 'and (r1 'numberp (rv 'x)) (r2 'or (r2 'equal (rv 'x) (r0 'zero)) (r1 'zerop (rv 'y)))))
   (cons (r2 'equal (r2 'meaning (r1 'plus-tree (r2 'append (rv 'x) (rv 'y))) (rv 'a))
                  (r2 'plus (r2 'meaning (r1 'plus-tree (rv 'x)) (rv 'a)) (r2 'meaning (r1 'plus-tree (rv 'y)) (rv 'a))))
   (cons (r2 'equal (r2 'meaning (r1 'plus-tree (r1 'plus-fringe (rv 'x))) (rv 'a))
                  (r1 'fix (r2 'meaning (rv 'x) (rv 'a))))
   (cons (r2 'equal (r2 'append (r2 'append (rv 'x) (rv 'y)) (rv 'z))
                  (r2 'append (rv 'x) (r2 'append (rv 'y) (rv 'z))))
   (cons (r2 'equal (r1 'reverse (r2 'append (rv 'a) (rv 'b)))
                  (r2 'append (r1 'reverse (rv 'b)) (r1 'reverse (rv 'a))))
   (cons (r2 'equal (r2 'times (rv 'x) (r2 'plus (rv 'y) (rv 'z)))
                  (r2 'plus (r2 'times (rv 'x) (rv 'y)) (r2 'times (rv 'x) (rv 'z))))
   (cons (r2 'equal (r2 'times (r2 'times (rv 'x) (rv 'y)) (rv 'z))
                  (r2 'times (rv 'x) (r2 'times (rv 'y) (rv 'z))))
   (cons (r2 'equal (r2 'equal (r2 'times (rv 'x) (rv 'y)) (r0 'zero))
                  (r2 'or (r1 'zerop (rv 'x)) (r1 'zerop (rv 'y))))
   (cons (r2 'equal (r3 'exec (r2 'append (rv 'x) (rv 'y)) (rv 'pds) (rv 'envrn))
                  (r3 'exec (rv 'y) (r3 'exec (rv 'x) (rv 'pds) (rv 'envrn)) (rv 'envrn)))
   (cons (r2 'equal (r2 'mc-flatten (rv 'x) (rv 'y))
                  (r2 'append (r1 'flatten (rv 'x)) (rv 'y)))
   (cons (r2 'equal (r2 'member (rv 'x) (r2 'append (rv 'a) (rv 'b)))
                  (r2 'or (r2 'member (rv 'x) (rv 'a)) (r2 'member (rv 'x) (rv 'b))))
   (cons (r2 'equal (r2 'member (rv 'x) (r1 'reverse (rv 'y)))
                  (r2 'member (rv 'x) (rv 'y)))
   (cons (r2 'equal (r1 'length (r1 'reverse (rv 'x)))
                  (r1 'length (rv 'x)))
   (cons (r2 'equal (r2 'member (rv 'a) (r2 'intersect (rv 'b) (rv 'c)))
                  (r2 'and (r2 'member (rv 'a) (rv 'b)) (r2 'member (rv 'a) (rv 'c))))
   (cons (r2 'equal (r2 'nth (r0 'zero) (rv 'i))
                  (r0 'zero))
   (cons (r2 'equal (r2 'exp (rv 'i) (r2 'plus (rv 'j) (rv 'k)))
                  (r2 'times (r2 'exp (rv 'i) (rv 'j)) (r2 'exp (rv 'i) (rv 'k))))
   (cons (r2 'equal (r2 'exp (rv 'i) (r2 'times (rv 'j) (rv 'k)))
                  (r2 'exp (r2 'exp (rv 'i) (rv 'j)) (rv 'k)))
   (cons (r2 'equal (r2 'reverse-loop (rv 'x) (rv 'y))
                  (r2 'append (r1 'reverse (rv 'x)) (rv 'y)))
   (cons (r2 'equal (r2 'reverse-loop (rv 'x) (r0 'nil))
                  (r1 'reverse (rv 'x)))
   (cons (r2 'equal (r2 'count-list (rv 'z) (r2 'sort-lp (rv 'x) (rv 'y)))
                  (r2 'plus (r2 'count-list (rv 'z) (rv 'x)) (r2 'count-list (rv 'z) (rv 'y))))
   (cons (r2 'equal (r2 'equal (r2 'append (rv 'a) (rv 'b)) (r2 'append (rv 'a) (rv 'c)))
                  (r2 'equal (rv 'b) (rv 'c)))
   (cons (r2 'equal (r2 'plus (r2 'remainder (rv 'x) (rv 'y)) (r2 'times (rv 'y) (r2 'quotient (rv 'x) (rv 'y))))
                  (r1 'fix (rv 'x)))
   (cons (r2 'equal (r2 'power-eval (r3 'big-plus1 (rv 'l) (rv 'i) (rv 'base)) (rv 'base))
                  (r2 'plus (r2 'power-eval (rv 'l) (rv 'base)) (rv 'i)))
   (cons (r2 'equal (r2 'power-eval (ra 'big-plus (cons (rv 'x) (cons (rv 'y) (cons (rv 'i) (cons (rv 'base) nil))))) (rv 'base))
                  (r2 'plus (rv 'i) (r2 'plus (r2 'power-eval (rv 'x) (rv 'base)) (r2 'power-eval (rv 'y) (rv 'base)))))
   (cons (r2 'equal (r2 'remainder (rv 'y) (rn 1))
                  (r0 'zero))
   (cons (r2 'equal (r2 'lessp (r2 'remainder (rv 'x) (rv 'y)) (rv 'y))
                  (r1 'not (r1 'zerop (rv 'y))))
   (cons (r2 'equal (r2 'remainder (rv 'x) (rv 'x))
                  (r0 'zero))
   (cons (r2 'equal (r2 'lessp (r2 'quotient (rv 'i) (rv 'j)) (rv 'i))
                  (r2 'and (r1 'not (r1 'zerop (rv 'i))) (r2 'or (r1 'zerop (rv 'j)) (r1 'not (r2 'equal (rv 'j) (rn 1))))))
   (cons (r2 'equal (r2 'lessp (r2 'remainder (rv 'x) (rv 'y)) (rv 'x))
                  (r3 'and (r1 'not (r1 'zerop (rv 'y))) (r1 'not (r1 'zerop (rv 'x))) (r1 'not (r2 'lessp (rv 'x) (rv 'y)))))
   (cons (r2 'equal (r2 'power-eval (r2 'power-rep (rv 'i) (rv 'base)) (rv 'base))
                  (r1 'fix (rv 'i)))
   (cons (r2 'equal (r2 'power-eval (ra 'big-plus (cons (r2 'power-rep (rv 'i) (rv 'base)) (cons (r2 'power-rep (rv 'j) (rv 'base)) (cons (r0 'zero) (cons (rv 'base) nil))))) (rv 'base))
                  (r2 'plus (rv 'i) (rv 'j)))
   (cons (r2 'equal (r2 'gcd (rv 'x) (rv 'y))
                  (r2 'gcd (rv 'y) (rv 'x)))
   (cons (r2 'equal (r2 'nth (r2 'append (rv 'a) (rv 'b)) (rv 'i))
                  (r2 'append (r2 'nth (rv 'a) (rv 'i)) (r2 'nth (rv 'b) (r2 'difference (rv 'i) (r1 'length (rv 'a))))))
   (cons (r2 'equal (r2 'difference (r2 'plus (rv 'x) (rv 'y)) (rv 'x))
                  (r1 'fix (rv 'y)))
   (cons (r2 'equal (r2 'difference (r2 'plus (rv 'y) (rv 'x)) (rv 'x))
                  (r1 'fix (rv 'y)))
   (cons (r2 'equal (r2 'difference (r2 'plus (rv 'x) (rv 'y)) (r2 'plus (rv 'x) (rv 'z)))
                  (r2 'difference (rv 'y) (rv 'z)))
   (cons (r2 'equal (r2 'times (rv 'x) (r2 'difference (rv 'c) (rv 'w)))
                  (r2 'difference (r2 'times (rv 'c) (rv 'x)) (r2 'times (rv 'w) (rv 'x))))
   (cons (r2 'equal (r2 'remainder (r2 'times (rv 'x) (rv 'z)) (rv 'z))
                  (r0 'zero))
   (cons (r2 'equal (r2 'difference (r2 'plus (rv 'b) (r2 'plus (rv 'a) (rv 'c))) (rv 'a))
                  (r2 'plus (rv 'b) (rv 'c)))
   (cons (r2 'equal (r2 'difference (r1 'add1 (r2 'plus (rv 'y) (rv 'z))) (rv 'z))
                  (r1 'add1 (rv 'y)))
   (cons (r2 'equal (r2 'lessp (r2 'plus (rv 'x) (rv 'y)) (r2 'plus (rv 'x) (rv 'z)))
                  (r2 'lessp (rv 'y) (rv 'z)))
   (cons (r2 'equal (r2 'lessp (r2 'times (rv 'x) (rv 'z)) (r2 'times (rv 'y) (rv 'z)))
                  (r2 'and (r1 'not (r1 'zerop (rv 'z))) (r2 'lessp (rv 'x) (rv 'y))))
   (cons (r2 'equal (r2 'lessp (rv 'y) (r2 'plus (rv 'x) (rv 'y)))
                  (r1 'not (r1 'zerop (rv 'x))))
   (cons (r2 'equal (r2 'gcd (r2 'times (rv 'x) (rv 'z)) (r2 'times (rv 'y) (rv 'z)))
                  (r2 'times (rv 'z) (r2 'gcd (rv 'x) (rv 'y))))
   (cons (r2 'equal (r2 'value (r1 'normalize (rv 'x)) (rv 'a))
                  (r2 'value (rv 'x) (rv 'a)))
   (cons (r2 'equal (r2 'equal (r1 'flatten (rv 'x)) (r2 'cons (rv 'y) (r0 'nil)))
                  (r2 'and (r1 'nlistp (rv 'x)) (r2 'equal (rv 'x) (rv 'y))))
   (cons (r2 'equal (r1 'listp (r1 'gopher (rv 'x)))
                  (r1 'listp (rv 'x)))
   (cons (r2 'equal (r2 'samefringe (rv 'x) (rv 'y))
                  (r2 'equal (r1 'flatten (rv 'x)) (r1 'flatten (rv 'y))))
   (cons (r2 'equal (r2 'equal (r2 'greatest-factor (rv 'x) (rv 'y)) (r0 'zero))
                  (r2 'and (r2 'or (r1 'zerop (rv 'y)) (r2 'equal (rv 'y) (rn 1))) (r2 'equal (rv 'x) (r0 'zero))))
   (cons (r2 'equal (r2 'equal (r2 'greatest-factor (rv 'x) (rv 'y)) (rn 1))
                  (r2 'equal (rv 'x) (rn 1)))
   (cons (r2 'equal (r1 'numberp (r2 'greatest-factor (rv 'x) (rv 'y)))
                  (r1 'not (r2 'and (r2 'or (r1 'zerop (rv 'y)) (r2 'equal (rv 'y) (rn 1))) (r1 'not (r1 'numberp (rv 'x))))))
   (cons (r2 'equal (r1 'times-list (r2 'append (rv 'x) (rv 'y)))
                  (r2 'times (r1 'times-list (rv 'x)) (r1 'times-list (rv 'y))))
   (cons (r2 'equal (r1 'prime-list (r2 'append (rv 'x) (rv 'y)))
                  (r2 'and (r1 'prime-list (rv 'x)) (r1 'prime-list (rv 'y))))
   (cons (r2 'equal (r2 'equal (rv 'z) (r2 'times (rv 'w) (rv 'z)))
                  (r2 'and (r1 'numberp (rv 'z)) (r2 'or (r2 'equal (rv 'z) (r0 'zero)) (r2 'equal (rv 'w) (rn 1)))))
   (cons (r2 'equal (r2 'greatereqp (rv 'x) (rv 'y))
                  (r1 'not (r2 'lessp (rv 'x) (rv 'y))))
   (cons (r2 'equal (r2 'equal (rv 'x) (r2 'times (rv 'x) (rv 'y)))
                  (r2 'or (r2 'equal (rv 'x) (r0 'zero)) (r2 'and (r1 'numberp (rv 'x)) (r2 'equal (rv 'y) (rn 1)))))
   (cons (r2 'equal (r2 'remainder (r2 'times (rv 'y) (rv 'x)) (rv 'y))
                  (r0 'zero))
   (cons (r2 'equal (r2 'equal (r2 'times (rv 'a) (rv 'b)) (rn 1))
                  (ra 'and (cons (r1 'not (r2 'equal (rv 'a) (r0 'zero))) (cons (r1 'not (r2 'equal (rv 'b) (r0 'zero))) (cons (r1 'numberp (rv 'a)) (cons (r1 'numberp (rv 'b)) (cons (r2 'equal (r1 '_1- (rv 'a)) (r0 'zero)) (cons (r2 'equal (r1 '_1- (rv 'b)) (r0 'zero)) nil))))))))
   (cons (r2 'equal (r2 'lessp (r1 'length (r2 'delete (rv 'x) (rv 'l))) (r1 'length (rv 'l)))
                  (r2 'member (rv 'x) (rv 'l)))
   (cons (r2 'equal (r1 'sort2 (r2 'delete (rv 'x) (rv 'l)))
                  (r2 'delete (rv 'x) (r1 'sort2 (rv 'l))))
   (cons (r2 'equal (r1 'dsort (rv 'x))
                  (r1 'sort2 (rv 'x)))
   (cons (r2 'equal (r1 'length (r2 'cons (rv 'x1) (r2 'cons (rv 'x2) (r2 'cons (rv 'x3) (r2 'cons (rv 'x4) (r2 'cons (rv 'x5) (r2 'cons (rv 'x6) (rv 'x7))))))))
                  (r2 'plus (rn 6) (r1 'length (rv 'x7))))
   (cons (r2 'equal (r2 'difference (r1 'add1 (r1 'add1 (rv 'x))) (rn 2))
                  (r1 'fix (rv 'x)))
   (cons (r2 'equal (r2 'quotient (r2 'plus (rv 'x) (r2 'plus (rv 'x) (rv 'y))) (rn 2))
                  (r2 'plus (rv 'x) (r2 'quotient (rv 'y) (rn 2))))
   (cons (r2 'equal (r2 'sigma (r0 'zero) (rv 'i))
                  (r2 'quotient (r2 'times (rv 'i) (r1 'add1 (rv 'i))) (rn 2)))
   (cons (r2 'equal (r2 'plus (rv 'x) (r1 'add1 (rv 'y)))
                  (r3 'if (r1 'numberp (rv 'y)) (r1 'add1 (r2 'plus (rv 'x) (rv 'y))) (r1 'add1 (rv 'x))))
   (cons (r2 'equal (r2 'equal (r2 'difference (rv 'x) (rv 'y)) (r2 'difference (rv 'z) (rv 'y)))
                  (r3 'if (r2 'lessp (rv 'x) (rv 'y)) (r1 'not (r2 'lessp (rv 'y) (rv 'z))) (r3 'if (r2 'lessp (rv 'z) (rv 'y)) (r1 'not (r2 'lessp (rv 'y) (rv 'x))) (r2 'equal (r1 'fix (rv 'x)) (r1 'fix (rv 'z))))))
   (cons (r2 'equal (r2 'meaning (r1 'plus-tree (r2 'delete (rv 'x) (rv 'y))) (rv 'a))
                  (r3 'if (r2 'member (rv 'x) (rv 'y)) (r2 'difference (r2 'meaning (r1 'plus-tree (rv 'y)) (rv 'a)) (r2 'meaning (rv 'x) (rv 'a))) (r2 'meaning (r1 'plus-tree (rv 'y)) (rv 'a))))
   (cons (r2 'equal (r2 'times (rv 'x) (r1 'add1 (rv 'y)))
                  (r3 'if (r1 'numberp (rv 'y)) (r2 'plus (rv 'x) (r2 'times (rv 'x) (rv 'y))) (r1 'fix (rv 'x))))
   (cons (r2 'equal (r2 'nth (r0 'nil) (rv 'i))
                  (r3 'if (r1 'zerop (rv 'i)) (r0 'nil) (r0 'zero)))
   (cons (r2 'equal (r1 'last (r2 'append (rv 'a) (rv 'b)))
                  (r3 'if (r1 'listp (rv 'b)) (r1 'last (rv 'b)) (r3 'if (r1 'listp (rv 'a)) (r2 'cons (r1 'car (r1 'last (rv 'a))) (rv 'b)) (rv 'b))))
   (cons (r2 'equal (r2 'equal (r2 'lessp (rv 'x) (rv 'y)) (rv 'z))
                  (r3 'if (r2 'lessp (rv 'x) (rv 'y)) (r2 'equal (r0 't) (rv 'z)) (r2 'equal (r0 'f) (rv 'z))))
   (cons (r2 'equal (r2 'assignment (rv 'x) (r2 'append (rv 'a) (rv 'b)))
                  (r3 'if (r2 'assignedp (rv 'x) (rv 'a)) (r2 'assignment (rv 'x) (rv 'a)) (r2 'assignment (rv 'x) (rv 'b))))
   (cons (r2 'equal (r1 'car (r1 'gopher (rv 'x)))
                  (r3 'if (r1 'listp (rv 'x)) (r1 'car (r1 'flatten (rv 'x))) (r0 'zero)))
   (cons (r2 'equal (r1 'flatten (r1 'cdr (r1 'gopher (rv 'x))))
                  (r3 'if (r1 'listp (rv 'x)) (r1 'cdr (r1 'flatten (rv 'x))) (r2 'cons (r0 'zero) (r0 'nil))))
   (cons (r2 'equal (r2 'quotient (r2 'times (rv 'y) (rv 'x)) (rv 'y))
                  (r3 'if (r1 'zerop (rv 'y)) (r0 'zero) (r1 'fix (rv 'x))))
   (cons (r2 'equal (r2 'get (rv 'j) (r3 'set (rv 'i) (rv 'val) (rv 'mem)))
                  (r3 'if (r2 'eqp (rv 'j) (rv 'i)) (rv 'val) (r2 'get (rv 'j) (rv 'mem))))
   nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(define-type records (listof (pairof symbol symrec @heap) @heap))

; Association list of symbols and symbol-records.

(define *symbol-records-alist* (ref records @heap) (new nil))

(define* assq-record (subr (maxeff (read @heap) spin) (symbol records) (pairof symbol symrec @heap))
  (lambda (sym l)
    (cond ((null? l) nil)
          ((symbol=? sym (car (car l))) (car l))
          (else (assq-record sym (cdr l))))))

(define make-symbol-record (subr (alloc @heap) (symbol) symrec)
  (lambda (sym) (the symrec (make-bloblet 0 sym nil))))

(define put-lemmas! (subr (write @heap) (symrec terms) unit)
  (lambda (symbol-record lemmas) (bloblet-set! symbol-record 1 lemmas)))

(define get-lemmas (subr (read @heap) (symrec) terms)
  (lambda (symbol-record) (bloblet-ref symbol-record 1)))

(define get-name (subr (read @heap) (symrec) symbol)
  (lambda (symbol-record) (bloblet-ref symbol-record 0)))

;; Scheme's `eq?` of the two records: each symbol has one record.
(define symbol-record-equal? (subr (read @heap) (symrec symrec) bool)
  (lambda (r1 r2) (symbol=? (bloblet-ref r1 0) (bloblet-ref r2 0))))

(define* symbol->symbol-record (subr mutates (symbol) symrec)
  (lambda (sym)
    (let ((x (assq-record sym (get *symbol-records-alist*))))
      (if (not (null? x))
          (cdr x)
          (let ((r (make-symbol-record sym)))
            (set *symbol-records-alist*
                 (cons (cons sym r)
                       (get *symbol-records-alist*)))
            r)))))

(define* put (subr mutates (symbol symbol terms) unit)
  (lambda (sym property value)
    (put-lemmas! (symbol->symbol-record sym) value)))

(define* get-property (subr mutates (symbol symbol) terms)
  (lambda (sym property)
    (get-lemmas (symbol->symbol-record sym))))

; Translates a term by replacing its constructor symbols by symbol-records.

(define-rec
  (translate-term (subr (maxeff mutates (read (globals *symbol-records-alist* app assq-record make-symbol-record num symbol->symbol-record translate-args translate-term var))) (raw) term)
    (lambda (term)
      (tagcase term
        (rv (s) (var s))
        (rn (n) (num n))
        (ra (f args) (app (symbol->symbol-record f)
                          (translate-args args))))))
  (translate-args (subr (maxeff mutates (read (globals *symbol-records-alist* app assq-record make-symbol-record num symbol->symbol-record translate-args translate-term var))) (raws) terms)
    (lambda (lst)
      (cond ((null? lst)
             nil)
            (else (cons (translate-term (car lst))
                        (translate-args (cdr lst))))))))

(define* add-lemma (subr mutates (raw) unit)
  (lambda (term)
    (tagcase term
      (ra (f args)
        (if (and (symbol=? f 'equal) (not (null? args)))
            (tagcase (car args)
              (ra (g gargs)
                (put g
                     'lemmas
                     (cons (translate-term term)
                           (get-property g 'lemmas))))
              ;; (error #f "ADD-LEMMA did not like term:  " term)
              (else x #u))
            #u))
      (else x #u))))

(define* add-lemma-lst (subr mutates (raws) bool)
  (lambda (lst)
    (cond ((null? lst)
           #t)
          (else (add-lemma (car lst))
                (add-lemma-lst (cdr lst))))))

(define* setup (subr mutates () bool)
  (lambda () (add-lemma-lst lemmas)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; The second phase.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type subst (listof (pairof symbol term @heap) @heap))

(define* assq-subst (subr (maxeff (read @heap) spin) (symbol subst) (pairof symbol term @heap))
  (lambda (sym l)
    (cond ((null? l) nil)
          ((symbol=? sym (car (car l))) (car l))
          (else (assq-subst sym (cdr l))))))

(define* translate-alist (subr mutates ((listof (pairof symbol raw @heap) @heap)) subst)
  (lambda (alist)
    (cond ((null? alist)
           nil)
          (else (cons (cons (car (car alist))
                            (translate-term (cdr (car alist))))
                      (translate-alist (cdr alist)))))))

(define-rec
  (apply-subst (subr (maxeff mutates (read (globals apply-subst apply-subst-lst assq-subst app))) (subst term) term)
    (lambda (alist term)
      (tagcase term
        (var (s)
          (let ((temp-temp (assq-subst s alist)))
            (if (not (null? temp-temp))
                (cdr temp-temp)
                term)))
        (app (f args) (app f (apply-subst-lst alist args)))
        (else x term))))
  (apply-subst-lst (subr (maxeff mutates (read (globals apply-subst apply-subst-lst assq-subst app))) (subst terms) terms)
    (lambda (alist lst)
      (cond ((null? lst)
             nil)
            (else (cons (apply-subst alist (car lst))
                        (apply-subst-lst alist (cdr lst))))))))

;; The global state of the second phase.
(define if-constructor (ref symrec @heap) (new (make-symbol-record '*))) ; becomes (symbol->symbol-record 'if)
(define rewrite-count (ref int @heap) (new 0)) ; sanity check
(define unify-subst (ref subst @heap) (new nil))
(define false-term (ref term @heap) (new (var '*)))  ; becomes (translate-term '(f))
(define true-term (ref term @heap) (new (var '*)))   ; becomes (translate-term '(t))

; Translated terms can be circular structures, which can't be
; compared using Scheme's equal? and member procedures, so we
; use these instead.

(define-rec
  (term-equal? (subr (maxeff (read @heap) spin (read (globals term-equal? term-args-equal? symbol-record-equal?))) (term term) bool)
    (lambda (x y)
      (tagcase x
        (app (xf xargs)
          (tagcase y
            (app (yf yargs)
              (and (symbol-record-equal? xf yf)
                   (term-args-equal? xargs yargs)))
            (else y #f)))
        ;; (equal? x y) of atoms
        (var (xs) (tagcase y (var (ys) (symbol=? xs ys)) (else y #f)))
        (num (xn) (tagcase y (num (yn) (= xn yn)) (else y #f))))))
  (term-args-equal? (subr (maxeff (read @heap) spin (read (globals term-equal? term-args-equal? symbol-record-equal?))) (terms terms) bool)
    (lambda (lst1 lst2)
      (cond ((null? lst1)
             (null? lst2))
            ((null? lst2)
             #f)
            ((term-equal? (car lst1) (car lst2))
             (term-args-equal? (cdr lst1) (cdr lst2)))
            (else #f)))))

(define* term-member? (subr (maxeff (read @heap) spin) (term terms) bool)
  (lambda (x lst)
    (cond ((null? lst)
           #f)
          ((term-equal? x (car lst))
           #t)
          (else (term-member? x (cdr lst))))))

(define* falsep (subr (maxeff (read @heap) spin) (term terms) bool)
  (lambda (x lst)
    (or (term-equal? x (get false-term))
        (term-member? x lst))))

(define* truep (subr (maxeff (read @heap) spin) (term terms) bool)
  (lambda (x lst)
    (or (term-equal? x (get true-term))
        (term-member? x lst))))

;; `(cadr x)`, `(caddr x)` and `(cadddr x)` of a term that is a pair.
(define term-cadr (subr (read @heap) (term) term)
  (lambda (x) (tagcase x (app (f args) (car args)) (else y y))))
(define term-caddr (subr (read @heap) (term) term)
  (lambda (x) (tagcase x (app (f args) (car (cdr args))) (else y y))))
(define term-cadddr (subr (read @heap) (term) term)
  (lambda (x) (tagcase x (app (f args) (car (cdr (cdr args)))) (else y y))))

(define* tautologyp (subr mutates (term terms terms) bool)
  (lambda (x true-lst false-lst)
    (cond ((truep x true-lst)
           #t)
          ((falsep x false-lst)
           #f)
          (else
           (tagcase x
             (app (f args)
               (if (symbol-record-equal? f (get if-constructor))
                   (cond ((truep (term-cadr x)
                                 true-lst)
                          (tautologyp (term-caddr x)
                                      true-lst false-lst))
                         ((falsep (term-cadr x)
                                  false-lst)
                          (tautologyp (term-cadddr x)
                                      true-lst false-lst))
                         (else (and (tautologyp (term-caddr x)
                                                (cons (term-cadr x)
                                                      true-lst)
                                                false-lst)
                                    (tautologyp (term-cadddr x)
                                                true-lst
                                                (cons (term-cadr x)
                                                      false-lst)))))
                   #f))
             ;; (not (pair? x))
             (else y #f))))))

(define-rec
  (one-way-unify1 (subr (maxeff mutates (read (globals assq-subst one-way-unify1 one-way-unify1-lst symbol-record-equal? term-args-equal? term-equal? unify-subst))) (term term) bool)
    (lambda (term1 term2)
      (tagcase term2
        (var (s)
          (let ((temp-temp (assq-subst s (get unify-subst))))
            (cond ((not (null? temp-temp))
                   (term-equal? term1 (cdr temp-temp)))
                  (else
                   (set unify-subst (cons (cons s term1)
                                          (get unify-subst)))
                   #t))))
        (num (n)                        ; This bug fix makes
          (tagcase term1                ; nboyer 10-25% slower!
            (num (m) (= m n))
            (else y #f)))
        (app (f2 args2)
          (tagcase term1
            (app (f1 args1)
              (if (symbol-record-equal? f1 f2)
                  (one-way-unify1-lst args1 args2)
                  #f))
            (else y #f))))))
  (one-way-unify1-lst (subr (maxeff mutates (read (globals assq-subst one-way-unify1 one-way-unify1-lst symbol-record-equal? term-args-equal? term-equal? unify-subst))) (terms terms) bool)
    (lambda (lst1 lst2)
      (cond ((null? lst1)
             (null? lst2))
            ((null? lst2)
             #f)
            ((one-way-unify1 (car lst1)
                             (car lst2))
             (one-way-unify1-lst (cdr lst1)
                                 (cdr lst2)))
            (else #f)))))

(define* one-way-unify (subr mutates (term term) bool)
  (lambda (term1 term2)
    (begin (set unify-subst nil)
           (one-way-unify1 term1 term2))))

(define-rec
  (rewrite (subr (maxeff mutates (read (globals app apply-subst apply-subst-lst assq-subst get-lemmas one-way-unify one-way-unify1 one-way-unify1-lst rewrite rewrite-args rewrite-count rewrite-with-lemmas symbol-record-equal? term-args-equal? term-caddr term-cadr term-equal? unify-subst))) (term) term)
    (lambda (term)
      (set rewrite-count (+ (get rewrite-count) 1))
      (tagcase term
        (app (f args)
          (rewrite-with-lemmas (app f
                                    (rewrite-args args))
                               (get-lemmas f)))
        (else x term))))
  (rewrite-args (subr (maxeff mutates (read (globals app apply-subst apply-subst-lst assq-subst get-lemmas one-way-unify one-way-unify1 one-way-unify1-lst rewrite rewrite-args rewrite-count rewrite-with-lemmas symbol-record-equal? term-args-equal? term-caddr term-cadr term-equal? unify-subst))) (terms) terms)
    (lambda (lst)
      (cond ((null? lst)
             nil)
            (else (cons (rewrite (car lst))
                        (rewrite-args (cdr lst)))))))
  (rewrite-with-lemmas (subr (maxeff mutates (read (globals app apply-subst apply-subst-lst assq-subst get-lemmas one-way-unify one-way-unify1 one-way-unify1-lst rewrite rewrite-args rewrite-count rewrite-with-lemmas symbol-record-equal? term-args-equal? term-caddr term-cadr term-equal? unify-subst))) (term terms) term)
    (lambda (term lst)
      (cond ((null? lst)
             term)
            ((one-way-unify term (term-cadr (car lst)))
             (rewrite (apply-subst (get unify-subst) (term-caddr (car lst)))))
            (else (rewrite-with-lemmas term (cdr lst)))))))

(define* tautp (subr mutates (term) bool)
  (lambda (x)
    (tautologyp (rewrite x)
                nil nil)))

(define* test (subr mutates ((listof (pairof symbol raw @heap) @heap) raw int) bool)
  (lambda (alist term n)
    (letrec ((loop (subr (maxeff mutates (read (globals r0 r2 ra))) (raw int) raw)
                   (lambda (term n)
                     (if (= n 0)
                         term
                         (loop (r2 'or term (r0 'f)) (- n 1))))))
      (let ((term
             (apply-subst
              (translate-alist alist)
              (translate-term
               (loop term n)))))
        (tautp term)))))

(define* setup-boyer (subr mutates () bool)
  (lambda ()
    (set *symbol-records-alist* nil)
    (set if-constructor (symbol->symbol-record 'if))
    (set false-term (translate-term (r0 'f)))
    (set true-term  (translate-term (r0 't)))
    (setup)))

(define* test-boyer (subr mutates ((listof (pairof symbol raw @heap) @heap) raw int) int)
  (lambda (alist term n)
    (set rewrite-count 0)
    (let ((answer (test alist term n)))
      (if answer
          (get rewrite-count)
          -1))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input int 5)
(define iterations int 1)

(define* run (subr mutates (int int) int)
  (lambda (i result)
    (if (= i 0)
        result
        (run (- i 1) (begin (setup-boyer) (test-boyer alist term input))))))
(run iterations 0)
