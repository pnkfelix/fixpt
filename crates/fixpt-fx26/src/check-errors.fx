;;; The checker, in FX-26: what its errors say, and where.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ errors
;; The error `m` at expression `x`.
(define k-fail-at (subr checks (string kx) void) (lambda (m x) (k-fail m (k-start x) (k-end x))))
;; The error `what` followed by type `t`, at `a`..`b`, or at expression `x`.
(define k-fail-ty (subr (maxeff checks spin) (string int int int) void)
  (lambda (what t a b) (k-fail (string-append what (k-show-ty t)) a b)))
(define k-fail-ty-at (subr (maxeff checks spin) (string int kx) void)
  (lambda (what t x) (k-fail-ty what t (k-start x) (k-end x))))
;; The error `what` followed by effect `e`, at `a`..`b`.
(define k-fail-effect (subr (maxeff checks spin) (string k-eff int int) void)
  (lambda (what e a b) (k-fail (string-append what (k-show-effect e)) a b)))
;; The error that a `plambda`'s body has effect `e`, at `a`..`b`.
(define k-fail-impure-plambda (subr (maxeff checks spin) (k-eff int int) void)
  (lambda (e a b)
    (k-fail-effect "a `plambda` body must be pure, and this one has " e a b)))
;; The error that a `t` has no `what` `l` (a part or a tag), at `a`..`b`.
(define k-fail-no-part (subr (maxeff checks spin) (int string symbol int int) void)
  (lambda (t what l a b)
    (k-fail (k-cat4 "a " (k-show-ty t) what (k-quote (symbol->string l))) a b)))
;; The error that a subroutine of `want` parameters is expected, and this `form` has `n`.
(define k-fail-arity (subr checks (int string int int int) void)
  (lambda (want form n a b)
    (k-fail (k-cat5 "a subroutine of " (int->string want) " parameter(s) is expected, and this `"
                    form (k-cat3 "` has " (int->string n) "")) a b)))
;; The error that a call has `got` arguments, where `want` are expected.
(define k-fail-arg-count (subr checks (int int int int) void)
  (lambda (want got a b)
    (k-fail (k-cat4 "expected " (int->string want) " argument(s), got " (int->string got)) a b)))
;; Why argument `i` (from 0), a `got`, will not do where a `want` is expected.
(define k-argument-error (subr (read @globals) (int string string) string)
  (lambda (i got want)
    (let ((n (int->string (+ i 1))))
      (k-cat5 "argument " n " is a " got (k-cat3 ", where a " want " is expected")))))
;; The error that argument `i` (from 0), `arg`, must be a `t`, not yet known.
(define k-fail-not-known (subr (maxeff checks spin) (kx int int) void)
  (lambda (arg i t)
    (let ((why (k-cat3 ", which is not yet known here; " "give the other arguments first, "
                       "or `proj` the operator")))
      (k-fail-at (k-cat5 "argument " (int->string (+ i 1)) " must be a " (k-show-ty t) why) arg))))
;; The error that `certify-length` is given a `t`, not a frozen list, at `x`.
(define k-fail-not-frozen (subr (maxeff checks spin) (int kx) void)
  (lambda (t x) (k-fail-ty-at "`certify-length` takes a frozen list, and this is a " t x)))
;; The error that `certify-acyclic` is given a `t`, which is not data, at `x`.
(define k-fail-not-data (subr (maxeff checks spin) (int kx) void)
  (lambda (t x)
    (k-fail-at (k-cat3 "`certify-acyclic` takes data, and a " (k-show-ty t) " is not data") x)))
;; The error that a bloblet of type `bt` cannot be changed, being frozen.
(define k-fail-frozen (subr (maxeff checks spin) (int int int) void)
  (lambda (bt a b)
    (k-fail (k-cat3 "a " (k-show-ty bt) " cannot be changed: its fields are frozen") a b)))
;; The error that a prompt's `body` has effect `beyond`, which the tag's `bound` does not allow.
(define k-fail-beyond (subr (maxeff checks spin) (kx k-eff k-eff) void)
  (lambda (body bound beyond)
    (k-fail-at (k-cat4 "the tag allows its delimited computations " (k-show-effect bound)
                       ", and this body also has " (k-show-effect beyond)) body)))
;; Why a `proj` giving descriptions `ds` does not fit a `poly` binding `bs`.
(define k-proj-count-error (subr (read @globals) (k-binders (listof k-desc acyclic)) string)
  (lambda (bs ds)
    (k-cat5 "this `poly` binds " (int->string (k-length bs)) " description(s); `proj` gave "
            (int->string (k-length ds)) "")))
;; What a prompt's body is, a `got`, where the tag's prompts deliver a `want`.
(define k-prompt-body-error (subr (read @globals) (string string) string)
  (lambda (want got) (k-cat4 "the tag's prompts deliver a " want ", and this body is a " got)))
;; What a handler is told, to take a `payload` to an `answer`; and what it gives instead, a `got`.
(define k-handler-wants (subr (maxeff kreads (alloc @t) spin) (int int) string)
  (lambda (payload answer)
    (k-cat4 "the handler must take a " (k-show-ty payload) " to a " (k-show-ty answer))))
(define k-handler-gives (subr (maxeff kreads (alloc @t) spin) (int int string) string)
  (lambda (payload answer got)
    (k-cat4 (k-handler-wants payload answer) ", and this gives a " got "")))
