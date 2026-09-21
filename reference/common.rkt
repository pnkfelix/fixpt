#lang racket/base
;;; Shared plumbing for the golden generators.
;;;
;;; The reference implementations live in a separate checkout, so they are
;;; reached with DYNAMIC-REQUIRE against a runtime-computed path rather than a
;;; static RELATIVE-IN -- that keeps the generators working wherever the two
;;; repositories sit relative to each other.
;;;
;;; DYNAMIC-REQUIRE is also the *correct* tool here for a second, less obvious
;;; reason: several of the bindings we need (*TK-ENV*, *INIT-TK-ENV*,
;;; *INIT-ALPHA-ENV*, ...) are module-level variables the reference SET!s at
;;; run time -- CREATE-INITIAL-ENVS assigns most of them.  Snapshotting them
;;; once at load time would capture the pre-initialisation value; `ref` below
;;; re-reads on every use instead.

(provide gifford-root impl-path make-ref deep->immutable deep->mutable
         normalize-space)

(require racket/mpair racket/string)

;; Override with FIXPT_GIFFORD when the archive is not a sibling checkout.
(define (gifford-root)
  (or (getenv "FIXPT_GIFFORD")
      (path->string
       (simplify-path
        (build-path (current-directory) 'up 'up "LangPlay" "GiffordHistory")))))

(define (impl-path which)  ; 'fx87 or 'fx91
  (build-path (gifford-root) "fx-lang" (symbol->string which) "private" "impl.rkt"))

;; (define ref (make-ref 'fx91))  then  (ref '*tk-env*)
(define (make-ref which)
  (define p (impl-path which))
  (unless (file-exists? p)
    (error 'fixpt-golden
           "reference implementation not found at ~a\n  set FIXPT_GIFFORD to the GiffordHistory checkout"
           p))
  (lambda (name) (dynamic-require p name)))

(define (deep->immutable x)
  (cond [(mpair? x) (cons (deep->immutable (mcar x)) (deep->immutable (mcdr x)))]
        [else x]))
(define (deep->mutable x)
  (cond [(pair? x) (mcons (deep->mutable (car x)) (deep->mutable (cdr x)))]
        [else x]))

(define (normalize-space s)
  (string-normalize-spaces (string-trim s)))
