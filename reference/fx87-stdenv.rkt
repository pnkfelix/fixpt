#lang racket/base
;;; fixpt -- generate FX-87's standard environment from the reference.
;;;
;;; The 1987 standard environment is declared in impl.rkt as literal FX-87
;;; type syntax, in tables like *INT-INITIAL-T-ENV*, which *STANDARD-INITIAL-T-ENV*
;;; gathers and pairs each entry with the immutable region.  Rather than
;;; transcribe a few hundred subroutine types by hand -- which would make them
;;; my guesses rather than the reference's answers -- this reads the tables out
;;; of the live implementation and writes them as a source file the Rust
;;; front end parses with its own parser.
;;;
;;; The tables are compatlisp mutable pairs, so DEEP->IMMUTABLE is required
;;; before anything can be written.
;;;
;;; *STANDARD-* is not the whole environment: *INITIAL-T-ENV* adds the kernel
;;; bindings NEW, GET and SET (and the boolean operators) on top of it.  Those
;;; are handled separately below -- see the comment there.
;;;
;;; Usage: racket fx87-stdenv.rkt <output.fx>

(require racket/pretty "common.rkt")

;; The kernel additions, from *INITIAL-T-ENV* / *INITIAL-K-ENV* /
;; *INITIAL-DSTORE* (impl.rkt around line 7040).  These sit on top of the
;; *STANDARD-* tables and are quasiquoted source syntax there rather than a
;; reachable binding of their own -- *INITIAL-T-ENV* has already been through
;; PARSE-DEXP by the time it exists -- so they are copied verbatim rather than
;; read out.  Copied, not invented: every line below appears in impl.rkt.
(define kernel-t-env
  '((equiv? (subr pure (bool bool) bool))
    (and? (subr pure (bool bool) bool))
    (or? (subr pure (bool bool) bool))
    (not? (subr pure (bool) bool))
    (new (poly ((r region))
           (poly ((t type))
             (subr (alloc r) (t) (ref t r)))))
    (get (poly ((r region))
           (poly ((t type))
             (subr (read r) ((ref t r)) t))))
    (set (poly ((r region))
           (poly ((t type))
             (subr (write r) ((ref t r) t) unit))))))
(define kernel-k-env
  '((bool type)
    (unit type)
    (ref (dfunc (type region) type))))
(define kernel-dstore
  '((bool bool)
    (unit unit)
    (ref ref)))

(define ref (make-ref 'fx87))
(define t-env (deep->immutable (ref '*standard-initial-t-env*)))
(define k-env (deep->immutable (ref '*standard-initial-k-env*)))
(define dstore (deep->immutable (ref '*standard-initial-dstore*)))

(define out-file
  (let ([a (current-command-line-arguments)])
    (unless (= 1 (vector-length a))
      (error 'fx87-stdenv "usage: fx87-stdenv.rkt <output.fx>"))
    (vector-ref a 0)))

(with-output-to-file out-file #:exists 'replace
  (lambda ()
    (printf ";;; FX-87 standard environment -- GENERATED, do not edit.\n")
    (printf ";;; regenerate with: reference/regenerate.sh\n")
    (printf ";;; source: GiffordHistory fx-lang/fx87/private/impl.rkt\n")
    (printf ";;;   *standard-initial-t-env*  value bindings, each (name type region)\n")
    (printf ";;;   *standard-initial-k-env*  description bindings, each (name kind)\n")
    (printf ";;;   *standard-initial-dstore* description values, each (name desc)\n\n")
    (printf "(k-env\n")
    (for ([b (in-list kernel-k-env)])
      (printf " ")
      (write b)
      (newline))
    (for ([b (in-list k-env)])
      (printf " ")
      (write b)
      (newline))
    (printf ")\n\n(d-store\n")
    (for ([b (in-list kernel-dstore)])
      (printf " ")
      (write b)
      (newline))
    (for ([b (in-list dstore)])
      (printf " ")
      (write b)
      (newline))
    (printf ")\n\n(t-env\n")
    ;; The kernel bindings live in the immutable region, exactly as
    ;; *INITIAL-T-ENV* pairs them.
    (for ([b (in-list kernel-t-env)])
      (printf " ")
      (write (list (car b) (cadr b) '@=))
      (newline))
    (for ([b (in-list t-env)])
      ;; Each entry is (name (type region)); flatten to (name type region) so
      ;; the Rust side does not have to know about the extra nesting.
      (define name (car b))
      (define tr (cadr b))
      (printf " ")
      (write (list name (car tr) (cadr tr)))
      (newline))
    (printf ")\n")))

(printf "wrote ~a: ~a value bindings, ~a kinds, ~a description values\n"
        out-file
        (+ (length kernel-t-env) (length t-env))
        (+ (length kernel-k-env) (length k-env))
        (+ (length kernel-dstore) (length dstore)))
