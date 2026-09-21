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
;;; Usage: racket fx87-stdenv.rkt <output.fx>

(require racket/pretty "common.rkt")

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
    (for ([b (in-list k-env)])
      (printf " ")
      (write b)
      (newline))
    (printf ")\n\n(d-store\n")
    (for ([b (in-list dstore)])
      (printf " ")
      (write b)
      (newline))
    (printf ")\n\n(t-env\n")
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
        out-file (length t-env) (length k-env) (length dstore))
