#lang racket/base
;;; Emit the built-in `fx` module's signature as FX-91 source.
;;;
;;; `create-initial-envs` (top.scm) builds it by splicing fifteen module
;;; declarations into one `moduleof`. Those declarations are plain quoted data
;;; in standard.scm, so the signature can be extracted rather than transcribed
;;; -- which removes a whole class of silent conformance failure, and means
;;; regenerating it is a reviewable diff like everything else here.
;;;
;;; Usage: racket fx91-stdmodule.rkt <output.fx>

(require racket/port racket/pretty "common.rkt")

(define out-file
  (let ([a (current-command-line-arguments)])
    (unless (= 1 (vector-length a))
      (error 'fx91-stdmodule "usage: fx91-stdmodule.rkt <output.fx>"))
    (vector-ref a 0)))

(define ref (make-ref 'fx91))

;; The exact splice order from top.scm's create-initial-envs. Order matters:
;; later declarations may mention earlier abstractions.
(define module-names
  '(effect-module bool-module unit-module refof-module int-module float-module
    char-module string-module sym-module permutation-module uniqueof-module
    listof-module vectorof-module sexp-module stream-module))

(define signature
  (cons 'moduleof
        (apply append (map (lambda (n) (deep->immutable (ref n))) module-names))))

(call-with-output-file out-file #:exists 'truncate
  (lambda (port)
    (fprintf port ";;; The built-in `fx` module's signature -- GENERATED, do not edit.\n")
    (fprintf port ";;; regenerate with: racket reference/fx91-stdmodule.rkt <out>\n")
    (fprintf port ";;; source: GiffordHistory fx-lang/fx91 standard.scm, spliced in\n")
    (fprintf port ";;; create-initial-envs order:\n")
    (fprintf port ";;;   ~a\n" module-names)
    (parameterize ([current-output-port port]
                   [pretty-print-columns 78])
      (pretty-write signature))))

(printf "fx91-stdmodule: wrote ~a (~a clauses)\n" out-file (length (cdr signature)))
