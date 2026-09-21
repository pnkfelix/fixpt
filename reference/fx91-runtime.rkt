#lang racket/base
;;; List the built-in `fx` module's run-time bindings.
;;;
;;; `standard.scm` registers these with ADD-RUN-TIME, and `top.scm` wraps the
;;; generated code in a `let` over them. They are extracted rather than read off
;;; by eye so that nothing is missed: a name that has a declared *type* but no
;;; run-time binding is exactly the bug that stops the reference evaluating form
;;; 168 of its own test suite.
;;;
;;; Usage: racket fx91-runtime.rkt [output.txt]

(require "common.rkt")

(define ref (make-ref 'fx91))
(void ((ref 'fx91-set-display-typechecking!) #f))

(define bindings
  (for*/list ([group (in-list (deep->immutable ((ref 'run-time-bindings))))]
              [b (in-list group)])
    b))

(define out
  (if (> (vector-length (current-command-line-arguments)) 0)
      (open-output-file (vector-ref (current-command-line-arguments) 0)
                        #:exists 'truncate)
      (current-output-port)))

(fprintf out ";;; fx module run-time bindings -- GENERATED, do not edit.\n")
(fprintf out ";;; regenerate with: racket reference/fx91-runtime.rkt <out>\n")
(fprintf out ";;; source: GiffordHistory fx-lang/fx91 standard.scm, ADD-RUN-TIME\n")
(fprintf out ";;; count: ~a\n" (length bindings))
(for ([b (in-list (sort bindings string<? #:key (lambda (b) (format "~a" (car b)))))])
  (fprintf out "~s\n" b))
(unless (eq? out (current-output-port)) (close-output-port out))
(eprintf "fx91-runtime: ~a bindings\n" (length bindings))
