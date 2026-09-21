#lang racket/base
;;; fixpt conformance golden generator -- FX-91.
;;;
;;; Drives GiffordHistory's ported reference implementation the same way
;;; top.scm's own `fx91` REPL loop does -- reset the environments, PARSE-EXP,
;;; TYPE/EFFECT-OF-EXP, UNPARSE-DEXP, then CODE-OF-EXP + EVAL-SCHEME -- and
;;; emits one machine-readable record per top-level form.
;;;
;;; Unlike the reference's own FX91-CHECK, each form gets a fresh reset and its
;;; evaluation is guarded, so one failing form does not truncate the run.  That
;;; is why this produces all 182 records where FX91-CHECK stops at 168.
;;;
;;; Two evaluation results are recorded where they differ:
;;;   #value        what the unmodified reference produces
;;;   #value-aug    the same, but with CONS~/NIL~ bound.  sexp-module declares
;;;                 both (standard.scm:566+) and never ADD-RUN-TIMEs either, so
;;;                 the generated Scheme references an unbound variable.  That
;;;                 is an authentic 1991 archive bug, not a porting artifact --
;;;                 fx91-hashlang/runtime.rkt supplies the same two shims.
;;;                 Recording both keeps the bug visible instead of papering
;;;                 over it.
;;;
;;; Usage: racket fx91-golden.rkt <input.fx> <output.expected>

(require racket/mpair racket/port "common.rkt")

(define-values (in-file out-file)
  (let ([a (current-command-line-arguments)])
    (unless (= 2 (vector-length a))
      (error 'fx91-golden "usage: fx91-golden.rkt <input.fx> <output.expected>"))
    (values (vector-ref a 0) (vector-ref a 1))))

(define ref (make-ref 'fx91))

;; Procedures are stable, so they can be hoisted; the *VARIABLES* cannot (see
;; common.rkt) and are re-read through `ref` at each use.
(define parse-exp            (ref 'parse-exp))
(define type/effect-of-exp   (ref 'type/effect-of-exp))
(define values-type          (ref 'values-type))
(define values-effect        (ref 'values-effect))
(define unparse-dexp         (ref 'unparse-dexp))
(define code-of-exp          (ref 'code-of-exp))
(define run-time-bindings    (ref 'run-time-bindings))
(define eval-scheme          (ref 'eval-scheme))
(define set-variable-env!    (ref 'set-variable-env!))
(define reset-for-check!     (ref 'fx91-reset-for-check!))
(define install-restart!     (ref 'fx91-install-restart!))
(define error-signal         (ref 'error-signal))
(define fx91-readtable       (ref 'fx91-readtable))

;; The two primitives sexp-module declares but never binds; representation per
;; fx91-hashlang/runtime.rkt -- FX-91's LISTOF really is mutable-pair-based, so
;; "non-empty list" means MPAIR?.
(define (fx-cons~ x s f) (if (mpair? x) (s (mcar x) (mcdr x)) (f x)))
(define (fx-nil~  x s f) (if (mpair? x) (f x) (s)))

(define (read-forms path)
  (parameterize ([read-case-sensitive #f] [current-readtable fx91-readtable])
    (call-with-input-file path
      (lambda (port)
        (let loop ([acc '()])
          (define d (read port))
          (if (eof-object? d) (reverse acc) (loop (cons d acc))))))))

((ref 'fx91-set-display-typechecking!) #f)
(void (parameterize ([current-output-port (open-output-nowhere)])
        ((ref 'create-initial-envs))))

;; (list 'ok node type effect) | (cons 'static-error message)
(define (typecheck form)
  (set-variable-env! (ref '*tk-env*)     (ref '*init-tk-env*))
  (set-variable-env! (ref '*store*)      (ref '*init-store*))
  (set-variable-env! (ref '*select-env*) (ref '*init-select-env*))
  (reset-for-check!)
  (define log (open-output-string))
  (define r
    (with-handlers ([exn:fail? (lambda (e) (cons 'static-error (normalize-space (exn-message e))))])
      (call/cc
       (lambda (restart)
         (install-restart! restart)
         (parameterize ([current-output-port log])
           (define node ((parse-exp (ref '*init-alpha-env*)) (deep->mutable form)))
           (define t/e (type/effect-of-exp node))
           (list 'ok node
                 (deep->immutable (unparse-dexp (values-type t/e)))
                 (deep->immutable (unparse-dexp (values-effect t/e)))))))))
  (if (eq? r error-signal)
      (cons 'static-error (normalize-space (get-output-string log)))
      r))

(define (mlist . xs) (if (null? xs) '() (mcons (car xs) (apply mlist (cdr xs)))))

(define (evaluate node)
  (with-handlers ([(lambda (_) #t)
                   (lambda (e) (cons 'error (if (exn? e) (exn-message e) (format "~a" e))))])
    (define code
      (let loop ([res (code-of-exp node)] [bs (run-time-bindings)])
        (if (null? bs) res (loop (mlist 'let (mcar bs) res) (mcdr bs)))))
    (cons 'ok (parameterize ([current-output-port (open-output-nowhere)])
                (eval-scheme code)))))

(define (emit port n form res)
  (fprintf port "#case ~a\n#src ~s\n" n form)
  (cond
    [(and (pair? res) (eq? (car res) 'static-error))
     (fprintf port "#static-error ~s\n" (cdr res))]
    [else
     (fprintf port "#type ~s\n#effect ~s\n" (caddr res) (cadddr res))
     (define plain (evaluate (cadr res)))
     (fprintf port "#~a ~s\n"
              (if (eq? (car plain) 'ok) "value" "value-error")
              (format "~a" (deep->immutable (cdr plain))))
     (unless (eq? (car plain) 'ok)
       (namespace-set-variable-value! 'cons~ fx-cons~ #t (ref 'fx91-eval-namespace))
       (namespace-set-variable-value! 'nil~  fx-nil~  #t (ref 'fx91-eval-namespace))
       (define aug (evaluate (cadr res)))
       (fprintf port "#~a ~s\n"
                (if (eq? (car aug) 'ok) "value-aug" "value-aug-error")
                (format "~a" (deep->immutable (cdr aug)))))])
  (fprintf port "#end\n"))

(define forms (read-forms in-file))
(printf "fx91-golden: ~a forms from ~a\n" (length forms) in-file)

;; tests.fx's (load "tests.list.fx") resolves against the current directory.
(parameterize ([current-directory
                (let-values ([(d _f _r) (split-path (path->complete-path in-file))]) d)])
  (call-with-output-file out-file #:exists 'truncate
    (lambda (port)
      (fprintf port ";;; fixpt FX-91 conformance goldens -- GENERATED, do not edit.\n")
      (fprintf port ";;; regenerate with: reference/regenerate.sh\n")
      (fprintf port ";;; source:    ~a\n" in-file)
      (fprintf port ";;; reference: GiffordHistory fx-lang/fx91/private/impl.rkt\n")
      (for ([form (in-list forms)] [n (in-naturals 1)])
        (emit port n form (typecheck form))))))
(printf "fx91-golden: wrote ~a\n" out-file)
