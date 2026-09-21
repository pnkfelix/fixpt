#lang racket/base
;;; fixpt conformance golden generator -- FX-87.
;;;
;;; Drives GiffordHistory's ported reference implementation
;;; (fx-lang/fx87/private/impl.rkt) the way erase.lisp's own TOP-LEVEL does
;;; for an ordinary expression -- PARSE-EXP then DESC-OF-EXP -- and prints
;;; the resulting (type . effect) through the same CREATE-FINITE-DEXP +
;;; UNPARSE-D-NODE pipeline SHOW-TYPE-AND-EFFECT uses.  CREATE-FINITE-DEXP
;;; is not optional: FX-87 builds genuinely CIRCULAR type structures with
;;; SET-CAR!, and it is what re-finitises them into DLETREC form.
;;;
;;; VALUES come from a second source.  The FX-87 port installs no evaluator
;;; (machdep.rkt's FX-EVAL-HOOK errors by design), so each well-typed form is
;;; also written to a temporary `#lang fx87-hashlang` module and run -- the
;;; archive's evaluating path, and the one its own test-cross-validate.rkt
;;; uses.  That path shares the checker with impl.rkt but has its own pair
;;; conversion, hygiene handling and runtime primitives, so a value produced
;;; there is evidence about the language rather than a restatement of the
;;; type.
;;;
;;; This makes regeneration slow -- one Racket module compile per case -- which
;;; is why the goldens are committed and this script is run deliberately.
;;;
;;; Usage: racket fx87-golden.rkt <input.fx-cases> <output.expected>

(require racket/port racket/file racket/string racket/sandbox "common.rkt")

(define ref (make-ref 'fx87))
(define parse-exp            (ref 'parse-exp))
(define desc-of-exp          (ref 'desc-of-exp))
(define initialize-top-level (ref 'initialize-top-level))
(define reset-user-error!    (ref 'fx-reset-user-error!))
(define create-finite-dexp   (ref 'create-finite-dexp))
(define unparse-d-node       (ref 'unparse-d-node))
(define desc->type           (ref 'desc->type))
(define desc->effect         (ref 'desc->effect))

(define-values (in-file out-file)
  (let ([a (current-command-line-arguments)])
    (unless (= 2 (vector-length a))
      (error 'fx87-golden "usage: fx87-golden.rkt <input.fx> <output.expected>"))
    (values (vector-ref a 0) (vector-ref a 1))))

;; FX-87 source folds symbol case and reads #t/#f/#u as SYMBOLS -- see
;; fx87-hashlang/lang/reader.rkt for the full rationale.
(define (dispatch str) (lambda (ch port src line col pos) (string->symbol str)))
(define fx87-readtable
  (make-readtable (current-readtable)
                  #\u 'dispatch-macro (dispatch "#u")
                  #\t 'dispatch-macro (dispatch "#t")
                  #\f 'dispatch-macro (dispatch "#f")))

(define (read-forms path)
  (parameterize ([read-case-sensitive #f] [current-readtable fx87-readtable])
    (call-with-input-file path
      (lambda (port)
        (let loop ([acc '()])
          (define d (read port))
          (if (eof-object? d) (reverse acc) (loop (cons d acc))))))))

(define (trim-error s)
  (define m (regexp-match #rx"(USER|FATAL) ERROR: *([^\n]*)" s))
  (normalize-space (if m (caddr m) s)))

;; (list 'ok type effect) | (list 'syntax-error msg) | (list 'type-error msg)
(define (check form)
  (initialize-top-level)
  (reset-user-error!)
  (define log (open-output-string))
  (with-handlers ([exn:fail? (lambda (e) (list 'type-error (normalize-space (exn-message e))))])
    (define node
      (parameterize ([current-output-port log])
        (parse-exp (deep->mutable form) (ref '*top-level-alpha-env*))))
    (cond
      [(ref '*user-error-seen*) (list 'syntax-error (trim-error (get-output-string log)))]
      [else
       (define desc
         (parameterize ([current-output-port log])
           (desc-of-exp node (ref '*top-level-tk-env*) (ref '*top-level-dstore*))))
       (if (and desc (not (eq? desc #f)) (not (ref '*user-error-seen*)))
           (list 'ok
                 (deep->immutable (unparse-d-node (create-finite-dexp (desc->type desc))))
                 (deep->immutable (unparse-d-node (create-finite-dexp (desc->effect desc)))))
           (list 'type-error (trim-error (get-output-string log))))])))

;; Run one form through `#lang fx87-hashlang` and return its printed value,
;; or #f if it does not produce one.  The module prints
;;   "  FORM\n      => DESC  (value: VAL)\n"
;; and we want only the VAL.
;;
;; Each case runs in a SEPARATE Racket process.  Sharing one turned out to
;; degrade badly: `#lang fx87-hashlang` calls into the very same impl.rkt
;; instance this script is driving, and after eighty-odd dynamically required
;; temporary modules the run wedged on a form that completes instantly on its
;; own.  A process per case costs a second and removes the whole class of
;; problem -- and it makes the deadline below real, since a subprocess can
;; simply be killed.
(define value-time-limit-seconds 25)
(define racket-exe (find-system-path 'exec-file))

(define (hashlang-value form)
  (define tmp (make-temporary-file "fixpt-fx87-~a.rkt"))
  (define result
    (with-handlers ([(lambda (e) #t) (lambda (e) #f)])
      (call-with-output-file tmp #:exists 'truncate
        (lambda (out)
          (displayln "#lang fx87-hashlang" out)
          (parameterize ([current-output-port out]) (write form))
          (newline out)))
      (define-values (proc stdout stdin stderr)
        (subprocess #f #f #f racket-exe (path->string tmp)))
      (define finished (sync/timeout value-time-limit-seconds proc))
      (unless finished (subprocess-kill proc #t))
      (define text (port->string stdout))
      (close-input-port stdout)
      (close-output-port stdin)
      (close-input-port stderr)
      (and finished
           ;; Bounded to one line: the module prints the value again on the
           ;; next, and `.` in a pregexp does match a newline, so an unbounded
           ;; match ran past the end of the record and captured both.
           (let ([m (regexp-match #px"\\(value: ([^\n]*)\\)" text)])
             (and m (string-trim (cadr m)))))))
  (with-handlers ([(lambda (e) #t) void]) (delete-file tmp))
  result)

(define (emit port n form)
  (define r (check form))
  (fprintf port "#case ~a\n" n)
  (fprintf port "#src ~s\n" form)
  (case (car r)
    [(ok)
     (fprintf port "#type ~s\n#effect ~s\n" (cadr r) (caddr r))
     ;; A well-typed form should also run. If the evaluating path cannot
     ;; produce a value -- a procedure, or a form it rejects for its own
     ;; reasons -- the case simply carries no #value and the Rust harness
     ;; counts it as having no dynamic golden rather than as a failure.
     (define v (hashlang-value form))
     (when v (fprintf port "#value ~s\n" v))]
    ;; One line per record: a message with a newline in it would otherwise
    ;; corrupt the format, and at least one case has one.
    [else      (fprintf port "#static-error ~s\n" (normalize-space (cadr r)))])
  (fprintf port "#end\n"))

(define forms (read-forms in-file))
(printf "fx87-golden: ~a forms from ~a\n" (length forms) in-file)
(call-with-output-file out-file #:exists 'truncate
  (lambda (port)
    (fprintf port ";;; fixpt FX-87 conformance goldens -- GENERATED, do not edit.\n")
    (fprintf port ";;; regenerate with: reference/regenerate.sh\n")
    (fprintf port ";;; source:    ~a\n" in-file)
    (fprintf port ";;; reference: GiffordHistory fx-lang/fx87/private/impl.rkt\n")
    (for ([f (in-list forms)] [n (in-naturals 1)]) (emit port n f))))
(printf "fx87-golden: wrote ~a\n" out-file)
