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
;;; Values are not produced here.  The FX-87 port installs no evaluator
;;; (machdep.rkt's FX-EVAL-HOOK errors by design); `#lang fx87-hashlang` is
;;; the archive's evaluating path and is driven separately.
;;;
;;; Usage: racket fx87-golden.rkt <input.fx-cases> <output.expected>

(require racket/port "common.rkt")

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

(define (emit port n form)
  (define r (check form))
  (fprintf port "#case ~a\n" n)
  (fprintf port "#src ~s\n" form)
  (case (car r)
    [(ok)      (fprintf port "#type ~s\n#effect ~s\n" (cadr r) (caddr r))]
    [else      (fprintf port "#static-error ~s\n" (cadr r))])
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
