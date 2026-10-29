;;; The prelude's control (`prelude.scm`): what every session needs,
;;; FX-26's runtime among them (`runtime.scm`), whatever runs its code.

;;; -------------------------------------------- continuations and winding
;;; SRFI 226's arrangement, on the engine's mark stack (`cmarks.rs`).
;;;
;;; A prompt, a `dynamic-wind` extent and an exception handler are each
;;; *attached to the continuation* rather than kept in a global. So capturing a
;;; continuation captures them, reinstating one reinstates them, and abandoning
;;; one discards them -- which is what makes an abandoned computation unable to
;;; leave a handler installed for whatever runs next. The engine supplies the
;;; mechanism (`%wcm`, `%prompt`, `%wind`, `%abort`, `%call/comp`, `%throw`);
;;; the policy -- which thunks run, in what order -- is written here.

(define-record-type %prompt-tag
  (%make-prompt-tag name)
  continuation-prompt-tag?
  (name %prompt-tag-name))

(define (make-continuation-prompt-tag . name)
  (%make-prompt-tag (if (pair? name) (car name) #f)))

(define %default-prompt-tag (make-continuation-prompt-tag 'default))
(define (default-continuation-prompt-tag) %default-prompt-tag)

;; The top level's own prompt. Holes and uncaught conditions abort to it; no
;; program has a reason to name it.
(define %toplevel-tag (make-continuation-prompt-tag 'toplevel))

(define (call-with-continuation-prompt thunk . rest)
  (let ((tag (if (pair? rest) (car rest) %default-prompt-tag))
        (handler (if (and (pair? rest) (pair? (cdr rest)))
                     (cadr rest)
                     (lambda (th) (th)))))
    ;; In argument position, so the prompt gets a frame of its own.
    (%prompt-result (%prompt tag handler thunk))))

(define (continuation-prompt-available? tag) (%prompt-available? tag))

(define (abort-current-continuation tag . vals)
  (%abort tag vals %abort-step))

;; One `dynamic-wind` extent left on the way out to a prompt. The engine has
;; already cut back to the extent's own frame, so `after` runs with exactly the
;; marks, handlers and outer extents that were live around the `dynamic-wind`.
(define (%abort-step after tag vals step)
  (after)
  (%abort tag vals step))

(define (call-with-composable-continuation f . tag)
  (%call/comp f (if (pair? tag) (car tag) %default-prompt-tag)))

(define (call-with-current-continuation f) (%call/cc f))
(define call/cc call-with-current-continuation)

(define (dynamic-wind before thunk after)
  (before)
  (let ((result (%wind (cons before after) thunk)))
    (after)
    result))

;; Every application of a continuation comes here first -- the engine calls
;; it -- so that leaving an extent runs its `after` and entering one runs its
;; `before`, before the continuation is reinstated raw by `%throw`. A full
;; continuation's extents are its own; a composable one's are added to the
;; ones already live where it is called.
(define (%continuation-apply k vals)
  (%wind-to (%current-winders)
            (if (%composable? k)
                (append (%continuation-winders k) (%current-winders))
                (%continuation-winders k)))
  (%throw k vals))

;; Both lists are innermost first and share their outermost extents.
(define (%wind-to from to)
  (let* ((shared (%shared-outer from to))
         (leaving (- (length from) shared))
         (entering (- (length to) shared)))
    (let unwind ((l from) (n leaving))
      (if (> n 0)
          (begin ((cdar l)) (unwind (cdr l) (- n 1)))))
    (let rewind ((l to) (n entering))
      (if (> n 0)
          (begin (rewind (cdr l) (- n 1)) ((caar l)))))))

(define (%shared-outer a b)
  (let loop ((a (reverse a)) (b (reverse b)) (n 0))
    (if (and (pair? a) (pair? b) (eq? (car a) (car b)))
        (loop (cdr a) (cdr b) (+ n 1))
        n)))

;;; ------------------------------------------------------ continuation marks

(define-record-type %mark-set
  (%make-mark-set pairs)
  continuation-mark-set?
  (pairs %mark-set-pairs))

(define (current-continuation-marks . tag)
  (%make-mark-set (%current-marks (if (pair? tag) (car tag) %default-prompt-tag))))

(define (continuation-marks k . tag)
  (%make-mark-set (%continuation-marks k (if (pair? tag) (car tag) %default-prompt-tag))))

(define (continuation-mark-set->list set key)
  (let loop ((l (%mark-set-pairs set)))
    (cond ((null? l) '())
          ((eq? (caar l) key) (cons (cdar l) (loop (cdr l))))
          (else (loop (cdr l))))))

(define (continuation-mark-set-first set key . rest)
  (let ((default (if (pair? rest) (car rest) #f))
        (tag (if (and (pair? rest) (pair? (cdr rest))) (cadr rest) %default-prompt-tag)))
    (if set
        (let ((l (continuation-mark-set->list set key)))
          (if (pair? l) (car l) default))
        (%first-mark key default tag))))

;;; ---------------------------------------------------------- conditions
;;; The handler stack is a continuation mark. Each mark holds the whole list,
;;; so installing a handler in tail position of another's thunk -- which
;;; replaces that frame's mark -- loses nothing.

(define %handler-key (list 'exception-handler))

(define (%handlers) (%first-mark %handler-key '() #f))

(define (with-exception-handler handler thunk)
  (%wcm %handler-key (cons handler (%handlers)) thunk))

(define (raise obj)
  (let ((hs (%handlers)))
    (if (null? hs)
        (%uncaught obj)
        (begin
          ;; The handler runs with itself removed, so a handler that raises
          ;; does not immediately re-enter itself.
          (%wcm %handler-key (cdr hs) (lambda () ((car hs) obj)))
          ;; R7RS: a handler invoked by `raise` must not return.
          (%uncaught obj)))))

(define (raise-continuable obj)
  (let ((hs (%handlers)))
    (if (null? hs)
        (%uncaught obj)
        (%wcm %handler-key (cdr hs) (lambda () ((car hs) obj))))))

;; Nothing will handle `obj`. Leave through the top level's prompt, so every
;; `after` thunk on the way out runs, and let the top level report it.
(define (%uncaught obj)
  (if (%prompt-available? %toplevel-tag)
      (abort-current-continuation %toplevel-tag (lambda () (%raise-uncaught obj)))
      (%raise-uncaught obj)))

;;; ------------------------------------------------------------- top level
;;; The session runs every top-level input through this. Two prompts: the
;;; default one, where `current-continuation-marks` and composable captures
;;; stop unless told otherwise, and inside it the top level's own, which holes
;;; and uncaught conditions abort to. The top level's is the *inner* one so that
;;; a hole captures the form and nothing of this machinery.

(define (%toplevel-run thunk)
  (call-with-continuation-prompt
   (lambda ()
     (call-with-continuation-prompt
      thunk
      %toplevel-tag
      (lambda (outcome) (if (procedure? outcome) (outcome) outcome))))))

;; `,resume` -- deliver a value to a held hole.
(define (%resume k v) (k v))

;;; ------------------------------------------------------ procedural macros
;;; SRFI 211's low-level transformers. The expander recognises the record,
;;; calls the procedure at each use, and answers `rename`, `inject` and
;;; `compare` itself: each is a `%host` request, which pauses this machine
;;; until the expander resumes it with the answer (`procmacro.rs`).

(define-record-type %transformer
  (%make-transformer kind proc)
  %transformer?
  (kind %transformer-kind)
  (proc %transformer-proc))

;; (lambda (form rename compare) ...): what the template inserts is renamed
;; by hand; anything left bare means what it means where the macro is used.
(define (er-macro-transformer f) (%make-transformer 'er f))

;; (lambda (form inject compare) ...): everything the template inserts is
;; renamed automatically; `inject` is how to capture on purpose.
(define (ir-macro-transformer f) (%make-transformer 'ir f))

(define (%macro-rename s) (%host 'rename s))
(define (%macro-inject s) (%host 'inject s))
(define (%macro-compare a b) (%host 'compare a b))

;; An IR transformer's input identifiers are marked -- `eq?` only to
;; themselves -- so that its output can be told apart from its template.
;; This gives back plain symbols, for code that wants to look at names.
(define (strip-syntax x)
  (cond ((symbol? x) (string->symbol (symbol->string x)))
        ((pair? x) (cons (strip-syntax (car x)) (strip-syntax (cdr x))))
        ((vector? x) (list->vector (strip-syntax (vector->list x))))
        (else x)))

;;; ------------------------------------------------------------ utilities

(define (void . ignored) (if #f #f))
