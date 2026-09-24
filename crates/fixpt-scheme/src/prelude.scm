;;; The fixpt prelude.
;;;
;;; Everything here could have been a primitive and deliberately is not. Two
;;; groups are worth pointing at:
;;;
;;; * `call/cc`, `dynamic-wind`, prompts, continuation marks,
;;;   `with-exception-handler`, `raise` and `raise-continuable`: the engine
;;;   provides raw mechanism that knows nothing about winding or handlers, and
;;;   the discipline is expressed here, in Scheme, where it is short enough to
;;;   check against R7RS and SRFI 226 by eye.
;;;
;;; * `map`, `for-each`, `assoc`, `member` and the `caar` family are ordinary
;;;   list code. Written here they automatically get proper tail calls and
;;;   behave correctly under `call/cc`; written in Rust each would need that
;;;   argued separately.

;;; ------------------------------------------------------------------ lists

(define (caar p) (car (car p)))
(define (cadr p) (car (cdr p)))
(define (cdar p) (cdr (car p)))
(define (cddr p) (cdr (cdr p)))
(define (caaar p) (car (caar p)))
(define (caadr p) (car (cadr p)))
(define (cadar p) (car (cdar p)))
(define (caddr p) (car (cddr p)))
(define (cdaar p) (cdr (caar p)))
(define (cdadr p) (cdr (cadr p)))
(define (cddar p) (cdr (cdar p)))
(define (cdddr p) (cdr (cddr p)))
(define (cadddr p) (car (cdddr p)))
(define (cddddr p) (cdr (cdddr p)))

(define (list? x)
  ;; Tortoise and hare, so a circular list answers #f instead of looping.
  (let loop ((slow x) (fast x))
    (cond ((null? fast) #t)
          ((not (pair? fast)) #f)
          ((null? (cdr fast)) #t)
          ((not (pair? (cdr fast))) #f)
          ((eq? (cdr fast) slow) #f)
          (else (loop (cdr slow) (cddr fast))))))

(define (list-tail lst k)
  (if (= k 0) lst (list-tail (cdr lst) (- k 1))))

(define (list-ref lst k) (car (list-tail lst k)))

(define (list-copy lst)
  (if (pair? lst) (cons (car lst) (list-copy (cdr lst))) lst))

(define (last-pair lst)
  (if (pair? (cdr lst)) (last-pair (cdr lst)) lst))

(define (memq x lst)
  (cond ((null? lst) #f)
        ((eq? x (car lst)) lst)
        (else (memq x (cdr lst)))))

(define (memv x lst)
  (cond ((null? lst) #f)
        ((eqv? x (car lst)) lst)
        (else (memv x (cdr lst)))))

(define (member x lst . compare)
  (let ((same? (if (null? compare) equal? (car compare))))
    (let loop ((l lst))
      (cond ((null? l) #f)
            ((same? x (car l)) l)
            (else (loop (cdr l)))))))

(define (assq x alist)
  (cond ((null? alist) #f)
        ((eq? x (caar alist)) (car alist))
        (else (assq x (cdr alist)))))

(define (assv x alist)
  (cond ((null? alist) #f)
        ((eqv? x (caar alist)) (car alist))
        (else (assv x (cdr alist)))))

(define (assoc x alist . compare)
  (let ((same? (if (null? compare) equal? (car compare))))
    (let loop ((l alist))
      (cond ((null? l) #f)
            ((same? x (caar l)) (car l))
            (else (loop (cdr l)))))))

(define (map f lst . rest)
  (if (null? rest)
      (let loop ((l lst))
        (if (null? l) '() (cons (f (car l)) (loop (cdr l)))))
      (let loop ((ls (cons lst rest)))
        (if (%any-null? ls)
            '()
            (cons (apply f (%heads ls)) (loop (%tails ls)))))))

(define (for-each f lst . rest)
  (if (null? rest)
      (let loop ((l lst))
        (if (pair? l) (begin (f (car l)) (loop (cdr l)))))
      (let loop ((ls (cons lst rest)))
        (if (not (%any-null? ls))
            (begin (apply f (%heads ls)) (loop (%tails ls)))))))

(define (%any-null? ls)
  (cond ((null? ls) #f)
        ((null? (car ls)) #t)
        (else (%any-null? (cdr ls)))))
(define (%heads ls) (if (null? ls) '() (cons (caar ls) (%heads (cdr ls)))))
(define (%tails ls) (if (null? ls) '() (cons (cdar ls) (%tails (cdr ls)))))

;;; -------------------------------------------------------------- numbers

(define (zero? n) (= n 0))
(define (positive? n) (> n 0))
(define (negative? n) (< n 0))
(define (even? n) (= (remainder n 2) 0))
(define (odd? n) (not (even? n)))
(define (1+ n) (+ n 1))
(define (max first . rest)
  (let loop ((best first) (l rest))
    (if (null? l) best (loop (if (> (car l) best) (car l) best) (cdr l)))))
(define (min first . rest)
  (let loop ((best first) (l rest))
    (if (null? l) best (loop (if (< (car l) best) (car l) best) (cdr l)))))
(define (lcm . ns)
  (let loop ((acc 1) (l ns))
    (if (null? l)
        acc
        (let ((n (abs (car l))))
          (loop (if (= n 0) 0 (quotient (* acc n) (gcd acc n))) (cdr l))))))
(define (exact->inexact x) (inexact x))
(define (inexact->exact x) (exact x))
(define (square x) (* x x))
(define (numerator q) (if (exact? q) (%numerator q) (inexact (%numerator (exact q)))))
(define (denominator q) (if (exact? q) (%denominator q) (inexact (%denominator (exact q)))))

;;; -------------------------------------------------------------- equality

(define (boolean=? a b . rest)
  (and (eq? a b) (or (null? rest) (apply boolean=? b rest))))
(define (symbol=? a b . rest)
  (and (eq? a b) (or (null? rest) (apply symbol=? b rest))))
(define (char=? a b . rest)
  (and (= (char->integer a) (char->integer b))
       (or (null? rest) (apply char=? b rest))))
(define (char<? a b . rest)
  (and (< (char->integer a) (char->integer b))
       (or (null? rest) (apply char<? b rest))))
(define (char>? a b . rest)
  (and (> (char->integer a) (char->integer b))
       (or (null? rest) (apply char>? b rest))))
(define (char<=? a b . rest)
  (and (<= (char->integer a) (char->integer b))
       (or (null? rest) (apply char<=? b rest))))
(define (char>=? a b . rest)
  (and (>= (char->integer a) (char->integer b))
       (or (null? rest) (apply char>=? b rest))))

;;; ------------------------------------------------- strings and vectors

(define (string-copy s . rest)
  (let* ((len (string-length s))
         (start (if (null? rest) 0 (car rest)))
         (end (if (or (null? rest) (null? (cdr rest))) len (cadr rest))))
    (substring s start end)))

(define (vector-copy v . rest)
  (let* ((len (vector-length v))
         (start (if (null? rest) 0 (car rest)))
         (end (if (or (null? rest) (null? (cdr rest))) len (cadr rest)))
         (out (make-vector (- end start))))
    (let loop ((i start))
      (if (< i end)
          (begin (vector-set! out (- i start) (vector-ref v i)) (loop (+ i 1)))
          out))))

(define (vector-append . vs)
  (list->vector (apply append (map vector->list vs))))

(define (vector-map f v . rest)
  (list->vector (apply map f (vector->list v) (map vector->list rest))))

(define (vector-for-each f v . rest)
  (apply for-each f (vector->list v) (map vector->list rest)))

(define (string-map f s . rest)
  (list->string (apply map f (string->list s) (map string->list rest))))

(define (string-for-each f s . rest)
  (apply for-each f (string->list s) (map string->list rest)))

(define (string->vector s) (list->vector (string->list s)))
(define (vector->string v) (list->string (vector->list v)))

;;; ----------------------------------------------------------- promises

(define (force p)
  (if (not (promise? p))
      p
      (let ((state (%promise-state p)))
        (cond
          ((= state 1) (%promise-value p))
          (else
           (let ((v ((%promise-value p))))
             (if (= (%promise-state p) 1)
                 ;; A re-entrant force already produced the value; R7RS says
                 ;; the first one wins.
                 (%promise-value p)
                 (let ((r (if (= state 2) (force v) v)))
                   (%promise-set-forced! p r)
                   r))))))))

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

;;; ------------------------------------------------------------ utilities

(define (void . ignored) (if #f #f))
