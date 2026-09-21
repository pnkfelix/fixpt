;;; The fixpt prelude.
;;;
;;; Everything here could have been a primitive and deliberately is not. Two
;;; groups are worth pointing at:
;;;
;;; * `call/cc`, `dynamic-wind`, `with-exception-handler`, `raise` and
;;;   `raise-continuable` are Kent Dybvig's classic arrangement: the engine
;;;   provides a raw `%call/cc` that knows nothing about winding, and the
;;;   winding and handler discipline is expressed here, in Scheme, where it is
;;;   short enough to check against the report by eye.
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
;;; Dybvig's arrangement. `%call/cc` is the raw, winding-unaware primitive.

(define %winders '())

(define (%common-tail x y)
  (let ((lx (length x)) (ly (length y)))
    (let loop ((x (if (> lx ly) (list-tail x (- lx ly)) x))
               (y (if (> ly lx) (list-tail y (- ly lx)) y)))
      (if (eq? x y) x (loop (cdr x) (cdr y))))))

(define (%do-wind new)
  (let ((tail (%common-tail new %winders)))
    ;; Leaving: run `after` thunks from the inside out.
    (let unwind ((l %winders))
      (if (not (eq? l tail))
          (begin (set! %winders (cdr l))
                 ((cdar l))
                 (unwind (cdr l)))))
    ;; Entering: run `before` thunks from the outside in.
    (let rewind ((l new))
      (if (not (eq? l tail))
          (begin (rewind (cdr l))
                 ((caar l))
                 (set! %winders l))))))

(define (call-with-current-continuation f)
  (%call/cc
   (lambda (k)
     (f (let ((saved %winders))
          (lambda vals
            (if (not (eq? saved %winders)) (%do-wind saved))
            (apply k vals)))))))

(define call/cc call-with-current-continuation)

(define (dynamic-wind before thunk after)
  (before)
  (set! %winders (cons (cons before after) %winders))
  (let ((result (thunk)))
    (set! %winders (cdr %winders))
    (after)
    result))

;;; ---------------------------------------------------------- conditions

(define %handlers '())

(define (%with-handlers hs thunk)
  (let ((saved %handlers))
    (dynamic-wind
     (lambda () (set! %handlers hs))
     thunk
     (lambda () (set! %handlers saved)))))

(define (with-exception-handler handler thunk)
  (%with-handlers (cons handler %handlers) thunk))

(define (raise obj)
  (if (null? %handlers)
      (%raise-uncaught obj)
      ;; The handler and the outer list must be read BEFORE %with-handlers
      ;; rebinds %handlers -- otherwise the thunk would look up `car` on the
      ;; already-shortened list.
      (let ((handler (car %handlers)) (outer (cdr %handlers)))
        ;; The handler runs with itself removed, so a handler that raises does
        ;; not immediately re-enter itself.
        (%with-handlers outer (lambda () (handler obj)))
        ;; R7RS: a handler invoked by `raise` must not return.
        (%raise-uncaught obj))))

(define (raise-continuable obj)
  (if (null? %handlers)
      (%raise-uncaught obj)
      (let ((handler (car %handlers)) (outer (cdr %handlers)))
        (%with-handlers outer (lambda () (handler obj))))))

;;; ------------------------------------------------------------ utilities

(define (void . ignored) (if #f #f))
