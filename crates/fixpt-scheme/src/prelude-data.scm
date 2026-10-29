;;; The prelude's data: lists, numbers, characters, strings and vectors,
;;; promises (`prelude.scm`). What lowered FX-26 and Scheme programs call;
;;; FX-26 compiled to words calls none of it (`PRELUDE_CONTROL`).

;;; ------------------------------------------------------------------ lists

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

;; R7RS 6.2.6's integer division: floor rounds the quotient toward -inf, so
;; the remainder has the divisor's sign (it is `modulo`); truncate rounds it
;; toward zero, so the remainder has the dividend's (it is `remainder`).
(define (floor-remainder n m) (modulo n m))
(define (floor-quotient n m) (quotient (- n (modulo n m)) m))
(define (floor/ n m) (values (floor-quotient n m) (floor-remainder n m)))
(define (truncate-quotient n m) (quotient n m))
(define (truncate-remainder n m) (remainder n m))
(define (truncate/ n m) (values (quotient n m) (remainder n m)))
;; The largest s with s*s <= k, and k - s*s: Newton's method on exact
;; integers, so right for bignums too.
(define (exact-integer-sqrt k)
  (if (not (and (exact-integer? k) (>= k 0)))
      (error "exact-integer-sqrt: not an exact non-negative integer" k))
  (let loop ((x k) (y (quotient (+ k 1) 2)))
    (if (>= y x)
        (values x (- k (* x x)))
        (loop y (quotient (+ y (quotient k y)) 2)))))
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

(define (string-downcase s) (list->string (map char-downcase (string->list s))))
(define (string-upcase s) (list->string (map char-upcase (string->list s))))
(define (string-foldcase s) (string-downcase s))
(define (string-ci=? a b . rest)
  (let loop ((a a) (b b) (rest rest))
    (and (string=? (string-foldcase a) (string-foldcase b))
         (or (null? rest) (loop b (car rest) (cdr rest))))))

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
