;;; VECSORT -- Vector sorting benchmark.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/vecsort.scm),
;;; ported to FX-26.
;;; Larceny's input: 1 iteration of (hash-then-sort chars), chars all
;;; Unicode characters from 0 to #x10ffff, surrogates skipped.
;;; Answer: #t (the sorted vector is equal to chars, Larceny's check).
;;;
;;; FX-26 has no (scheme sort): `vector-sort` is Larceny's own, from
;;; src/Lib/Common/sort.sch (which SRFI 132 in Larceny uses): the vector
;;; made a list, sorted in place by Richard A. O'Keefe's merge sort (after
;;; D.H.D. Warren), `sort!!` and `merge!!`, whose `seq` is a ref here, and
;;; made a vector again. Vectors are arrays; `length`, `vector->list` and
;;; `list->vector` are written out for characters.
;;; FX-26 has no `char<?`: it compares `char->integer`s. Nor `remainder`:
;;; `modulo`, the same for the non-negative scalar values here.
;;;
;;; Copyright 2007 William D Clinger.
;;;
;;; Permission to copy this software, in whole or in part, to use this
;;; software for any lawful purpose, and to redistribute this software
;;; is granted subject to the restriction that all copies made of this
;;; software must include this copyright notice in full.
;;;
;;; I also request that you send me a copy of any improvements that you
;;; make to this software so that they may be incorporated within it to
;;; the benefit of the Scheme community.

(define-type chars (listof char @heap))
(define-type charv (arrayof char @heap))
(define-type less (subr pure (char char) bool))
(define-effect lists (maxeff (read @heap) (write @heap) (alloc @heap) spin))

(define char<? less
  (lambda (c0 c1) (< (char->integer c0) (char->integer c1))))

(define hash<? less
  (lambda (c0 c1)
    (let ((hash (lambda ((c char))
                  (let* ((sv (char->integer c))
                         (h1 (quotient sv 1000))
                         (h2 (modulo sv 1000)))
                    (- sv (+ (* 1000 h2) h1))))))
      (< (hash c0) (hash c1)))))

;; Destructive merge of two sorted lists.
(define* merge!! (subr lists (chars chars less) chars)
  (lambda (a b less?)
    (letrec ((loop (subr lists (chars chars chars) unit)
               (lambda (r a b)
                 (if (less? (car b) (car a))
                     (begin (set-cdr! r b)
                            (if (null? (cdr b))
                                (set-cdr! b a)
                                (loop b a (cdr b))))
                     ;; (car a) <= (car b)
                     (begin (set-cdr! r a)
                            (if (null? (cdr a))
                                (set-cdr! a b)
                                (loop a (cdr a) b)))))))
      (cond ((null? a) b)
            ((null? b) a)
            ((less? (car b) (car a))
             (begin (if (null? (cdr b))
                        (set-cdr! b a)
                        (loop b a (cdr b)))
                    b))
            (else                       ; (car a) <= (car b)
             (begin (if (null? (cdr a))
                        (set-cdr! a b)
                        (loop a (cdr a) b))
                    a))))))

(define* chars-length (subr lists (chars) int)
  (lambda (xs)
    (letrec ((loop (subr lists (chars int) int)
               (lambda (xs n) (if (null? xs) n (loop (cdr xs) (+ n 1))))))
      (loop xs 0))))

;; Sort procedure which copies the input list and then sorts the
;; new list imperatively. Due to Richard O'Keefe; algorithm
;; attributed to D.H.D. Warren
(define* sort!! (subr lists (chars less) chars)
  (lambda (seq0 less?)
    (let ((seq (the (ref chars @heap) (new seq0))))
      (letrec ((step (subr (maxeff lists (read (globals merge!!))) (int) chars)
                 (lambda (n)
                   (cond ((> n 2)
                          (let* ((j (quotient n 2))
                                 (a (step j))
                                 (k (- n j))
                                 (b (step k)))
                            (merge!! a b less?)))
                         ((= n 2)
                          (let ((x (car (get seq)))
                                (y (car (cdr (get seq))))
                                (p (get seq)))
                            (begin
                              (set seq (cdr (cdr (get seq))))
                              (if (less? y x)
                                  (begin (set-car! p y)
                                         (set-car! (cdr p) x))
                                  #u)
                              (set-cdr! (cdr p) nil)
                              p)))
                         ((= n 1)
                          (let ((p (get seq)))
                            (begin (set seq (cdr (get seq)))
                                   (set-cdr! p nil)
                                   p)))
                         (else nil)))))
        (step (chars-length (get seq)))))))

(define* vector->list (subr lists (charv) chars)
  (lambda (v)
    (letrec ((loop (subr lists (int chars) chars)
               (lambda (i l) (if (< i 0) l (loop (- i 1) (cons (array-ref v i) l))))))
      (loop (- (array-length v) 1) nil))))

(define* list->vector (subr lists (chars) charv)
  (lambda (l)
    (let ((v (the charv (make-array (chars-length l) #\a))))
      (letrec ((loop (subr lists (int chars) charv)
                 (lambda (i l)
                   (if (null? l) v (begin (array-set! v i (car l)) (loop (+ i 1) (cdr l)))))))
        (loop 0 l)))))

(define* vector-sort (subr lists (less charv) charv)
  (lambda (less? seq) (list->vector (sort!! (vector->list seq) less?))))

(define* hash-then-sort (subr lists (charv) charv)
  (lambda (chars) (vector-sort char<? (vector-sort hash<? chars))))

;; Returns a vector of all Unicode characters from lo to hi, inclusive.
(define* all-characters (subr lists (char char) charv)
  (lambda (lo hi)
    (letrec ((loop (subr lists (int int chars) chars)
               (lambda (sv0 sv1 chars)
                 (cond ((< sv1 sv0) chars)
                       ((or (< sv1 #xd800) (< #xdfff sv1))
                        (loop sv0 (- sv1 1) (cons (integer->char sv1) chars)))
                       (else (loop sv0 #xd7ff chars))))))
      (list->vector (loop (char->integer lo) (char->integer hi) nil)))))

;; equal? on vectors of characters: Larceny's check of the result.
(define* chars=? (subr lists (charv charv) bool)
  (lambda (a b)
    (letrec ((loop (subr lists (int) bool)
               (lambda (i)
                 (cond ((= i (array-length a)) #t)
                       ((char=? (array-ref a i) (array-ref b i)) (loop (+ i 1)))
                       (else #f)))))
      (and (= (array-length a) (array-length b)) (loop 0)))))
;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 0)
(define input2 int #x10ffff)
(define iterations int 1)

(define chars charv (all-characters (integer->char input1) (integer->char input2)))

(define* run (subr lists (int charv) charv)
  (lambda (i result) (if (= i 0) result (run (- i 1) (hash-then-sort chars)))))
(chars=? (run iterations (make-array 0 #\a)) chars)
