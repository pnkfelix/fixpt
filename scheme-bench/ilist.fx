;;; ILIST -- Immutable list benchmark for (scheme ilist).
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/ilist.scm),
;;; ported to FX-26. Larceny's input: 1 iteration of (go 8).
;;; Answer: ((x0 x1 x2 x3 x4 x5 x6 x7)).
;;;
;;; An ilist's pair, a record of two immutable fields in Larceny's SRFI 116
;;; (lib/SRFI/srfi/116/ilists.body*.scm), is FX-26's frozen pair: an
;;; ilist of T is a `(listof T acyclic)`, made by `cons`, never written.
;;; FX-26 has no (scheme ilist), so the SRFI 116 procedures the benchmark
;;; calls are written here, after Larceny's, each for the element type it
;;; is used at: `iiota` (built backwards, then `ireverse`d), `imap` (in
;;; order), `iappend` of two (`ifold-right ipair`), `iconcatenate`
;;; (`ireduce-right iappend`), `itake`, `idrop`, `ilength`, `imember`
;;; (`ifind-tail`), `ifilter` and `ilist->list`.
;;; - `iequal?` asks `ilist?`, a walk of the whole list (Floyd's, with a
;;;   lag), of both arguments at every step, as there. FX-26 has no `eq?`
;;;   on pairs, and a frozen list has no cycle, so the walk's `(eq? x lag)`
;;;   test is left out; the lag still moves. On the symbols in the lists,
;;;   `ilist?` is #f at once, and `iequal?` is `equal?`, `symbol=?`: that
;;;   case is `iequal-symbol?`.
;;; - `ifilter`'s `eq?` test that shares an unfiltered tail is left out:
;;;   the kept tail is made afresh (one permutation is kept, of 40320).

(define-type iints (listof int acyclic))
(define-type istrs (listof string acyclic))
(define-type isyms (listof symbol acyclic))
(define-type isets (listof isyms acyclic))
(define-type isetss (listof isets acyclic))
(define-effect ilists (maxeff (read @heap) (alloc @heap) spin))

(define* iiota (subr ilists (int) iints)
  (lambda (count)
    (letrec ((ireverse (subr ilists (iints iints) iints)
               ;; (ifold ipair '() lis)
               (lambda (lis ans) (if (null? lis) ans (ireverse (cdr lis) (cons (car lis) ans)))))
             (loop (subr ilists (int iints) iints)
               (lambda (n r)
                 (if (= n count) (ireverse r nil) (loop (+ 1 n) (cons (+ 0 (* n 1)) r))))))
      (loop 0 nil))))

(define* ilength (subr ilists (isyms) int)
  (lambda (x)
    (letrec ((lp (subr ilists (isyms int) int)
               (lambda (x len) (if (null? x) len (lp (cdr x) (+ len 1))))))
      (lp x 0))))

(define* itake (subr ilists (isyms int) isyms)
  (lambda (lis k) (if (= k 0) nil (cons (car lis) (itake (cdr lis) (- k 1))))))

(define* idrop (subr ilists (isyms int) isyms)
  (lambda (lis k) (if (= k 0) lis (idrop (cdr lis) (- k 1)))))

;; (iappend list1 tail) = (ifold-right ipair tail list1)
(define* iappend (subr ilists (isyms isyms) isyms)
  (lambda (list1 tail) (if (null? list1) tail (cons (car list1) (iappend (cdr list1) tail)))))

(define* iappend-sets (subr ilists (isets isets) isets)
  (lambda (list1 tail) (if (null? list1) tail (cons (car list1) (iappend-sets (cdr list1) tail)))))

;; (iconcatenate lists) = (ireduce-right iappend '() lists)
(define* iconcatenate (subr ilists (isetss) isets)
  (lambda (ilis)
    (letrec ((recur (subr (maxeff ilists (read (globals iappend-sets))) (isets isetss) isets)
               (lambda (head ilis)
                 (if (null? ilis) head (iappend-sets head (recur (car ilis) (cdr ilis)))))))
      (if (null? ilis) (the isets nil) (recur (car ilis) (cdr ilis))))))

;; ilist?, as proper-ilist?: a walk with a lag, less the `eq?` (see above).
(define* ilist? (subr ilists (isyms) bool)
  (lambda (x)
    (letrec ((lp (subr ilists (isyms isyms) bool)
               (lambda (x lag)
                 (if (null? x)
                     #t
                     (let ((x (cdr x)))
                       (if (null? x)
                           #t
                           (let ((x (cdr x))
                                 (lag (cdr lag)))
                             (lp x lag))))))))
      (lp x x))))

;; iequal? on two symbols: neither is an ilist, so equal?.
(define iequal-symbol? (subr pure (symbol symbol) bool)
  (lambda (x y) (symbol=? x y)))

(define* iequal? (subr ilists (isyms isyms) bool)
  (lambda (x y)
    (cond ((or (not (ilist? x))
               (not (ilist? y)))
           #f)                          ; (equal? x y): never, here
          ((null? x)
           (null? y))
          ((null? y)
           (null? x))
          ((iequal-symbol? (car x) (car y))
           (iequal? (cdr x) (cdr y)))
          (else
           #f))))

(define* symbols (subr ilists (int) isyms)
  (lambda (n)
    (letrec ((imap-number->string (subr ilists (iints) istrs)
               (lambda (lis)
                 (if (null? lis) nil
                     (let ((tail (cdr lis)) (x (int->string (car lis))))
                       (cons x (imap-number->string tail))))))
             (imap-prefix (subr ilists (istrs) istrs)
               (lambda (lis)
                 (if (null? lis) nil
                     (let ((tail (cdr lis)) (x (string-append "x" (car lis))))
                       (cons x (imap-prefix tail))))))
             (imap-string->symbol (subr ilists (istrs) isyms)
               (lambda (lis)
                 (if (null? lis) nil
                     (let ((tail (cdr lis)) (x (string->symbol (car lis))))
                       (cons x (imap-string->symbol tail)))))))
      (imap-string->symbol (imap-prefix (imap-number->string (iiota n)))))))

(define* powerset (subr ilists (isyms) isets)
  (lambda (universe)
    (if (null? universe)
        (the isets (cons (the isyms nil) nil))
        (let* ((x (car universe))
               (u2 (cdr universe))
               (pu2 (powerset u2)))
          (letrec ((imap (subr ilists (isets) isets)
                     (lambda (lis)
                       (if (null? lis) nil
                           (let ((tail (cdr lis)) (y (the isyms (cons x (car lis)))))
                             (cons y (imap tail)))))))
            (iappend-sets pu2 (imap pu2)))))))

(define* permutations (subr ilists (isyms) isets)
  (lambda (universe)
    (if (null? universe)
        (the isets (cons (the isyms nil) nil))
        (let* ((x (car universe))
               (u2 (cdr universe))
               (perms2 (permutations u2)))
          (letrec ((imap-i (subr (maxeff ilists (read (globals iappend itake idrop))) (isyms iints) isets)
                     (lambda (perm lis)
                       (if (null? lis) nil
                           (let ((tail (cdr lis))
                                 (y (iappend (itake perm (car lis)) (cons x (idrop perm (car lis))))))
                             (cons y (imap-i perm tail))))))
                   (imap-perm (subr (maxeff ilists (read (globals iappend itake idrop iiota ilength))) (isets) isetss)
                     (lambda (lis)
                       (if (null? lis) nil
                           (let ((tail (cdr lis))
                                 (y (imap-i (car lis) (iiota (+ 1 (ilength (car lis)))))))
                             (cons y (imap-perm tail)))))))
            (iconcatenate (imap-perm perms2)))))))

(define* go (subr ilists (int) (listof (listof symbol @heap) @heap))
  (lambda (n)
    (let* ((universe (symbols n))
           (subsets (powerset universe))
           (perms (permutations universe)))
      (letrec ((imember (subr (maxeff ilists (read (globals iequal? ilist? iequal-symbol?))) (isyms isets) bool)
                 ;; (imember perm subsets iequal?), as ifind-tail
                 (lambda (x lis)
                   (and (not (null? lis))
                        (if (iequal? x (car lis)) #t (imember x (cdr lis))))))
               (ifilter (subr (maxeff ilists (read (globals iequal? ilist? iequal-symbol?))) (isets) isets)
                 (lambda (lis)
                   (if (null? lis) lis
                       (let ((head (car lis))
                             (tail (cdr lis)))
                         (if (imember head subsets)
                             (cons head (ifilter tail))
                             (ifilter tail))))))
               (ilist->list (subr ilists (isyms) (listof symbol @heap))
                 (lambda (lis) (if (null? lis) nil (cons (car lis) (ilist->list (cdr lis))))))
               (map-ilist->list (subr ilists (isets) (listof (listof symbol @heap) @heap))
                 ;; (map ilist->list (ilist->list ...)), the outer ilist->list
                 ;; and map fused
                 (lambda (lis) (if (null? lis) nil (cons (ilist->list (car lis)) (map-ilist->list (cdr lis)))))))
        (map-ilist->list (ifilter perms))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 8)
(define iterations int 1)

(define* run (subr ilists (int (listof (listof symbol @heap) @heap)) (listof (listof symbol @heap) @heap))
  (lambda (i result) (if (= i 0) result (run (- i 1) (go input1)))))
(run iterations nil)
