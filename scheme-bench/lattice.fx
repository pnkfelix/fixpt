;;; LATTICE -- Obtained from Andrew Wright.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/lattice.scm),
;;; ported to FX-26. Larceny's input: 10 iterations of (run 44).
;;; Answer: 120549.
;;;
;;; A lattice's elements are the symbols `low` and `high`, then lists of
;;; elements, then lists of those: an `elem`, a `define-datatype` of a
;;; symbol or a list of elements. The comparisons' results stay the
;;; symbols `less`, `more`, `equal` and `uncomparable`, compared with
;;; `symbol=?` for `eq?`; `case` is a `cond` of them. A lattice is a pair
;;; of its elements and its comparison, as in the original. `maps-rest` is
;;; polymorphic in what it collects, as the original is untyped in it:
;;; `maps` collects lists of elements, `count-maps` sums ints. `map`,
;;; `memq` of a quoted list, and `(apply append x)` are written out;
;;; `error` in the base comparison, never reached, returns `uncomparable`,
;;; FX-26 having no `error`, and so does `run` for a size it does not
;;; know, returning 0.

(define-datatype elem (sym symbol) (seq (listof elem @heap)))
(define-type elems (listof elem @heap))

;; What comparing and walks do: read, build and reverse lists, recurse,
;; and call the program's procedures, which the closures passed around
;; call too.
(define-effect walks
  (maxeff (read @heap) (write @heap) (alloc @heap) spin
          (read (globals seq lattice->cmp lattice->elements reverse! zulu-select select-map
                         map-and append2 maps-1 maps-rest sum-list))))
(define-type cmp (subr walks (elem elem) symbol))

; Given a comparison routine that returns one of
;       less
;       more
;       equal
;       uncomparable
; return a new comparison routine that applies to sequences.
(define* lexico (subr pure (cmp) cmp)
  (lambda (base)
    (letrec ((lex-fixed (subr walks (symbol elems elems) symbol)
               (lambda (fixed lhs rhs)
                 (letrec ((check (subr walks (elems elems) symbol)
                            (lambda (lhs rhs)
                              (if (null? lhs)
                                  fixed
                                  (let ((probe
                                         (base (car lhs)
                                               (car rhs))))
                                    (if (or (symbol=? probe 'equal)
                                            (symbol=? probe fixed))
                                        (check (cdr lhs)
                                               (cdr rhs))
                                        'uncomparable))))))
                   (check lhs rhs))))
             (lex-first (subr walks (elems elems) symbol)
               (lambda (lhs rhs)
                 (if (null? lhs)
                     'equal
                     (let ((probe
                            (base (car lhs)
                                  (car rhs))))
                       (cond ((or (symbol=? probe 'less) (symbol=? probe 'more))
                              (lex-fixed probe
                                         (cdr lhs)
                                         (cdr rhs)))
                             ((symbol=? probe 'equal)
                              (lex-first (cdr lhs)
                                         (cdr rhs)))
                             (else
                              'uncomparable)))))))
      (lambda ((lhs elem) (rhs elem))
        (lex-first (tagcase lhs (sym (s) nil) (seq (l) l))
                   (tagcase rhs (sym (s) nil) (seq (l) l)))))))

(define-type lattice (pairof elems cmp @heap))

(define* make-lattice (subr (alloc @heap) (elems cmp) lattice)
  (lambda (elem-list cmp-func)
    (cons elem-list cmp-func)))

(define* lattice->elements (subr (read @heap) (lattice) elems) (lambda (l) (car l)))

(define* lattice->cmp (subr (read @heap) (lattice) cmp) (lambda (l) (cdr l)))

(define reverse! (subr walks (elems) elems)
  (letrec ((rotate (subr walks (elems elems) elems)
             (lambda (fo fum)
               (let ((next (cdr fo)))
                 (begin
                   (set-cdr! fo fum)
                   (if (null? next)
                       fo
                       (rotate next fo)))))))
    (lambda ((lst elems))
      (if (null? lst)
          (the elems nil)
          (rotate lst nil)))))

; Select elements of a list which pass some test.
(define* zulu-select (subr walks ((subr walks (elem) bool) elems) elems)
  (lambda (test lst)
    (letrec ((select-a (subr walks (elems elems) elems)
               (lambda (ac lst)
                 (if (null? lst)
                     (reverse! ac)
                     (select-a
                      (let ((head (car lst)))
                        (if (test head)
                            (cons head ac)
                            ac))
                      (cdr lst))))))
      (select-a nil lst))))

; Select elements of a list which pass some test and map a function
; over the result.  Note, only efficiency prevents this from being the
; composition of select and map.
(define* select-map (subr walks
                          ((subr walks ((pairof elem elem @heap)) bool)
                           (subr walks ((pairof elem elem @heap)) elem)
                           (listof (pairof elem elem @heap) @heap))
                          elems)
  (lambda (test func lst)
    (letrec ((select-a (subr walks (elems (listof (pairof elem elem @heap) @heap)) elems)
               (lambda (ac lst)
                 (if (null? lst)
                     (reverse! ac)
                     (select-a
                      (let ((head (car lst)))
                        (if (test head)
                            (cons (func head)
                                  ac)
                            ac))
                      (cdr lst))))))
      (select-a nil lst))))

; This version of map-and tail-recurses on the last test.
(define* map-and (subr walks ((subr walks (elem) bool) elems) bool)
  (lambda (proc lst)
    (if (null? lst)
        #t
        (letrec ((drudge (subr walks (elems) bool)
                   (lambda (lst)
                     (let ((rest (cdr lst)))
                       (if (null? rest)
                           (proc (car lst))
                           (and (proc (car lst))
                                (drudge rest)))))))
          (drudge lst)))))

(define* append2 (subr (maxeff (read @heap) (alloc @heap) spin) (elems elems) elems)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (append2 (cdr xs) ys)))))

(define-type pas (listof (pairof elem elem @heap) @heap))

(define* maps-1 (subr walks (lattice lattice pas elem) elems)
  (lambda (source target pas new)
    (let ((scmp (lattice->cmp source))
          (tcmp (lattice->cmp target)))
      (let ((less
             (select-map
              (lambda (p)
                (symbol=? 'less
                          (scmp (car p) new)))
              (lambda (p) (cdr p))
              pas))
            (more
             (select-map
              (lambda (p)
                (symbol=? 'more
                          (scmp (car p) new)))
              (lambda (p) (cdr p))
              pas)))
        (zulu-select
         (lambda (t)
           (and
            (map-and
             (lambda (t2)
               (let ((r (tcmp t2 t)))  ; (memq r '(less equal))
                 (or (symbol=? r 'less) (symbol=? r 'equal))))
             less)
            (map-and
             (lambda (t2)
               (let ((r (tcmp t2 t)))  ; (memq r '(more equal))
                 (or (symbol=? r 'more) (symbol=? r 'equal))))
             more)))
         (lattice->elements target))))))

(define maps-rest
  (poly ((t type))
    (subr walks
          (lattice lattice pas elems
           (subr walks (pas) t)
           (subr walks ((listof t @heap)) t))
          t))
  (plambda ((t type))
    (lambda (source target pas rest to-1 to-collect)
      (if (null? rest)
          (to-1 pas)
          (let ((next (car rest))
                (rest (cdr rest)))
            (letrec ((map1 (subr walks (elems) (listof t @heap))
                       (lambda (l)
                         (if (null? l)
                             nil
                             (cons (maps-rest source target
                                              (cons
                                               (cons next (car l))
                                               pas)
                                              rest
                                              to-1
                                              to-collect)
                                   (map1 (cdr l)))))))
              (to-collect
               (map1 (maps-1 source target pas next)))))))))

(define* maps (subr (maxeff walks (read (globals make-lattice lexico)))
                    (lattice lattice) lattice)
  (lambda (source target)
    (make-lattice
     ((proj maps-rest elems)
                source
                target
                nil
                (lattice->elements source)
                (lambda (x)             ; (list (map cdr x))
                  (letrec ((map-cdr (subr walks (pas) elems)
                             (lambda (x) (if (null? x) nil (cons (cdr (car x)) (map-cdr (cdr x)))))))
                    (the elems (cons (seq (map-cdr x)) nil))))
                (lambda (x)             ; (apply append x)
                  (letrec ((append* (subr walks ((listof elems @heap)) elems)
                             (lambda (x) (if (null? x) nil (append2 (car x) (append* (cdr x)))))))
                    (append* x))))
     (lexico (lattice->cmp target)))))

(define* sum-list (subr walks ((listof int @heap)) int)
  (lambda (lst)
    (if (null? lst)
        0
        (+ (car lst) (sum-list (cdr lst))))))

(define* count-maps (subr walks
                          (lattice lattice) int)
  (lambda (source target)
    ((proj maps-rest int)
               source
               target
               nil
               (lattice->elements source)
               (lambda (x) 1)
               sum-list)))

(define* run (subr (maxeff walks (read (globals make-lattice lexico maps count-maps sym)))
                   (int) int)
  (lambda (k)
    (let* ((l2
            (make-lattice (list (sym 'low) (sym 'high))
                          (lambda (lhs rhs)
                            (tagcase lhs
                              (sym (lhs)
                                (tagcase rhs
                                  (sym (rhs)
                                    (cond ((symbol=? lhs 'low)
                                           (cond ((symbol=? rhs 'low)
                                                  'equal)
                                                 ((symbol=? rhs 'high)
                                                  'less)
                                                 (else
                                                  'uncomparable)))
                                          ((symbol=? lhs 'high)
                                           (cond ((symbol=? rhs 'low)
                                                  'more)
                                                 ((symbol=? rhs 'high)
                                                  'equal)
                                                 (else
                                                  'uncomparable)))
                                          (else
                                           'uncomparable)))
                                  (seq (l) 'uncomparable)))
                              (seq (l) 'uncomparable)))))
           (l3 (maps l2 l2))
           (l4 (maps l3 l3)))
      (begin
        (count-maps l2 l2)
        (count-maps l3 l3)
        (count-maps l2 l3)
        (count-maps l3 l2)
        (cond ((= k 33) (count-maps l3 l3))
              ((= k 44) (count-maps l4 l4))
              ((= k 45) (let ((l5 (maps l4 l4)))
                          (count-maps l4 l5)))
              ((= k 54) (let ((l5 (maps l4 l4)))
                          (count-maps l5 l4)))
              ((= k 55) (let ((l5 (maps l4 l4)))
                          (count-maps l5 l5)))
              (else 0))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 44)
(define iterations int 10)

(define* run-benchmark (subr (maxeff walks (read (globals run))) (int int) int)
  (lambda (i result) (if (= i 0) result (run-benchmark (- i 1) (run input1)))))
(run-benchmark iterations 0)
