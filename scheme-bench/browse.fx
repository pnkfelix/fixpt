;;; BROWSE -- Benchmark to create and browse through
;;; an AI-like data base of units.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/browse.scm),
;;; ported to FX-26. Larceny's input: 2000 iterations of
;;; (browse '((*a ?b *b ?b a *a a *b *a)
;;;           (*a *b *b *a (*a) (*b))
;;;           (? ? * (b a) * ? ?))).
;;; Answer: the database, a list of the 100 units' names, symbols made of
;;; numbers: (837 177 1090 617 661 749 628 56 826 408 1035 474 320 452 672
;;; 991 155 122 793 221 716 727 848 309 144 936 100 881 287 430 23 771 232
;;; 804 958 650 1068 1057 463 276 1046 1002 199 34 738 210 540 397 342 364
;;; 782 683 89 375 166 595 892 705 507 639 331 188 243 441 1013 1079 67 298
;;; 386 573 859 133 760 12 529 815 111 496 45 265 925 903 254 78 551 606 485
;;; 518 419 870 562 1 353 980 694 914 969 947 584 1024), which Larceny's
;;; input file writes |837| |177| ….
;;;
;;; The patterns and the data are lists of symbols and of such lists: an
;;; `item` is a `define-datatype` of a symbol or a list of items, and the
;;; lists stay mutable lists, since `init` makes the list of patterns
;;; circular and `randomize` and `append-to-tail!` splice lists in place.
;;; `eq?` of two items (`item-eq?`) is `eq?` of their symbols or of their
;;; lists: an item, a sum, is immutable, and FX-26's `eq?` says nothing of
;;; two unequal sums, but the pairs within are mutable, so `eq?` of them
;;; is exact, as Scheme's is. A `*` variable's binding, a list, is kept in
;;; the association list as an item, `(lst l)`, so that both kinds of
;;; binding are one type (`item-list` takes the list back out).
;;; `my-match` returns `'()` in one case where it otherwise returns a
;;; boolean; only its truth is ever used,
;;; and `'()` is true, so here it returns `#t` there. Its `symbol->string`
;;; of an empty list, an error in the original, is never reached; here that
;;; case is `#f`. A property whose value is `#f` has `nil`; `get` of none
;;; returns `nil` for `#f`. `get` is `get-property`, since FX-26's `get` reads a
;;; reference. `properties`, `*current-gensym*` and `*rand*`,
;;; which the original `set!`s, are references. `do` loops, and the
;;; `set!`s of their variables, are loops passing the new values on.
;;; `tree-copy` of the list of patterns copies the same pairs as the
;;; original's, at two types. `assq` is written out. The inputs are built
;;; in the file.

(define-datatype item (sym symbol) (lst (listof item @heap)))
(define-type items (listof item @heap))
;; A unit's properties: `pattern` to a list of data, and made-up names
;; to `#f` (`nil`).
(define-type value (listof items @heap))
(define-type plist (listof (pairof symbol value @heap) @heap))

(define lookup
  (poly ((v type))
    (subr (maxeff (read @heap) spin) (symbol (listof (pairof symbol v @heap) @heap)) (pairof symbol v @heap)))
  (plambda ((v type))
    (lambda (key table)
      (letrec ((loop (subr (maxeff (read @heap) spin) ((listof (pairof symbol v @heap) @heap)) (pairof symbol v @heap))
                 (lambda (x)
                   (if (null? x)
                       no-pair
                       (let ((pair (car x)))
                         (if (eq? (car pair) key)
                             pair
                             (loop (cdr x))))))))
        (loop table)))))

(define properties (ref (listof (pairof symbol plist @heap) @heap) @heap) (new nil))

(define* get-property (subr (maxeff (read @heap) spin) (symbol symbol) value)
  (lambda (key1 key2)
    (let ((x (lookup key1 (get properties))))
      (if (not (null? x))
          (let ((y (lookup key2 (cdr x))))
            (if (not (null? y))
                (cdr y)
                nil))
          nil))))

(define* put (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (symbol symbol value) unit)
  (lambda (key1 key2 val)
    (let ((x (lookup key1 (get properties))))
      (if (not (null? x))
          (let ((y (lookup key2 (cdr x))))
            (if (not (null? y))
                (set-cdr! y val)
                (set-cdr! x (cons (cons key2 val) (cdr x)))))
          (set properties
               (cons (cons key1 (cons (cons key2 val) nil)) (get properties)))))))

(define *current-gensym* (ref int @heap) (new 0))

(define* generate-symbol (subr (maxeff (read @heap) (write @heap)) () symbol)
  (lambda ()
    (begin
      (set *current-gensym* (+ (get *current-gensym*) 1))
      (string->symbol (int->string (get *current-gensym*))))))

(define* append-to-tail! (subr (maxeff (read @heap) (write @heap) spin) (items items) items)
  (lambda (x y)
    (if (null? x)
        y
        (letrec ((loop (subr (maxeff (read @heap) (write @heap) spin) (items items) items)
                   (lambda (a b)
                     (if (null? b)
                         (begin (set-cdr! a y) x)
                         (loop b (cdr b))))))
          (loop x (cdr x))))))

;; `tree-copy`, of items, and of the list of patterns.
(define-rec
  (tree-copy-item (subr (maxeff (read @heap) (alloc @heap) spin (read (globals tree-copy-item tree-copy-items lst))) (item) item)
    (lambda (x)
      (tagcase x
        (sym (s) x)
        (lst (l) (lst (tree-copy-items l))))))
  (tree-copy-items (subr (maxeff (read @heap) (alloc @heap) spin (read (globals tree-copy-item tree-copy-items lst))) (items) items)
    (lambda (x)
      (if (null? x)
          x
          (cons (tree-copy-item (car x))
                (tree-copy-items (cdr x)))))))
(define* tree-copy (subr (maxeff (read @heap) (alloc @heap) spin) (value) value)
  (lambda (x)
    (if (null? x)
        x
        (cons (tree-copy-items (car x))
              (tree-copy (cdr x))))))

;;; n is # of symbols
;;; m is maximum amount of stuff on the plist
;;; npats is the number of basic patterns on the unit
;;; ipats is the instantiated copies of the patterns

(define *rand* (ref int @heap) (new 21))

(define-effect inits
  (maxeff (read @heap) (write @heap) (alloc @heap) spin
          (read (globals put lookup properties generate-symbol *current-gensym*))))

(define* init (subr (maxeff inits (read (globals tree-copy))) (int int int value) (listof symbol @heap))
  (lambda (n m npats ipats)
    (let ((ipats (tree-copy ipats)))
      (letrec ((circle (subr (maxeff (read @heap) (write @heap) spin) (value) unit)
                 (lambda (p)
                   (if (null? (cdr p)) (set-cdr! p ipats) (circle (cdr p)))))
               (loop (subr inits (int int symbol (listof symbol @heap)) (listof symbol @heap))
                 (lambda (n i name a)
                   (if (= n 0)
                       a
                       (let ((a (the (listof symbol @heap) (cons name a))))
                         (letrec ((put-names (subr inits (int) unit)
                                    (lambda (i)
                                      (if (= i 0)
                                          #u
                                          (begin (put name (generate-symbol) nil)
                                                 (put-names (- i 1))))))
                                  (pattern (subr (maxeff (read @heap) (alloc @heap) spin) (int value value) value)
                                    (lambda (i ipats a)
                                      (if (= i 0)
                                          a
                                          (pattern (- i 1) (cdr ipats) (cons (car ipats) a))))))
                           (begin
                             (put-names i)
                             (put name
                                  'pattern
                                  (pattern npats ipats nil))
                             (put-names (- m i))
                             (loop (- n 1)
                                   (if (= i 0) m (- i 1))
                                   (generate-symbol)
                                   a))))))))
        (begin
          (circle ipats)
          (loop n m (generate-symbol) nil))))))

(define* browse-random (subr (maxeff (read @heap) (write @heap)) () int)
  (lambda ()
    (begin
      (set *rand* (remainder (* (get *rand*) 17) 251))
      (get *rand*))))


(define* randomize (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) ((listof symbol @heap)) (listof symbol @heap))
  (lambda (l)
    (letrec ((loop (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read (globals browse-random *rand*)))
                         ((listof symbol @heap) (listof symbol @heap)) (listof symbol @heap))
               (lambda (l a)
                 (if (null? l)
                     a
                     (let ((n (remainder (browse-random) (list-length l))))
                       (if (= n 0)
                           (loop (cdr l) (cons (car l) a))
                           (letrec ((find (subr (maxeff (read @heap) spin) (int (listof symbol @heap)) (listof symbol @heap))
                                      (lambda (n x) (if (= n 1) x (find (- n 1) (cdr x))))))
                             (let ((x (find n l)))
                               (let ((a (the (listof symbol @heap) (cons (car (cdr x)) a))))
                                 (begin
                                   (set-cdr! x (cdr (cdr x)))
                                   (loop l a)))))))))))
      (loop l nil))))

;; `eq?` of two items: of their symbols, or of their lists, which stay
;; mutable pairs, so that `eq?` of them is exact.
(define* item-eq? (subr pure (item item) bool)
  (lambda (x y)
    (tagcase x
      (sym (s) (tagcase y (sym (t) (eq? s t)) (lst (l) #f)))
      (lst (l) (tagcase y (sym (t) #f) (lst (m) (eq? l m)))))))

(define* is? (subr pure (item symbol) bool)
  (lambda (x s) (tagcase x (sym (t) (eq? t s)) (lst (l) #f))))

(define-type alist (listof (pairof symbol item @heap) @heap))

(define* assq (subr (maxeff (read @heap) spin) (symbol alist) (pairof symbol item @heap))
  (lambda (key l)
    (cond ((null? l) no-pair)
          ((eq? (car (car l)) key) (car l))
          (else (assq key (cdr l))))))


;; A `*` variable's binding, as a list.
(define* item-list (subr pure (item) items)
  (lambda (x) (tagcase x (lst (l) l) (sym (s) (the items nil)))))
(define-effect matches
  (maxeff (read @heap) (write @heap) (alloc @heap) spin
          (read (globals my-match item-eq? is? assq append-to-tail! sym lst))))

(define* my-match (subr matches (items items alist) bool)
  (lambda (pat dat alist)
    (cond ((null? pat)
           (null? dat))
          ((null? dat) #t)              ; '() in the original
          ((or (is? (car pat) '?)
               (item-eq? (car pat)
                         (car dat)))
           (my-match (cdr pat) (cdr dat) alist))
          ((is? (car pat) '*)
           (or (my-match (cdr pat) dat alist)
               (my-match (cdr pat) (cdr dat) alist)
               (my-match pat (cdr dat) alist)))
          (else
           (tagcase (car pat)
             (sym (s)
               (cond ((char=? (string-ref (symbol->string s) 0)
                              #\?)
                      (let ((val (assq s alist)))
                        (cond ((not (null? val))
                               (my-match (cons (cdr val)
                                               (cdr pat))
                                         dat alist))
                              (else (my-match (cdr pat)
                                              (cdr dat)
                                              (cons (cons s
                                                          (car dat))
                                                    alist))))))
                     ((char=? (string-ref (symbol->string s) 0)
                              #\*)
                      (let ((val (assq s alist)))
                        (cond ((not (null? val))
                               (my-match (append (item-list (cdr val))
                                                 (cdr pat))
                                         dat alist))
                              (else
                               (letrec ((loop (subr matches (items items items) bool)
                                          (lambda (l e d)
                                            (if (or (null? e)
                                                    (my-match (cdr pat)
                                                              d
                                                              (cons
                                                               (cons s (lst l))
                                                               alist)))
                                                (if (null? e) #f #t)
                                                (loop (append-to-tail!
                                                       l
                                                       (cons (if (null? d)
                                                                 (lst nil)
                                                                 (car d))
                                                             nil))
                                                      (cdr e)
                                                      (if (null? d) nil (cdr d)))))))
                                 (loop nil (cons (lst nil) dat) dat))))))

                     ;; fix suggested by Manuel Serrano
                     ;; (cond did not have an else clause);
                     ;; this changes the run time quite a bit

                     (else #f)))
             (lst (l)
               (and
                (not (null? l))         ; (pair? (car pat))
                (tagcase (car dat) (sym (t) #f) (lst (m) (not (null? m)))) ; (pair? (car dat))
                (my-match l
                          (tagcase (car dat) (sym (t) nil) (lst (m) m))
                          alist)
                (my-match (cdr pat)
                          (cdr dat) alist))))))))

(define database (listof symbol @heap)
  (randomize
   (init 100 10 4
         (list (list (sym 'a) (sym 'a) (sym 'a) (sym 'b) (sym 'b) (sym 'b) (sym 'b) (sym 'a) (sym 'a) (sym 'a) (sym 'a) (sym 'a) (sym 'b) (sym 'b) (sym 'a) (sym 'a) (sym 'a))
               (list (sym 'a) (sym 'a) (sym 'b) (sym 'b) (sym 'b) (sym 'b) (sym 'a) (sym 'a) (lst (list (sym 'a) (sym 'a))) (lst (list (sym 'b) (sym 'b))))
               (list (sym 'a) (sym 'a) (sym 'a) (sym 'b) (lst (list (sym 'b) (sym 'a))) (sym 'b) (sym 'a) (sym 'b) (sym 'a))))))

(define* investigate (subr (maxeff matches (read (globals get-property lookup properties))) ((listof symbol @heap) value) unit)
  (lambda (units pats)
    (letrec ((units-loop (subr (maxeff matches (read (globals get-property lookup properties))) ((listof symbol @heap)) unit)
               (lambda (units)
                 (if (null? units)
                     #u
                     (letrec ((pats-loop (subr (maxeff matches (read (globals get-property lookup properties))) (value) unit)
                                (lambda (pats)
                                  (if (null? pats)
                                      #u
                                      (letrec ((p-loop (subr matches (value) unit)
                                                 (lambda (p)
                                                   (if (null? p)
                                                       #u
                                                       (begin
                                                         (my-match (car pats) (car p) nil)
                                                         (p-loop (cdr p)))))))
                                        (begin
                                          (p-loop (get-property (car units) 'pattern))
                                          (pats-loop (cdr pats))))))))
                       (begin
                         (pats-loop pats)
                         (units-loop (cdr units))))))))
      (units-loop units))))

(define* browse (subr (maxeff matches (read (globals investigate get lookup properties database))) (value) (listof symbol @heap))
  (lambda (pats)
    (begin
      (investigate
       database
       pats)
      database)))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 value
  (list (list (sym '*a) (sym '?b) (sym '*b) (sym '?b) (sym 'a) (sym '*a) (sym 'a) (sym '*b) (sym '*a))
        (list (sym '*a) (sym '*b) (sym '*b) (sym '*a) (lst (cons (sym '*a) (the items nil))) (lst (cons (sym '*b) (the items nil))))
        (list (sym '?) (sym '?) (sym '*) (lst (list (sym 'b) (sym 'a))) (sym '*) (sym '?) (sym '?))))
(define iterations int 2000)

(define* run (subr (maxeff matches (read (globals browse investigate get-property lookup properties database input1)))
                   (int (listof symbol @heap)) (listof symbol @heap))
  (lambda (i result) (if (= i 0) result (run (- i 1) (browse input1)))))
(run iterations nil)
