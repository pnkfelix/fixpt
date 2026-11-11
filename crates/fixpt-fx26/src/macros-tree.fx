;;; A program's aligned tree as its shaper asks of it (`macros-shaper.fx`):
;;; each node's parent, the list it is an element of and its place there,
;;; its list's elements, and whether it is under another node, each found
;;; once for every node when the walk begins (`tree-begin!`), so that each
;;; question is answered in time of its own, not of the program's size. A
;;; template's tree is a few dozen nodes, and these were found by climbing
;;; it; a file's is many thousands (`TODO.md` §239). Part of the expander:
;;; loaded by `macros-shaper.fx`, and loading `macros-walk.fx`, so that the
;;; shaper's nodes are these.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define walk-module ((proj (load-module "fx26:macros-walk.fx") rs re rm rc rp)))
(define scopes-module (with walk-module scopes-module))
(define align-module (with scopes-module align-module))
(define types-module (with align-module types-module))
(import types-module (type addr))
(import align-module node-kids node-path k-pair k-form k-desc k-seq)
(import walk-module addr=?)

;; Each node's parent (-1 for none); the list node each is an element of
;; (-1 for none) and its place there; each node's place in a walk of the
;; tree before and after its children; its list's elements, once asked.
(define parents (ref (arrayof int rs) rs) (new (make-array 1 -1)))
(define lists (ref (arrayof int rs) rs) (new (make-array 1 -1)))
(define places (ref (arrayof int rs) rs) (new (make-array 1 0)))
(define pres (ref (arrayof int rs) rs) (new (make-array 1 0)))
(define posts (ref (arrayof int rs) rs) (new (make-array 1 0)))
(define elems-done (ref (arrayof bool rs) rs) (new (make-array 1 #f)))
(define-type ints (listof int acyclic))
(define elems-made (ref (arrayof ints rs) rs) (new (make-array 1 (the ints nil))))
(define tops (ref (arrayof int rs) rs) (new (make-array 1 -1)))

;; The tree of nodes 0 to `n`, found.
(define tree-begin! (->* (int) unit)
  (lambda (n)
    (begin
      (set parents (the (arrayof int rs) (make-array n -1)))
      (set lists (the (arrayof int rs) (make-array n -1)))
      (set places (the (arrayof int rs) (make-array n 0)))
      (set pres (the (arrayof int rs) (make-array n -1)))
      (set posts (the (arrayof int rs) (make-array n -1)))
      (set elems-done (the (arrayof bool rs) (make-array n #f)))
      (set elems-made (the (arrayof ints rs) (make-array n (the ints nil))))
      (set tops (the (arrayof int rs) (make-array n -1)))
      (parents-from 0 n)
      (places-from 0 n)
      (numbered-from 0 n 0))))
(define parent-of (->* (int) int) (lambda (i) (if (< i 0) -1 (array-ref (get parents) i))))
;; Node `i`'s children, in order.
(define kids-of (->* (int) (listof int acyclic))
  (lambda (i)
    (tagcase (node-kids i)
      (k-pair (x y) (list x y))
      (k-form (x) (list x))
      (k-seq (x) (list x))
      (k-desc (xs) xs)
      (else y nil))))
(define parents-from (->* (int int) unit)
  (lambda (i n)
    (if (= i n) #u (begin (parent-each (kids-of i) i) (parents-from (+ i 1) n)))))
(define parent-each (->* ((listof int acyclic) int) unit)
  (lambda (xs i)
    (if (null? xs) #u (begin (array-set! (get parents) (car xs) i) (parent-each (cdr xs) i)))))

;;; ------------------------------------------------------------ places in lists

;; Each list's elements given their list node and place: a chain of pairs
;; from its head (a pair no pair's cdr is), its list a form's (the form's
;; head counted as its place 0 where the chain is the whole form) or its
;; own; a description's parts, by their order.
(define places-from (->* (int int) unit)
  (lambda (i n)
    (if (= i n)
        #u
        (begin
          (tagcase (node-kids i)
            (k-pair (x y) (if (chain-head? i) (chain-placed! i) #u))
            (k-desc (xs) (desc-placed! xs i 0))
            (else y #u))
          (places-from (+ i 1) n)))))
(define chain-head? (->* (int) bool)
  (lambda (i)
    (let ((q (parent-of i)))
      (not (and (>= q 0) (tagcase (node-kids q) (k-pair (a d) (= d i)) (else y #f)))))))
(define chain-placed! (->* (int) unit)
  (lambda (h)
    (let* ((q (parent-of h))
           (form (and (>= q 0) (tagcase (node-kids q) (k-form (x) (= x h)) (else y #f))))
           (list-node (if form q h))
           (from (if (and form (not (addr=? (node-path h) (node-path q)))) 1 0)))
      (chain-each! h list-node from))))
(define chain-each! (->* (int int int) unit)
  (lambda (c l k)
    (tagcase (node-kids c)
      ;; Placed only where `a`'s parent is this pair, as the parents array
      ;; has it (the last written), from which its place was found before.
      (k-pair (a d)
        (begin (if (= (parent-of a) c)
                   (begin (array-set! (get lists) a l) (array-set! (get places) a k))
                   #u)
               (chain-each! d l (+ k 1))))
      (else y #u))))
(define desc-placed! (->* ((listof int acyclic) int int) unit)
  (lambda (xs p k)
    (if (null? xs)
        #u
        (begin
          ;; A part twice: its first place, as a search of the parts finds it.
          (if (and (= (parent-of (car xs)) p) (< (array-ref (get lists) (car xs)) 0))
              (begin (array-set! (get lists) (car xs) p) (array-set! (get places) (car xs) k))
              #u)
          (desc-placed! (cdr xs) p (+ k 1))))))
;; The list node `b` is an element of, and its place there; (-1 . 0) if
;; none.
(define position (->* (int) (tupleof int int))
  (lambda (b)
    (if (or (< b 0) (< (array-ref (get lists) b) 0))
        (tuple -1 0)
        (tuple (array-ref (get lists) b) (array-ref (get places) b)))))
;; The nodes of node `at`'s list's elements, by place (-1 where no node is,
;; a form's head).
(define elems (->* (int) (listof int acyclic))
  (lambda (at)
    (if (array-ref (get elems-done) at)
        (array-ref (get elems-made) at)
        (let ((e (elems-found at)))
          (begin (array-set! (get elems-made) at e) (array-set! (get elems-done) at #t) e)))))
(define elems-found (->* (int) (listof int acyclic))
  (lambda (at)
    (tagcase (node-kids at)
      (k-form (x)
        (if (addr=? (node-path x) (node-path at)) (cars x) (cons -1 (cars x))))
      (k-pair (a d) (cars at))
      (k-desc (xs) xs)
      (else y nil))))
(define cars (->* (int) (listof int acyclic))
  (lambda (x) (tagcase (node-kids x) (k-pair (a d) (cons a (cars d))) (else y nil))))
;; The `k`th element of node `at`'s list, or -1.
(define elem (->* (int int) int)
  (lambda (at k) (int-at (elems at) k)))
(define int-at (->* ((listof int acyclic) int) int)
  (lambda (xs k) (cond ((null? xs) -1) ((= k 0) (car xs)) (else (int-at (cdr xs) (- k 1))))))

;;; ------------------------------------------------------------ under

;; Each node's place in a walk of the tree, before and after its children,
;; from each root, the walk's stack its own: a list may be long.
(define numbered-from (->* (int int int) unit)
  (lambda (i n k)
    (cond ((= i n) #u)
          ((< (parent-of i) 0) (numbered-from (+ i 1) n (numbered (list (tuple i #f)) k)))
          (else (numbered-from (+ i 1) n k)))))
(define numbered (->* ((listof (tupleof int bool) acyclic) int) int)
  (lambda (stack k)
    (if (null? stack)
        k
        (let ((i (extract (car stack) 1)))
          (if (extract (car stack) 2)
              (begin (array-set! (get posts) i k) (numbered (cdr stack) (+ k 1)))
              (begin (array-set! (get pres) i k)
                     (numbered (kids-pushed (kids-of i) (cons (tuple i #t) (cdr stack)))
                               (+ k 1))))))))
;; Nodes `xs` onto `stack`, the first on top.
(define kids-pushed (->* ((listof int acyclic) (listof (tupleof int bool) acyclic))
                         (listof (tupleof int bool) acyclic))
  (lambda (xs stack)
    (if (null? xs) stack (cons (tuple (car xs) #f) (kids-pushed (cdr xs) stack)))))
;; Whether node `at` is node `m` or under it, by its path (each innermost
;; step first, `path+`: `m`'s is the end of `at`'s): under the outermost
;; node of `m`'s path, which every node whose path ends with it is under.
(define under? (->* (int int) bool)
  (lambda (at m)
    (let ((t (path-top m)))
      (and (<= (array-ref (get pres) t) (array-ref (get pres) at))
           (<= (array-ref (get posts) at) (array-ref (get posts) t))))))
(define path-top (->* (int) int)
  (lambda (m)
    (let ((t (array-ref (get tops) m)))
      (if (>= t 0)
          t
          (let* ((q (parent-of m))
                 (top (if (and (>= q 0) (addr=? (node-path q) (node-path m))) (path-top q) m)))
            (begin (array-set! (get tops) m top) top))))))
