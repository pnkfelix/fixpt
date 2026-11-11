;;; The expander's environments with each import's ribs one level indexed
;;; by name (`macros-env-types.fx`'s `env-ops`; `TODO.md` §234): what
;;; `macros-env-list.fx` finds, found in the depth of a tree for each such
;;; level, where the list walks every rib. A module of `n` items is a rib
;;; for each item, all in one import (`macros-kernel.fx`'s `items`), so one
;;; level here. A module file of no state.
;;;
;;; An environment is its levels, as the list has them (`env-levels`), and
;;; its groups, innermost first, what a name is looked for in: the ribs and
;;; the earlier repetitions' atoms of one `env-within`, ribcages passed
;;; between them, a tree by name (`ix-…`), the first binder of a name in
;;; their order kept; and each module whose names the walk does not know, a
;;; group of its own, in its place among them.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define env-types ((proj (load-module "fx26:macros-env-types.fx") rs re rm rc rp)))
(import env-types lv-rib lv-cage lv-earlier lv-shape (type level levels namer looked))
(define types-module (with env-types types-module))
(import types-module atm-lit (type atm atms))

;; Binders by name and namespace: a tree by each name's hash
;; (`symbol-name-hash`, FNV-1a, so as deep as a tree of random keys), one of
;; the same hash as a node's but another name or namespace to its right.
(define-datatype index (ix-leaf) (ix-node int symbol bool int index index))
(define-datatype group (gr-names index) (gr-shape int))
(define-type groups (listof group acyclic))
;; Abstract outside this file by what is imported of it: `macros-nodes.fx`
;; takes the type and the operations, never `env-of` (a datatype, since a
;; type `define-generative` makes, of a module a file makes, cannot be named
;; in that file's own type: `TODO.md` §235).
(define-datatype env (env-of (tupleof levels groups)))
(define down-env (->* (env) (tupleof levels groups)) (lambda (e) (tagcase e (env-of (x) x))))

(define env-empty env (env-of (tuple (the levels nil) (the groups nil))))
(define env-within (->* (env levels namer) env)
  (lambda (e ls name)
    (let ((x (down-env e)))
      (env-of (tuple (append ls (extract x 1))
                     (append (grouped ls (ix-leaf) #f name) (extract x 2)))))))
(define env-levels (->* (env) levels) (lambda (e) (extract (down-env e) 1)))
(define env-any-shape? (->* (env) bool)
  (lambda (e) (any-shape-group? (extract (down-env e) 2))))
(define any-shape-group? (->* (groups) bool)
  (lambda (gs)
    (and (not (null? gs))
         (or (tagcase (car gs) (gr-shape (m) #t) (else y #f)) (any-shape-group? (cdr gs))))))
;; `ls`'s groups, innermost first: the run of ribs to a module's level
;; one group (`ix`, `open` if it has a level yet), each module's its own.
(define grouped (->* (levels index bool namer) groups)
  (lambda (ls ix open name)
    (if (null? ls)
        (if open (list (gr-names ix)) nil)
        (tagcase (car ls)
          (lv-rib (as) (grouped (cdr ls) (indexed as ix name) #t name))
          (lv-earlier (as) (grouped (cdr ls) (indexed as ix name) #t name))
          (lv-cage (c) (grouped (cdr ls) ix open name))
          (lv-shape (m)
            (let ((rest (cons (gr-shape m) (grouped (cdr ls) (ix-leaf) #f name))))
              (if open (cons (gr-names ix) rest) rest)))))))
;; Each binder of `as` in `ix`, after those there: the first of a name kept.
(define indexed (->* (atms index namer) index)
  (lambda (as ix name)
    (if (null? as)
        ix
        (indexed (cdr as)
                 (tagcase (car as)
                   (atm-lit (b d)
                     (let ((m (name b)))
                       (if (null? m) ix (ix-kept ix (car m) (symbol-name-hash (car m)) d b))))
                   (else y ix))
                 name))))
;; `ix` with binder `b` of name `n` (hash `h`, a description's if `d`),
;; unless it has one of that name and namespace already.
(define ix-kept (->* (index symbol int bool int) index)
  (lambda (ix n h d b)
    (tagcase ix
      (ix-node (k m e x l r)
        (cond ((< h k) (ix-node k m e x (ix-kept l n h d b) r))
              ((and (= h k) (symbol=? n m) (eq? d e)) ix)
              (else (ix-node k m e x l (ix-kept r n h d b)))))
      (else y (ix-node h n d b (ix-leaf) (ix-leaf))))))
(define ix-find (->* (index symbol int bool) int)
  (lambda (ix n h d)
    (tagcase ix
      (ix-node (k m e x l r)
        (cond ((< h k) (ix-find l n h d))
              ((and (= h k) (symbol=? n m) (eq? d e)) x)
              (else (ix-find r n h d))))
      (else y -1))))
(define env-lookup (->* (env symbol bool int namer) looked)
  (lambda (e n d from name)
    (looked-in (dropped (extract (down-env e) 2) from) n (symbol-name-hash n) d from)))
(define dropped (->* (groups int) groups)
  (lambda (gs k) (if (or (= k 0) (null? gs)) gs (dropped (cdr gs) (- k 1)))))
(define looked-in (->* (groups symbol int bool int) looked)
  (lambda (gs n h d k)
    (if (null? gs)
        (tuple -1 -1 k)
        (let ((next (+ k 1)))
          (tagcase (car gs)
            (gr-names (ix)
              (let ((b (ix-find ix n h d)))
                (if (>= b 0) (tuple 0 b next) (looked-in (cdr gs) n h d next))))
            (gr-shape (m) (tuple 1 m next)))))))
