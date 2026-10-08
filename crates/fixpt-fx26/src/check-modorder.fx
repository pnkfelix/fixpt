;;; The checker, in FX-26: a module's definitions see each other, as
;;; `letrec*`'s (`DONE.md` §37). Every name a module defines is in scope in
;;; all of it, and its items are made in the order written. A typed lambda's
;;; value (a definition's, or a `define-rec` member's) may name any item: it
;;; does not run when it is made. Every other item's value runs then, so it
;;; may reach only items made before it: those it names, and those named by
;;; the lambdas it reaches, followed through them. A module breaking that is
;;; refused, naming the chain; nothing is reordered. The Rust checker's
;;; `modorder.rs`, step for step; `check-module-rules.fx` uses it.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-modorder-module (module
;; Reading the checker's tables and making lists.
(define-effect kallocs (maxeff (read @globals) (alloc @t)))
;; A module's typed lambda: its name, written type, value, the item it is
;; written in, whether that is a `define-rec`, and whether a `define*`.
(define-type k-mlam (productof (1 symbol) (2 int) (3 kx) (4 int) (5 bool) (6 bool)))
(define-type k-mlams (listof k-mlam acyclic))
;; A name a module defines, and the item defining it.
(define-type k-places (listof (productof (1 symbol) (2 int)) acyclic))

;; Whether item `it` is a definition of a lambda with a written type.
(define k-lambda-item? (subr (read @globals) (k-item) bool)
  (lambda (it)
    (and (= (extract it 1) 2) (not (null? (extract it 4))) (k-lambda? (car (extract it 5))))))
;; A `define-rec`'s members, item `i`, onto `out` (newest first).
(define k-mlams-of-group (subr kallocs (k-names k-ids kxs int k-mlams) k-mlams)
  (lambda (ns ts xs i out)
    (if (null? ns)
        out
        (k-mlams-of-group (cdr ns) (cdr ts) (cdr xs) i
                          (the k-mlams (cons (product (1 (car ns)) (2 (car ts)) (3 (car xs))
                                                      (4 i) (5 #t) (6 #f))
                                             out))))))
;; The typed lambdas of `items`, from item `i`, onto `out` (newest first).
(define k-mlams-from (subr kallocs (k-items int k-mlams) k-mlams)
  (lambda (items i out)
    (if (null? items)
        out
        (let* ((it (car items))
               (k (extract it 1))
               (more (cond ((k-lambda-item? it)
                            (the k-mlams (cons (product (1 (car (extract it 2)))
                                                        (2 (car (extract it 4)))
                                                        (3 (car (extract it 5))) (4 i) (5 #f)
                                                        (6 (= (extract it 3) -2)))
                                               out)))
                           ((= k 3) (k-mlams-of-group (extract it 2) (extract it 4) (extract it 5)
                                                      i out))
                           (else out))))
          (k-mlams-from (cdr items) (+ i 1) more)))))
;; The typed lambdas of `items`, in written order.
(define k-mod-lambdas (subr kallocs (k-items) k-mlams)
  (lambda (items) (reverse (k-mlams-from items 0 nil))))
;; The lambda of `ls` named `n`, or none.
(define k-mlam-named (subr (read @globals) (k-mlams symbol) k-mlams)
  (lambda (ls n)
    (cond ((null? ls) nil)
          ((symbol=? (extract (car ls) 1) n) ls)
          (else (k-mlam-named (cdr ls) n)))))
;; Each `define-rec` member a `lambda`, or an error at the first that is not.
(define k-mod-recs-lambdas (subr checks (k-mlams) unit)
  (lambda (ls)
    (cond ((null? ls) #u)
          ((or (not (extract (car ls) 5)) (k-lambda? (extract (car ls) 3)))
           (k-mod-recs-lambdas (cdr ls)))
          (else (k-fail-at (k-cat3 "`" (symbol->string (extract (car ls) 1))
                                   "`, in a `define-rec`, is a `lambda`")
                           (extract (car ls) 3))))))

;; A `define*` that is not a `lambda`, from `items`: an error at the first.
(define k-mod-star-lambdas (subr checks (k-items) unit)
  (lambda (items)
    (cond ((null? items) #u)
          ((and (= (extract (car items) 1) 2) (= (extract (car items) 3) -2)
                (not (k-lambda? (car (extract (car items) 5)))))
           (k-fail-at "`define*` defines a procedure: a `lambda`" (car (extract (car items) 5))))
          (else (k-mod-star-lambdas (cdr items))))))

;;; ------------------------------------------------------------ places

;; Names `ns`, each at item `i`, onto `out` (newest first).
(define k-places-onto (subr kallocs (k-names int k-places) k-places)
  (lambda (ns i out)
    (if (null? ns)
        out
        (k-places-onto (cdr ns) i (the k-places (cons (product (1 (car ns)) (2 i)) out))))))
(define k-places-from (subr kallocs (k-items int k-places) k-places)
  (lambda (items i out)
    (if (null? items)
        out
        (let* ((it (car items)) (k (extract it 1)) (ns (extract it 2))
               (more (case k ((0)
                              (let ((n (car ns)))
                                (k-places-onto (the k-names (list (k-conversion-name "up-" n)
                                                                  (k-conversion-name "down-" n)))
                                               i out)))
                             ((2 3) (k-places-onto ns i out))
                             (else out))))
          (k-places-from (cdr items) (+ i 1) more)))))
;; Each name `items` define, and the item defining it, in written order.
(define k-mod-places (subr kallocs (k-items) k-places)
  (lambda (items) (reverse (k-places-from items 0 nil))))
;; The item defining `n`, or -1.
(define k-place-of (subr (read @globals) (k-places symbol) int)
  (lambda (ps n)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) n) (extract (car ps) 2))
          (else (k-place-of (cdr ps) n)))))
;; The names of `ps` among `free`, in written order.
(define k-places-among (subr (maxeff kreads (alloc @t)) (k-places k-names) k-names)
  (lambda (ps free)
    (cond ((null? ps) nil)
          ((k-has-name? free (extract (car ps) 1))
           (the k-names (cons (extract (car ps) 1) (k-places-among (cdr ps) free))))
          (else (k-places-among (cdr ps) free)))))
;; The names free in `x` the module defines, in written order.
(define k-mod-names-in (subr kmakes (kx k-places) k-names)
  (lambda (x ps) (k-places-among ps (k-free-vars x))))

;;; ------------------------------------------------------------ modules as written

;; Whether `x` is a module as written: a `module` (or a `load-module`'s),
;; under any `plambda`, `proj`, `lambda` of no parameters or call of none;
;; an earlier such item, of `early`; or a value of one, `(with m y)`. As
;; the Rust checker's `written_module`.
(define k-written-module? (subr (maxeff kreads spin) (kx k-names) bool)
  (lambda (x early)
    (tagcase x
      (x-module (items a b) #t)
      (x-app (f args a b) (and (null? args) (k-written-module? f early)))
      (x-lambda (ps body a b) (and (null? ps) (k-written-module? body early)))
      (x-proj (body ds a b) (k-written-module? body early))
      (x-plambda (bs body a b) (k-written-module? body early))
      (x-var (n a b) (k-has-name? early n))
      (x-with (m body a b)
        (and (k-has-name? early m) (tagcase body (x-var (n c d) #t) (else y #f))))
      (else y #f))))
;; The names the module (its places `ps`) defines that a module as written
;; `x` names: of `(with m y)`, `m` only, `y` being `m`'s.
(define k-early-names-in (subr kmakes (kx k-places) k-names)
  (lambda (x ps)
    (tagcase x
      (x-with (m body a b) (if (< (k-place-of ps m) 0) nil (the k-names (cons m nil))))
      (else y (k-mod-names-in x ps)))))
;; Whether each of `ns` is one of `ks`.
(define k-all-named? (subr kreads (k-names k-names) bool)
  (lambda (ns ks) (or (null? ns) (and (k-has-name? ks (car ns)) (k-all-named? (cdr ns) ks)))))
;; The items checked before a module's typed lambdas are bound, from the
;; first, onto `early` (newest first): each with no type written whose value
;; is a module as written naming no item of the module but earlier such ones.
(define k-early-from (subr (maxeff kmakes spin) (k-items k-places k-names) k-names)
  (lambda (items ps early)
    (if (null? items)
        early
        (let* ((it (car items))
               (ok (and (= (extract it 1) 2) (null? (extract it 4))
                        (k-written-module? (car (extract it 5)) early)
                        (k-all-named? (k-early-names-in (car (extract it 5)) ps) early))))
          (k-early-from (cdr items) ps
                        (if ok (the k-names (cons (car (extract it 2)) early)) early))))))
;; Those items' names, in written order. Checked first, a module's values'
;; names are known to a `with` of it not checked yet (`k-hazard-mods`). As
;; the Rust checker's `early_modules`.
(define k-early-modules (subr (maxeff kmakes spin) (k-items) k-names)
  (lambda (items) (reverse (k-early-from items (k-mod-places items) nil))))

;;; ------------------------------------------------------------ hazards

;; What has been reached: each name, the one it was reached from, and
;; whether it was.
(define-type k-reached (listof (productof (1 symbol) (2 symbol) (3 bool)) acyclic))
(define k-reached-has? (subr (read @globals) (k-reached symbol) bool)
  (lambda (rs n) (and (not (null? rs)) (or (symbol=? (extract (car rs) 1) n)
                                           (k-reached-has? (cdr rs) n)))))
(define k-reached-of (subr (read @globals) (k-reached symbol) k-reached)
  (lambda (rs n)
    (cond ((null? rs) nil)
          ((symbol=? (extract (car rs) 1) n) rs)
          (else (k-reached-of (cdr rs) n)))))
;; Names `ns` not reached yet, each from `from` (`has`), onto `rs`.
(define k-reach-new (subr kallocs (k-names symbol bool k-reached) k-reached)
  (lambda (ns from has rs)
    (cond ((null? ns) rs)
          ((k-reached-has? rs (car ns)) (k-reach-new (cdr ns) from has rs))
          (else (k-reach-new (cdr ns) from has
                             (the k-reached (cons (product (1 (car ns)) (2 from) (3 has)) rs)))))))
;; The chain to `n`, from the value's first name it was reached through.
(define k-chain-to (subr (maxeff kallocs spin) (k-reached symbol k-names) k-names)
  (lambda (rs n out)
    (let ((r (car (k-reached-of rs n))))
      (if (extract r 3)
          (k-chain-to rs (extract r 2) (the k-names (cons n out)))
          (the k-names (cons n out))))))
;; `n`, quoted.
(define k-quote-name (subr (read @globals) (symbol) string)
  (lambda (n) (k-quote (symbol->string n))))
;; What is said of `x`, whose value reaches `chain`'s last name, not made
;; yet, through the lambdas before it: as the Rust checker's `too_soon`.
(define k-chain-rest (subr (read @globals) (k-names) string)
  (lambda (ns)
    (if (null? ns)
        ""
        (k-cat3 ", which uses " (k-quote-name (car ns)) (k-chain-rest (cdr ns))))))
(define k-too-soon (subr (read @globals) (symbol k-names) string)
  (lambda (x chain)
    (let* ((last (car (reverse chain)))
           (head (k-cat4 (k-quote-name x) " uses " (k-quote-name (car chain))
                         (k-chain-rest (cdr chain)))))
      (cond ((symbol=? last x) (string-append head ", before it is made"))
            ((null? (cdr chain)) (string-append head ", defined after it"))
            (else (k-cat3 head ", defined after " (k-quote-name x)))))))
;; Names `ns` not reached yet, in order.
(define k-not-reached (subr kallocs (k-names k-reached) k-names)
  (lambda (ns rs)
    (cond ((null? ns) nil)
          ((k-reached-has? rs (car ns)) (k-not-reached (cdr ns) rs))
          (else (the k-names (cons (car ns) (k-not-reached (cdr ns) rs)))))))
;; The module (its places and typed lambdas) and the item being checked:
;; its position, name and value.
(define-type k-hz (productof (1 k-places) (2 k-mlams) (3 int) (4 symbol) (5 kx)))
;; Breadth first from `todo` (names reached, in order), every name reached
;; in `rs`: an error at the value of `h`'s item at the first reached not
;; made before it.
(define k-hazard-walk (subr (maxeff checks spin) (k-names k-reached k-hz) unit)
  (lambda (todo rs h)
    (if (null? todo)
        #u
        (let ((n (car todo)) (ps (extract h 1)))
          (if (>= (k-place-of ps n) (extract h 3))
              (k-fail-at (k-too-soon (extract h 4) (k-chain-to rs n nil)) (extract h 5))
              (let ((l (k-mlam-named (extract h 2) n)))
                (if (null? l)
                    (k-hazard-walk (cdr todo) rs h)
                    (let* ((fresh (k-not-reached (k-mod-names-in (extract (car l) 3) ps) rs))
                           (next (append (cdr todo) fresh)))
                      (k-hazard-walk next (k-reach-new fresh n #t rs) h)))))))))
;; Refused: an item, from `i`, that is not a typed lambda whose value may
;; reach, when it is made, an item not made yet (itself included).
(define k-hazards-from (subr (maxeff checks spin) (k-items int k-places k-mlams) unit)
  (lambda (items i ps ls)
    (if (null? items)
        #u
        (let ((it (car items)))
          (begin
            (if (and (= (extract it 1) 2) (not (k-lambda-item? it)))
                (let* ((x (car (extract it 2)))
                       (init (car (extract it 5)))
                       (names (k-mod-names-in init ps)))
                  (k-hazard-walk names (k-reach-new names x #f nil)
                                 (product (1 ps) (2 ls) (3 i) (4 x) (5 init))))
                #u)
            (k-hazards-from (cdr items) (+ i 1) ps ls))))))
;; Each module checked first, of `known`, binds its values' names in a
;; `with` of it not checked yet (`k-with-bound`), so that `(define x (with m
;; x))` re-exports `m`'s `x`.
(define k-mod-hazards (subr (maxeff checks spin) (k-items k-mlams k-hazard-list) unit)
  (lambda (items ls known)
    (let* ((outer (get k-hazard-mods))
           (bound (set k-hazard-mods known))
           (r (k-hazards-from items 0 (k-mod-places items) ls)))
      (set k-hazard-mods outer))))

;;; ------------------------------------------------------------ groups

;; The lambdas of `ls` named in `names`.
(define k-mlam-names-among (subr (maxeff kreads (alloc @t)) (k-mlams k-names) k-names)
  (lambda (ls names)
    (cond ((null? ls) nil)
          ((k-has-name? names (extract (car ls) 1))
           (the k-names (cons (extract (car ls) 1) (k-mlam-names-among (cdr ls) names))))
          (else (k-mlam-names-among (cdr ls) names)))))
;; Each lambda's name, and the lambdas its value names.
(define-type k-edges (listof (productof (1 symbol) (2 k-names)) acyclic))
(define k-mod-edges (subr kmakes (k-mlams k-mlams) k-edges)
  (lambda (ls all)
    (if (null? ls)
        nil
        (the k-edges (cons (product (1 (extract (car ls) 1))
                                    (2 (k-mlam-names-among all (k-free-vars (extract (car ls) 3)))))
                           (k-mod-edges (cdr ls) all))))))
;; The lambdas' strongly connected components (Tarjan's): each lambda's
;; place in the walk, its low link, and its component, by name; the walk's
;; stack, and the counts of places and of components. A lambda walked and
;; not yet in a component is on the stack. Linear in the lambdas and their
;; edges, where reaching from each lambda in turn was cubic, with lists.
(define-type k-scc-ints (table symbol int @t))
(define k-scc-edges (ref (table symbol k-names @t) @t) (new (make-table symbol-hash symbol=?)))
(define k-scc-index (ref k-scc-ints @t) (new (make-table symbol-hash symbol=?)))
(define k-scc-low (ref k-scc-ints @t) (new (make-table symbol-hash symbol=?)))
(define k-scc-comp (ref k-scc-ints @t) (new (make-table symbol-hash symbol=?)))
(define k-scc-stack (ref k-names @t) (new nil))
(define k-scc-count (ref int @t) (new 0))
(define k-scc-comps (ref int @t) (new 0))
(define k-scc-get (subr (maxeff (read @globals) (read @t)) ((ref k-scc-ints @t) symbol) int)
  (lambda (t n) (table-ref (get t) n -1)))
(define k-scc-low-to (subr kstate (symbol int) unit)
  (lambda (v x) (if (< x (k-scc-get k-scc-low v)) (table-set! (get k-scc-low) v x) #u)))
;; The stack popped down to `v`, each lambda popped in component `c`.
(define k-scc-pop (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (v c)
    (let ((w (car (get k-scc-stack))))
      (begin (set k-scc-stack (cdr (get k-scc-stack)))
             (table-set! (get k-scc-comp) w c)
             (if (symbol=? w v) #u (k-scc-pop v c))))))
(define-rec
  (k-scc-visit (subr (maxeff kstate spin) (symbol) unit)
    (lambda (v)
      (let ((i (get k-scc-count)))
        (begin (table-set! (get k-scc-index) v i)
               (table-set! (get k-scc-low) v i)
               (set k-scc-count (+ i 1))
               (set k-scc-stack (cons v (get k-scc-stack)))
               (k-scc-succs v (table-ref (get k-scc-edges) v (the k-names nil)))
               (if (= (k-scc-get k-scc-low v) i)
                   (let ((c (get k-scc-comps))) (begin (set k-scc-comps (+ c 1)) (k-scc-pop v c)))
                   #u)))))
  (k-scc-succs (subr (maxeff kstate spin) (symbol k-names) unit)
    (lambda (v ws)
      (if (null? ws)
          #u
          (let ((w (car ws)))
            (begin
              (cond ((< (k-scc-get k-scc-index w) 0)
                     (begin (k-scc-visit w) (k-scc-low-to v (k-scc-get k-scc-low w))))
                    ((< (k-scc-get k-scc-comp w) 0) (k-scc-low-to v (k-scc-get k-scc-index w)))
                    (else #u))
              (k-scc-succs v (cdr ws))))))))
;; Each lambda of `es` walked, in order, from a fresh start.
(define k-scc-walk (subr (maxeff kstate spin) (k-edges) unit)
  (lambda (es)
    (if (null? es)
        #u
        (begin (if (< (k-scc-get k-scc-index (extract (car es) 1)) 0)
                   (k-scc-visit (extract (car es) 1))
                   #u)
               (k-scc-walk (cdr es))))))
(define k-scc-note-edges (subr kstate (k-edges) unit)
  (lambda (es)
    (if (null? es)
        #u
        (begin (table-set! (get k-scc-edges) (extract (car es) 1) (extract (car es) 2))
               (k-scc-note-edges (cdr es))))))
(define k-scc-start (subr kstate (k-edges) unit)
  (lambda (es)
    (begin (set k-scc-edges (make-table symbol-hash symbol=?))
           (set k-scc-index (make-table symbol-hash symbol=?))
           (set k-scc-low (make-table symbol-hash symbol=?))
           (set k-scc-comp (make-table symbol-hash symbol=?))
           (set k-scc-stack nil) (set k-scc-count 0) (set k-scc-comps 0)
           (k-scc-note-edges es))))
;; Whether lambda `a` is on a cycle: it names itself, or another is in its
;; component (of `bs`).
(define k-scc-cyclic? (subr (maxeff (read @globals) (read @t)) (symbol k-letrec-bs) bool)
  (lambda (a bs)
    (or (k-has-name? (table-ref (get k-scc-edges) a (the k-names nil)) a)
        (letrec ((other (subr (maxeff (read @globals) (read @t)) (k-letrec-bs) bool)
                   (lambda (bs)
                     (and (not (null? bs))
                          (let ((b (extract (car bs) 1)))
                            (or (and (not (symbol=? b a))
                                     (= (k-scc-get k-scc-comp b) (k-scc-get k-scc-comp a)))
                                (other (cdr bs))))))))
          (other bs)))))
;; The recursive group of the lambda named `a`, in written order, its
;; bindings from `bs`: those in its component, if it is on a cycle; none if
;; it is in none.
(define k-mod-group (subr (maxeff kreads (alloc @t)) (symbol k-letrec-bs) k-letrec-bs)
  (lambda (a bs)
    (let ((c (k-scc-get k-scc-comp a)))
      (letrec ((members (subr (maxeff kreads (alloc @t)) (k-letrec-bs) k-letrec-bs)
                 (lambda (bs)
                   (cond ((null? bs) nil)
                         ((= (k-scc-get k-scc-comp (extract (car bs) 1)) c)
                          (the k-letrec-bs (cons (car bs) (members (cdr bs)))))
                         (else (members (cdr bs)))))))
        (if (k-scc-cyclic? a bs) (members bs) (the k-letrec-bs nil))))))
;; Each of `ls`'s recursive group (`k-mod-group`), in order.
(define-type k-groups (listof k-letrec-bs acyclic))
(define k-groups-of (subr (maxeff kreads (alloc @t)) (k-letrec-bs k-letrec-bs) k-groups)
  (lambda (ls all)
    (if (null? ls)
        nil
        (the k-groups (cons (k-mod-group (extract (car ls) 1) all) (k-groups-of (cdr ls) all))))))
;; The same, of the lambdas' edges `es`.
(define k-mod-groups (subr (maxeff kstate spin) (k-edges k-letrec-bs k-letrec-bs) k-groups)
  (lambda (es ls all) (begin (k-scc-start es) (k-scc-walk es) (k-groups-of ls all))))))

(define-type k-mlam (select check-modorder-module k-mlam))
(define-type k-mlams (select check-modorder-module k-mlams))
(define-type k-places (select check-modorder-module k-places))
(define k-lambda-item? (with check-modorder-module k-lambda-item?))
(define k-mod-lambdas (with check-modorder-module k-mod-lambdas))
(define k-mod-recs-lambdas (with check-modorder-module k-mod-recs-lambdas))
(define k-mod-star-lambdas (with check-modorder-module k-mod-star-lambdas))
(define k-place-of (with check-modorder-module k-place-of))
(define k-mod-hazards (with check-modorder-module k-mod-hazards))
(define k-early-modules (with check-modorder-module k-early-modules))
(define k-mod-edges (with check-modorder-module k-mod-edges))
(define-type k-groups (select check-modorder-module k-groups))
(define k-mod-groups (with check-modorder-module k-mod-groups))
