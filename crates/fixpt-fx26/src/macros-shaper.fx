;;; Binding shapes, in FX-26 (`docs/research/binding-shapes.md`;
;;; `macros/shapes.rs`'s `Shaper`): what the modules a program's forms open
;;; give, as its walk (`macros-walk.fx`) finds them bound, and what each
;;; reference asks of them. Part of the expander: loaded by
;;; `macros-shapes.fx`, and loading `macros-walk.fx`.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define tree-module ((proj (load-module "fx26:macros-tree.fx") rs re rm rc rp)))
(define walk-module (with tree-module walk-module))
(import tree-module tree-begin! parent-of position elems elem under?)
(define scopes-module (with walk-module scopes-module))
(define align-module (with scopes-module align-module))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted vec (type syn))
(import parser-module parse-tag p-ok p-err syn-symbol? syn-symbol syn-name mk-symbol mk-list len
        nth syn-string? syn-datums sh-module sh-fun
        (type syns-a names presult loaded-file loaded-files shape shapes members)
        (effect parses tree-builds))
(import types-module kind-of proper-items s-item s-expr syn-keyword? split
        (type fails addr atm atms))
(import align-module align node-export node-imports node-syn node-core node-kids node-path nnodes
        nodes-reset!
        program-walk unplaced lv-rib lv-earlier lv-shape lv-cage k-binder k-ref k-form k-pair
        k-desc k-seq atm-lit
        env-empty env-lookup binder-name
        (type level levels found rooted env))
(import scopes-module walk evaluate)
(import walk-module walked pfail-walk walked-out show-renamed falses addr=? int-in?)

;;; ------------------------------------------------------------ shapes

;; Shapes (`shape`, `shapes`, `members`): `parser-types.fx`'s, which the
;; checker makes too, of the types it knows (`k-type-shape`).
(define one (->* (shape) shapes) (lambda (x) (list x)))
;; A function's shape, if anything of it is known.
(define sh-fun-of (->* ((listof shapes acyclic) shapes) shapes)
  (lambda (ps r) (if (or (not (null? r)) (any-known? ps)) (one (sh-fun ps r)) nil)))
(define any-known? (->* ((listof shapes acyclic)) bool)
  (lambda (ps) (and (not (null? ps)) (or (not (null? (car ps))) (any-known? (cdr ps))))))
;; Member `n` of members `ms`, in a list of one.
(define member-of (->* (symbol members) (listof (tupleof symbol shapes) acyclic))
  (lambda (n ms)
    (cond ((null? ms) nil)
          ((symbol=? n (extract (car ms) 1)) (list (car ms)))
          (else (member-of n (cdr ms))))))
;; Members by name, for as many as the top level has (`top-vals`): a tree
;; by each name's hash (`symbol-name-hash`, FNV-1a, so as deep as a
;; tree of random keys), a name of the same hash as a node's but another
;; to its right; persistent, so that each form's reading state keeps the
;; top level's as they were (`shapes-after!`) for nothing. Added and found
;; in the tree's depth, where a list of them was copied whole for each name
;; added (`with-member`) and walked for each found (`member-of`).
(define-datatype name-tree (nm-leaf) (nm-node int symbol shapes name-tree name-tree))
;; Member `n` of `t`, in a list of one, as `member-of` gives it.
(define names-find (->* (symbol name-tree) (listof (tupleof symbol shapes) acyclic))
  (lambda (n t) (names-find-hashed n (symbol-name-hash n) t)))
(define names-find-hashed (->* (symbol int name-tree) (listof (tupleof symbol shapes) acyclic))
  (lambda (n h t)
    (tagcase t
      (nm-node (k m s l r)
        (cond ((< h k) (names-find-hashed n h l))
              ((and (= h k) (symbol=? n m)) (list (tuple m s)))
              (else (names-find-hashed n h r))))
      (else y nil))))
;; `t` with `n` (its shape `s`) in its place, a later one of a name in its
;; place.
(define names-with (->* (name-tree symbol shapes) name-tree)
  (lambda (t n s) (names-with-hashed t n (symbol-name-hash n) s)))
(define names-with-hashed (->* (name-tree symbol int shapes) name-tree)
  (lambda (t n h s)
    (tagcase t
      (nm-node (k m x l r)
        (cond ((< h k) (nm-node k m x (names-with-hashed l n h s) r))
              ((and (= h k) (symbol=? n m)) (nm-node k m s l r))
              (else (nm-node k m x l (names-with-hashed r n h s)))))
      (else y (nm-node h n s (nm-leaf) (nm-leaf))))))
;; Each of members `xs` onto `t`, in order.
(define names-onto (->* (members name-tree) name-tree)
  (lambda (xs t)
    (if (null? xs)
        t
        (names-onto (cdr xs) (names-with t (extract (car xs) 1) (extract (car xs) 2))))))
(define names-empty? (->* (name-tree) bool)
  (lambda (t) (tagcase t (nm-leaf () #t) (else y #f))))
;; Whether shape `s` gives `n`, a description's if `d`, else a value's.
(define gives? (->* (shapes symbol bool) bool)
  (lambda (s n d)
    (and (not (null? s))
         (tagcase (car s)
           (sh-module (vs ds) (not (null? (member-of n (if d ds vs)))))
           (else y #f)))))
;; Name `n`'s own shape in `s`, a description's if `d`.
(define member-shape (->* (shapes symbol bool) shapes)
  (lambda (s n d)
    (if (null? s)
        nil
        (tagcase (car s)
          (sh-module (vs ds)
            (let ((m (member-of n (if d ds vs)))) (if (null? m) nil (extract (car m) 2))))
          (else y nil)))))
(define result-of (->* (shapes) shapes)
  (lambda (s) (if (null? s) nil (tagcase (car s) (sh-fun (ps r) r) (else y nil)))))
(define param-of (->* (shapes int) shapes)
  (lambda (s k)
    (if (null? s) nil (tagcase (car s) (sh-fun (ps r) (shape-at ps k)) (else y nil)))))
;; The `k`th of `ps`, or none.
(define shape-at (->* ((listof shapes acyclic) int) shapes)
  (lambda (ps k) (cond ((null? ps) nil) ((= k 0) (car ps)) (else (shape-at (cdr ps) (- k 1))))))
;; The last of `xs`, or -1.
(define last-int (->* ((listof int acyclic)) int)
  (lambda (xs) (cond ((null? xs) -1) ((null? (cdr xs)) (car xs)) (else (last-int (cdr xs))))))
(define int-at (->* ((listof int acyclic) int) int)
  (lambda (xs k) (cond ((null? xs) -1) ((= k 0) (car xs)) (else (int-at (cdr xs) (- k 1))))))
;; `ms` with `n` (its shape `s`) in its place, a later one of a name in its
;; place.
(define with-member (->* (members symbol shapes) members)
  (lambda (ms n s) (append (without-member ms n) (the members (list (tuple n s))))))
(define without-member (->* (members symbol) members)
  (lambda (ms n)
    (cond ((null? ms) nil)
          ((symbol=? n (extract (car ms) 1)) (without-member (cdr ms) n))
          (else (cons (car ms) (without-member (cdr ms) n))))))
(define members-onto (->* (members members) members)
  (lambda (xs ms)
          (if (null? xs) ms
              (members-onto (cdr xs) (with-member ms (extract (car xs) 1) (extract (car xs) 2))))))
;; `xs` onto `out`, the last first.
(define members-reversed (->* (members members) members)
  (lambda (xs out) (if (null? xs) out (members-reversed (cdr xs) (cons (car xs) out)))))
;; Of `rs`, gathered the last first, each name's last, in the order of the
;; last definitions; `seen`, the names already kept, onto `out`.
(define members-latest (->* (members name-tree members) members)
  (lambda (rs seen out)
    (cond ((null? rs) out)
          ((not (null? (names-find (extract (car rs) 1) seen))) (members-latest (cdr rs) seen out))
          (else (members-latest (cdr rs) (names-with seen (extract (car rs) 1) nil)
                                (cons (car rs) out))))))
;; Those of `ms` that `hidden` has not.
(define members-hidden (->* (members name-tree) members)
  (lambda (ms hidden)
    (cond ((null? ms) nil)
          ((not (null? (names-find (extract (car ms) 1) hidden))) (members-hidden (cdr ms) hidden))
          (else (cons (car ms) (members-hidden (cdr ms) hidden))))))
(define top-vals (ref name-tree rs) (new (nm-leaf)))
(define top-descs (ref name-tree rs) (new (nm-leaf)))
(define shaping-top (ref bool rs) (new #f))
(define-type file-shape (tupleof string shapes shapes syns-a))
(define file-shapes (ref (listof file-shape acyclic) rs) (new nil))
(define file-shape-keyed (->* (string (listof file-shape acyclic)) (listof file-shape acyclic))
  (lambda (key fs)
    (cond ((null? fs) nil)
          ((string=? key (extract (car fs) 1)) (list (car fs)))
          (else (file-shape-keyed key (cdr fs))))))
;; The files the driver read, by where each load starts (`parser-loads.fx`).
(define files-given (ref loaded-files rs) (new nil))
(define file-given-at (->* (int loaded-files) loaded-files)
  (lambda (a fs)
    (cond ((null? fs) nil)
          ((= a (extract (car fs) 1)) (list (car fs)))
          (else (file-given-at a (cdr fs))))))
;; The key of file `f`, loaded as an input's if `input?`, as `parse-loaded`
;; makes it: what its hidden global is named by, `%shared:key`.
(define file-key (->* (loaded-file bool) string)
  (lambda (f input?)
    (let ((raw (extract f 7)))
      (if (input-key? raw) raw (string-append (if input? "input:" "") raw)))))
(define input-key? (->* (string) bool)
  (lambda (k) (and (> (string-length k) 6) (string=? (substring k 0 6) "input:"))))
;; The shape of the file a load at `a` reads, in a list of one.
(define file-at (->* (int) (listof file-shape acyclic))
  (lambda (a)
    (let ((f (file-given-at a (get files-given))))
      (if (null? f) nil (file-shape-keyed (file-key (car f) (load-input-at? a))
                                          (get file-shapes))))))
;; What the load at `a` makes, or (`module?`) the module it describes: its
;; file's shape; or, its file made by a form before and not read for this
;; one, its hidden global's, `%shared:key`, as the top level has it.
(define load-shape (->* (int bool) shapes)
  (lambda (a module?)
    (let* ((f (file-at a))
           (known (cond ((null? f) nil) (module? (extract (car f) 3)) (else (extract (car f) 2)))))
      (cond ((not (null? known)) known)
            (else
             (let ((g (file-given-at a (get files-given))))
               (if (null? g)
                   nil
                   (let* ((input? (load-input-at? a))
                          (v (names-find (string->symbol
                                          (string-append "%shared:" (file-key (car g) input?)))
                                         (get top-vals)))
                          (s (if (null? v) nil (extract (car v) 2))))
                     (if (and module? input?) (result-of s) s)))))))))
;; Whether the load at `a` is an input's, as the prepass noted it.
(define inputs-at (ref (listof int acyclic) rs) (new nil))
(define load-input-at? (->* (int) bool)
  (lambda (a) (int-in? a (get inputs-at))))
;; The program's top level and files forgotten, for another; its files
;; `fs`.
(define shapes-reset! (->* (loaded-files) unit)
  (lambda (fs)
    (begin (set top-vals (nm-leaf)) (set top-descs (nm-leaf)) (set file-shapes nil)
           (set inputs-at nil)
           (set files-given fs))))
;; The files the driver read for the forms to come, `fs`.
(define shapes-files! (->* (loaded-files) unit)
  (lambda (fs) (set files-given fs)))

;;; ------------------------------------------------------------ one walk's shapes

;; The walk's: each node's environment if the walk found it (its tree:
;; `macros-tree.fx`); each node's shape as an expression and as a type, once
;; found (0 not yet, 1 being found, 2 found); what each module, by its
;; expression's node, was asked; and whether each node is in a module an
;; `include` includes.
(define envs (ref (arrayof env rs) rs) (new (make-array 1 env-empty)))
(define exp-state (ref (arrayof int rs) rs) (new (make-array 1 0)))
(define exp-made (ref (arrayof shapes rs) rs) (new (make-array 1 (the shapes nil))))
(define ty-state (ref (arrayof int rs) rs) (new (make-array 1 0)))
(define ty-made (ref (arrayof shapes rs) rs) (new (make-array 1 (the shapes nil))))
(define in-included (ref (arrayof bool rs) rs) (new (make-array 1 #f)))
;; What a module was asked: each name, a description's or a value's, and
;; whether it gives it; and whether its shape was not known where asked.
(define-type asked (tupleof (listof (tupleof symbol bool bool) acyclic) bool))
;; By each module's node: the names asked, the last first; those of
;; values and of descriptions, by name; whether its shape was not known
;; where asked. And what each module gives, by name, once found.
(define ask-names (ref (arrayof (listof (tupleof symbol bool bool) acyclic) rs) rs)
  (new (make-array 1 (the (listof (tupleof symbol bool bool) acyclic) nil))))
(define ask-vals (ref (arrayof name-tree rs) rs) (new (make-array 1 (nm-leaf))))
(define ask-descs (ref (arrayof name-tree rs) rs) (new (make-array 1 (nm-leaf))))
(define ask-unknown (ref (arrayof bool rs) rs) (new (make-array 1 #f)))
(define given-done (ref (arrayof bool rs) rs) (new (make-array 1 #f)))
(define given-vals (ref (arrayof name-tree rs) rs) (new (make-array 1 (nm-leaf))))
(define given-descs (ref (arrayof name-tree rs) rs) (new (make-array 1 (nm-leaf))))
;; The walk of form `form`'s state made, its root `root`, what it found
;; `found`.
(define shaper-begin! (->* (int found) unit)
  (lambda (root found)
    (let ((n (get nnodes)))
      (begin
        (tree-begin! n)
        (set envs (the (arrayof env rs) (make-array n env-empty)))
        (set exp-state (the (arrayof int rs) (make-array n 0)))
        (set exp-made (the (arrayof shapes rs) (make-array n (the shapes nil))))
        (set ty-state (the (arrayof int rs) (make-array n 0)))
        (set ty-made (the (arrayof shapes rs) (make-array n (the shapes nil))))
        (set in-included (the (arrayof bool rs) (make-array n #f)))
        (set ask-names (the (arrayof (listof (tupleof symbol bool bool) acyclic) rs)
                            (make-array n (the (listof (tupleof symbol bool bool) acyclic) nil))))
        (set ask-vals (the (arrayof name-tree rs) (make-array n (nm-leaf))))
        (set ask-descs (the (arrayof name-tree rs) (make-array n (nm-leaf))))
        (set ask-unknown (the (arrayof bool rs) (make-array n #f)))
        (set given-done (the (arrayof bool rs) (make-array n #f)))
        (set given-vals (the (arrayof name-tree rs) (make-array n (nm-leaf))))
        (set given-descs (the (arrayof name-tree rs) (make-array n (nm-leaf))))
        (envs-from found)
        (includes-marked 0 n)))))
(define envs-from (->* (found) unit)
  (lambda (fs)
    (if (null? fs)
        #u
        (begin (array-set! (get envs) (extract (car fs) 1) (extract (car fs) 2))
               (envs-from (cdr fs))))))
;; Each node in a module an `include` includes, marked.
(define includes-marked (->* (int int) unit)
  (lambda (i n)
    (if (= i n)
        #u
        (begin
          (if (and (form-node? i) (head-is? (node-syn i) 'include))
              (let ((m (elem i 1))) (if (>= m 0) (mark-under m) #u))
              #u)
          (includes-marked (+ i 1) n)))))
(define mark-under (->* (int) unit)
  (lambda (x)
    (begin
      (array-set! (get in-included) x #t)
      (tagcase (node-kids x)
        (k-pair (a d) (begin (mark-under a) (mark-under d)))
        (k-form (y) (mark-under y))
        (k-seq (y) (mark-under y))
        (k-desc (ys) (mark-each ys))
        (else y #u)))))
(define mark-each (->* ((listof int acyclic)) unit)
  (lambda (xs) (if (null? xs) #u (begin (mark-under (car xs)) (mark-each (cdr xs))))))
(define form-node? (->* (int) bool)
  (lambda (i) (tagcase (node-kids i) (k-form (x) #t) (else y #f))))
;; The name at the head of list `s`, or "".
(define head-of (->* (syn) string)
  (lambda (s)
    (let ((items (proper-items s)))
      (if (and (not (null? items)) (syn-symbol? (car items))) (syn-name (car items)) ""))))
;; The name at the head of list `s`, or `no-head`: asked of every list a
;; pass reaches, its name not made a string (`head-of`).
(define no-head symbol (string->symbol ""))
(define head-sym (->* (syn) symbol)
  (lambda (s)
    (let ((items (proper-items s)))
      (if (and (not (null? items)) (syn-symbol? (car items))) (syn-symbol (car items)) no-head))))
(define head-is? (->* (syn symbol) bool) (lambda (s n) (symbol=? (head-sym s) n)))
;;; ------------------------------------------------------------ where a value comes from

;; Where binder `b`'s value comes from (`macros/shapes.rs`'s `Source`): the
;; expression bound (0), a type declared (1), a member of the module at a
;; node (2, its name), the `k`th parameter of the procedure type a name
;; names (3), parameter `i` of the function given as argument `k` to the
;; operator at a node (4); none (-1).
(define-type source (tupleof int int int int symbol))
(define no-source source (tuple -1 0 0 0 '-))
(define source-of (->* (fails int) source)
  (lambda (fail b)
    (let* ((pq (position b)) (q (extract pq 1)) (i (extract pq 2)))
      (if (< q 0)
          no-source
          (let ((fq (position q)))
            (cond
              ;; A lambda's parameter of no type of its own: the procedure
              ;; type the lambda is declared at says it.
              ((and (= (extract fq 2) 1) (>= (extract fq 1) 0)
                    (string=? (head-of (node-syn (extract fq 1))) "lambda"))
               (let ((d (declared-param (extract fq 1) i)))
                 (if (>= (extract d 1) 0) d (argument-param (extract fq 1) i))))
              ;; A description function's name, `(define-type (f …) T)`.
              ((and (= i 0) (= (extract fq 2) 1) (>= (extract fq 1) 0)
                    (string=? (head-of (node-syn (extract fq 1))) "define-type"))
               (tuple 1 (elem (extract fq 1) 2) 0 0 '-))
              (else (source-in-list b q i))))))))
(define source-in-list (->* (int int int) source)
  (lambda (b q i)
    (let* ((list (node-syn q)) (n (len (proper-items list))) (head (head-of list)))
      (cond
        ((and (string=? head "define") (= i 1) (= n 3)) (tuple 0 (elem q 2) 0 0 '-))
        ((and (or (string=? head "define") (string=? head "define*")) (= i 1) (= n 4))
         (tuple 1 (elem q 2) 0 0 '-))
        ((and (string=? head "define-type") (= i 1) (= n 3)) (tuple 1 (elem q 2) 0 0 '-))
        ((and (string=? head "import") (>= i 2))
         (tagcase (node-kids b)
           (k-binder (m d) (if d no-source (tuple 2 (elem q 1) 0 0 m)))
           (else y no-source)))
        ;; An element of a list of bindings, `(x e)`, `(x T)`, `(x T e)`:
        ;; which, by the form whose operand the list is.
        ((and (= i 0) (or (= n 2) (= n 3)))
         (let* ((r (extract (position q) 1))
                (fk (if (>= r 0) (position r) (tuple -1 0)))
                (f (extract fk 1)) (k (extract fk 2)) (second (elem q 1))
                (fh (if (>= f 0) (head-of (node-syn f)) "")))
           (cond ((and (= k 1) (or (string=? fh "let") (string=? fh "let*") (string=? fh "par")))
                  (tuple 0 second 0 0 '-))
                 ((or (and (= k 1) (or (string=? fh "letrec") (string=? fh "lambda")
                                       (string=? fh "module-parameters")))
                      (and (= k 2) (string=? fh "rlambda")))
                  (tuple 1 second 0 0 '-))
                 (else no-source))))
        (else no-source)))))
;; The `k`th parameter of lambda `f` as the type it is declared at writes
;; it: a typed `define`'s or a `the`'s, through `plambda`s, in a `subr` or
;; `->` under `poly`s and `allof`s.
(define declared-param (->* (int int) source)
  (lambda (f k)
    (let ((t (declared-type f)))
      (if (< t 0) no-source (param-of-type t k)))))
(define declared-type (->* (int) int)
  (lambda (at)
    (let* ((pi (position at)) (p (extract pi 1)) (i (extract pi 2))
           (h (if (>= p 0) (head-of (node-syn p)) "")))
      (cond ((< p 0) -1)
            ((and (string=? h "plambda") (= i 2)) (declared-type p))
            ((and (or (string=? h "define") (string=? h "define*")) (= i 3)) (elem p 2))
            ((and (string=? h "the") (= i 2)) (elem p 1))
            (else -1)))))
(define param-of-type (->* (int int) source)
  (lambda (t k)
    (let* ((s (node-syn t)) (h (head-of s)) (items (proper-items s)))
      (cond
        ((syn-symbol? s) (tuple 3 0 0 k (syn-symbol s)))
        ((or (string=? h "allof") (string=? h "poly"))
         (let ((x (elem t (if (string=? h "allof") 1 (- (len items) 1)))))
           (if (< x 0) no-source (param-of-type x k))))
        ((or (string=? h "->") (string=? h "subr"))
         (let* ((conv (and (string=? h "subr") (> (len items) 1)
                           (string=? (head-of (nth items 1)) "conv")))
                (ps (elem t (cond ((string=? h "->") 1) (conv 3) (else 2))))
                (p (if (< ps 0) -1 (elem ps k))))
           (cond ((< p 0) no-source)
                 ((dependent? (node-syn p)) (tuple 1 (elem p 2) 0 0 '-))
                 (else (tuple 1 p 0 0 '-)))))
        (else no-source)))))
;; Whether `s` is a dependent parameter, `(c : T)`.
(define dependent? (->* (syn) bool)
  (lambda (s)
    (let ((items (proper-items s)))
      (and (= (len items) 3) (syn-symbol? (nth items 1)) (string=? (syn-name (nth items 1)) ":")))))
;; Parameter `i` of lambda `f`, given as an argument of an application.
(define argument-param (->* (int int) source)
  (lambda (f i)
    (let* ((pj (position f)) (app (extract pj 1)) (j (extract pj 2))
           (op (if (>= app 0) (operator app) -1)))
      (if (and (>= op 0) (>= j 1)) (tuple 4 op (- j 1) i '-) no-source))))
;; The node of application `at`'s operator, or -1.
(define operator (->* (int) int)
  (lambda (at)
    (tagcase (node-kids at)
      (k-form (x)
        (if (addr=? (node-path x) (node-path at))
            (tagcase (node-kids x) (k-pair (f d) f) (else y -1))
            -1))
      (else y -1))))
(define binder-shape (->* (fails int) shapes)
  (lambda (fail b)
    (let ((src (source-of fail b)))
      (case (extract src 1)
        ((0) (exp-shape fail (extract src 2)))
        ((1) (ty-shape fail (extract src 2)))
        ((2) (member-shape (exp-shape fail (extract src 2)) (extract src 5) #f))
        ;; The `k`th parameter of the procedure type a name names, as the
        ;; checker has the type (`global-shape`).
        ((3) (param-of (global-shape (extract src 5) #t) (extract src 4)))
        ((4) (param-of (param-of (exp-shape fail (extract src 2)) (extract src 3)) (extract src 4)))
        (else nil)))))

;;; ------------------------------------------------------------ what a name is bound by

;; What reference `at`, of `n`, a description's if `d`, is bound by: a
;; binder's node (>= 0); the module a `with` or `include` opens around it
;; that gives it (its node in the second); free (-1); or, past a module
;; whose shape is not known, not to be said (-2). Each module looked at is
;; asked, and the answer kept (`askeds`).
(define resolve (->* (fails int symbol bool) (tupleof int int))
  (lambda (fail at n d) (resolve-in fail at n d (array-ref (get envs) at) 0)))
(define resolve-in (->* (fails int symbol bool env int) (tupleof int int))
  (lambda (fail at n d env from)
    (let* ((l (env-lookup env n d from binder-name)) (m (extract l 2)) (next (extract l 3)))
      (case (extract l 1)
        ((0) (tuple m 0))
        ((1)
         ;; A module's own expression is not in the scope of what it gives;
         ;; nor is an `include`'s of what any includes.
         (if (or (under? at m) (and (array-ref (get in-included) at) (included? m)))
             (resolve-in fail at n d env next)
             (let ((s (exp-shape fail m)))
               (if (null? s)
                   (begin (ask! m n d #f #t) (tuple -2 0))
                   (let ((given (node-gives? m s n d)))
                     (begin (ask! m n d given #f)
                            (if given (tuple -3 m) (resolve-in fail at n d env next))))))))
        (else (tuple -1 0))))))
(define binder-named (->* (symbol bool atms) int)
  (lambda (n d as)
    (if (null? as)
        -1
        (tagcase (car as)
          (atm-lit (b e)
            (if (and (eq? d e) (tagcase (node-kids b) (k-binder (m f) (symbol=? m n)) (else y #f)))
                b
                (binder-named n d (cdr as))))
          (else y (binder-named n d (cdr as)))))))
;; Whether node `m` is the module an `include` includes.
(define included? (->* (int) bool)
  (lambda (m)
    (let ((fi (position m)))
      (and (= (extract fi 2) 1) (>= (extract fi 1) 0)
           (head-is? (node-syn (extract fi 1)) 'include)))))
;; Module `m` asked for `n`, and its answer.
(define ask! (->* (int symbol bool bool bool) unit)
  (lambda (m n d given unknown)
    (cond (unknown (array-set! (get ask-unknown) m #t))
          ((not (null? (names-find n (array-ref (get (if d ask-descs ask-vals)) m)))) #u)
          (else
           (begin
             (array-set! (get (if d ask-descs ask-vals)) m
                         (names-with (array-ref (get (if d ask-descs ask-vals)) m) n nil))
             (array-set! (get ask-names) m
                         (cons (tuple n d given) (array-ref (get ask-names) m))))))))
;; What module `m` was asked, in the order asked.
(define asked-of (->* (int) asked)
  (lambda (m)
    (if (< m 0)
        (tuple nil #f)
        (tuple (reverse (array-ref (get ask-names) m)) (array-ref (get ask-unknown) m)))))
;; Whether module `m`, of shape `s`, gives `n`; its shape there: by names
;; found once for each module node (`given-by`), not its members searched.
(define node-gives? (->* (int shapes symbol bool) bool)
  (lambda (m s n d) (not (null? (names-find n (given-by m s d))))))
(define node-member-shape (->* (int shapes symbol bool) shapes)
  (lambda (m s n d)
    (let ((x (names-find n (given-by m s d)))) (if (null? x) nil (extract (car x) 2)))))
(define given-by (->* (int shapes bool) name-tree)
  (lambda (m s d)
    (begin
      (if (array-ref (get given-done) m)
          #u
          (let ((both (tagcase (if (null? s) (sh-module nil nil) (car s))
                        (sh-module (vs ds) (tuple (names-first vs) (names-first ds)))
                        (else y (tuple (nm-leaf) (nm-leaf))))))
            (begin (array-set! (get given-vals) m (extract both 1))
                   (array-set! (get given-descs) m (extract both 2))
                   (array-set! (get given-done) m #t))))
      (array-ref (get (if d given-descs given-vals)) m))))
;; Members `ms` by name, the first of a name kept, as `member-of` finds it.
(define names-first (->* (members) name-tree)
  (lambda (ms) (names-onto (members-reversed ms nil) (nm-leaf))))
;; The shape of what reference `at`, of `n`, refers to.
(define reference (->* (fails int symbol bool) shapes)
  (lambda (fail at n d)
    (let* ((r (resolve fail at n d)) (b (extract r 1)))
      (cond ((>= b 0) (binder-shape fail b))
            ((= b -3) (node-member-shape (extract r 2) (exp-shape fail (extract r 2)) n d))
            ((= b -1) (top-shape n d))
            (else nil)))))
;; A top-level name's shape; a file's hidden global's, its file's.
(define top-shape (->* (symbol bool) shapes)
  (lambda (n d)
    (let* ((name (symbol->string n))
           (shared (and (not d) (> (string-length name) 8)
                        (string=? (substring name 0 8) "%shared:")))
           (m (if (get shaping-top) (names-find n (get (if d top-descs top-vals))) nil)))
      (cond ((and (not (null? m)) (not (null? (extract (car m) 2)))) (extract (car m) 2))
            (shared
             (let ((f (file-shape-keyed (substring name 8 (string-length name)) (get file-shapes))))
               (if (null? f) (global-shape n d) (extract (car f) 2))))
            ;; Else as the checker found its type: a definition read from a
            ;; `.fasl`, a stage's module, which no form read here defines.
            (else (global-shape n d))))))
;; The top level's names' shapes as the checker has their types, for the
;; forms to be parsed (`check-global-shapes!`): values', descriptions'.
(define global-vals (ref name-tree rs) (new (nm-leaf)))
(define global-descs (ref name-tree rs) (new (nm-leaf)))
(define globals-given! (->* (members members) unit)
  (lambda (vs ds)
    (begin (set global-vals (names-onto vs (nm-leaf)))
           (set global-descs (names-onto ds (nm-leaf))))))
;; Name `n`'s shape, a description's if `d`, as the checker has its type
;; (`Global`): of a top-level form only.
(define global-shape (->* (symbol bool) shapes)
  (lambda (n d)
    (if (get shaping-top)
        (let ((m (names-find n (get (if d global-descs global-vals)))))
          (if (null? m) nil (extract (car m) 2)))
        nil)))

;;; ------------------------------------------------------------ expressions', types', modules'

;; The shape of expression node `at`, if it makes a module (or a function
;; that makes one) whose shape is known.
(define exp-shape (->* (fails int) shapes)
  (lambda (fail at)
    (case (array-ref (get exp-state) at)
      ((2) (array-ref (get exp-made) at))
      ((1) nil)
      (else
       (begin
         (array-set! (get exp-state) at 1)
         (let ((s (exp-found fail at)))
           (begin (array-set! (get exp-made) at s) (array-set! (get exp-state) at 2) s)))))))
(define ty-shape (->* (fails int) shapes)
  (lambda (fail at)
    (if (< at 0)
        nil
        (case (array-ref (get ty-state) at)
          ((2) (array-ref (get ty-made) at))
          ((1) nil)
          (else
           (begin
             (array-set! (get ty-state) at 1)
             (let ((s (ty-found fail at)))
               (begin (array-set! (get ty-made) at s) (array-set! (get ty-state) at 2) s))))))))
(define exp-found (->* (fails int) shapes)
  (lambda (fail at)
    (tagcase (node-kids at)
      (k-ref (n d free) (reference fail at n d))
      (k-binder (n d) (binder-shape fail at))
      (else y
        (let* ((s (node-syn at)) (items (proper-items s)) (h (head-of s)) (e (elems at))
               (k (len items)) (last (if (> k 1) (last-int e) -1))
               (at-e (lambda ((i int)) (int-at e i))))
          (cond
            ((= k 0) nil)
            ((string=? h "module") (module-shape fail (cdr e)))
            ;; A hidden global's definition, `(%loaded "key" "path")`, too
            ;; (`parse-loaded`).
            ((or (string=? h "load-module") (string=? h "load-input") (string=? h "%loaded"))
             (load-shape (syn-start-of-list s) #f))
            ((string=? h "the") (ty-shape fail (at-e 1)))
            ((string=? h "extend") (extended (exp-shape fail (at-e 1)) (exp-shape fail last)))
            ((and (string=? h "with") (= k 3) (syn-symbol? (nth items 1))
                  (string=? (syn-name (nth items 1)) "#%toplevel") (syn-symbol? (nth items 2)))
             (top-shape (syn-symbol (nth items 2)) #f))
            ((name-in-list? h (list "with" "let" "let*" "letrec" "begin" "letregion" "letfreeze"
                                    "letrena" "letreap" "plambda" "dlambda"))
             (if (>= last 0) (exp-shape fail last) nil))
            ((string=? h "proj") (exp-shape fail (at-e 1)))
            ((and (string=? h "if") (= k 4))
             (let ((a (exp-shape fail (at-e 2))) (b (exp-shape fail (at-e 3))))
               (if (and (not (null? a)) (shapes=? a b)) a nil)))
            ((or (string=? h "lambda") (string=? h "rlambda"))
             (let ((formals (at-e (if (string=? h "lambda") 1 2))))
               (sh-fun-of (if (>= formals 0) (formals-shapes fail formals) nil)
                          (if (>= last 0) (exp-shape fail last) nil))))
            ;; An application: its operator's result.
            (else (let ((op (operator at)))
                    (if (< op 0) nil (result-of (exp-shape fail op)))))))))))
(define name-in-list? (->* (string (listof string acyclic)) bool)
  (lambda (h hs) (and (not (null? hs)) (or (string=? h (car hs)) (name-in-list? h (cdr hs))))))
(define syn-start-of-list (->* (syn) int)
  (lambda (s) (tagcase s (lst (items d a b x) a) (dotted (items t d a b x) a) (else y -1))))
;; `extend`'s: the first's names, then the second's, the second's winning.
(define extended (->* (shapes shapes) shapes)
  (lambda (a b)
    (if (or (null? a) (null? b))
        nil
        (tagcase (car a)
          (sh-module (v0 d0)
            (tagcase (car b)
              (sh-module (v1 d1) (one (sh-module (members-onto v1 v0) (members-onto d1 d0))))
              (else y nil)))
          (else y nil)))))
;; The shapes of lambda formals `f`'s parameters: a typed one's type's, an
;; untyped one's as its binder has it.
(define formals-shapes (->* (fails int) (listof shapes acyclic))
  (lambda (fail f)
    (map-shapes fail (elems f))))
(define map-shapes (->* (fails (listof int acyclic)) (listof shapes acyclic))
  (lambda (fail ps)
    (if (null? ps)
        nil
        (cons (let ((p (car ps)))
                (if (< p 0)
                    nil
                    (tagcase (node-kids p)
                      (k-binder (n d) (binder-shape fail p))
                      (else y (ty-shape fail (elem p 1))))))
              (map-shapes fail (cdr ps))))))
;; The shape of the module whose items are the nodes `items`: the names each
;; exports, but a `module-parameters`'; without what a `hide` holds or
;; gives, though the module define it too.
;; Each item's members gathered onto `vs`, `ds` (and what a `hide` holds,
;; onto `hvs`, `hds`), the last first, so that gathering copies nothing;
;; at the end each name once, where its last definition puts it
;; (`members-latest`), as `with-member` one at a time would have it.
(define module-shape (->* (fails (listof int acyclic)) shapes)
  (lambda (fail items) (module-from fail items nil nil nil nil)))
(define module-from (->* (fails (listof int acyclic) members members members members) shapes)
  (lambda (fail items vs ds hvs hds)
    (if (null? items)
        (one (sh-module (members-hidden (members-latest vs (nm-leaf) nil)
                                        (names-onto hvs (nm-leaf)))
                        (members-hidden (members-latest ds (nm-leaf) nil)
                                        (names-onto hds (nm-leaf)))))
        (let* ((x (car items)) (h (if (< x 0) "" (head-of (node-syn x)))))
          (cond
            ((< x 0) nil)
            ((string=? h "module-parameters") (module-from fail (cdr items) vs ds hvs hds))
            (else
             (tagcase (node-kids x)
               (k-form (f)
                 (let ((ex (node-export f)))
                   (if (null? ex)
                       (module-from fail (cdr items) vs ds hvs hds)
                       (let ((got (levels-members fail (exported fail ex (node-syn x))
                                                  (tuple (the members nil) (the members nil) #t))))
                         (cond ((not (extract got 3)) nil)
                               ((string=? h "hide")
                                (module-from fail (cdr items) vs ds
                                             (append (extract got 1) hvs)
                                             (append (extract got 2) hds)))
                               (else
                                (module-from fail (cdr items) (append (extract got 1) vs)
                                             (append (extract got 2) ds) hvs hds)))))))
               (else y (module-from fail (cdr items) vs ds hvs hds)))))))))
;; What levels `ls` bind, as members, onto `got`, the last first (and a
;; name more than once: `module-from` keeps each one's last); its third,
;; whether every module among them has a shape.
(define levels-members
        (->* (fails levels (tupleof members members bool)) (tupleof members members bool))
  (lambda (fail ls got)
    (if (or (null? ls) (not (extract got 3)))
        got
        (levels-members fail (cdr ls)
          (tagcase (car ls)
            (lv-rib (as) (atms-members fail as got))
            (lv-earlier (as) (atms-members fail as got))
            (lv-shape (m)
              (let ((s (exp-shape fail m)))
                (if (null? s)
                    (tuple (extract got 1) (extract got 2) #f)
                    (tagcase (car s)
                      (sh-module (v d)
                        (tuple (members-reversed v (extract got 1))
                               (members-reversed d (extract got 2)) #t))
                      (else y (tuple (extract got 1) (extract got 2) #f))))))
            (lv-cage (c) (tuple (extract got 1) (extract got 2) #f)))))))
(define atms-members
        (->* (fails atms (tupleof members members bool)) (tupleof members members bool))
  (lambda (fail as got)
    (if (null? as)
        got
        (atms-members fail (cdr as)
          (tagcase (car as)
            (atm-lit (b d)
              (tagcase (node-kids b)
                (k-binder (n e)
                  (let ((s (binder-shape fail b)))
                    (if d
                        (tuple (extract got 1) (cons (tuple n s) (extract got 2)) #t)
                        (tuple (cons (tuple n s) (extract got 1)) (extract got 2) #t))))
                (else y got)))
            (else y got))))))
;; Whether two shapes are the same.
(define shapes=? (->* (shapes shapes) bool)
  (lambda (a b)
    (cond ((null? a) (null? b))
          ((null? b) #f)
          (else
           (tagcase (car a)
             (sh-module (v0 d0)
               (tagcase (car b) (sh-module (v1 d1) (and (members=? v0 v1) (members=? d0 d1)))
                        (else y #f)))
             (sh-fun (p0 r0)
               (tagcase (car b) (sh-fun (p1 r1) (and (shape-lists=? p0 p1) (shapes=? r0 r1)))
                        (else y #f))))))))
(define members=? (->* (members members) bool)
  (lambda (a b)
    (cond ((null? a) (null? b))
          ((null? b) #f)
          (else (and (symbol=? (extract (car a) 1) (extract (car b) 1))
                     (shapes=? (extract (car a) 2) (extract (car b) 2))
                     (members=? (cdr a) (cdr b)))))))
(define shape-lists=? (->* ((listof shapes acyclic) (listof shapes acyclic)) bool)
  (lambda (a b)
    (cond ((null? a) (null? b))
          ((null? b) #f)
          (else (and (shapes=? (car a) (car b)) (shape-lists=? (cdr a) (cdr b)))))))

;; The shape of type node `at`, if it describes a module (or a function
;; that makes one) whose shape is known.
(define ty-found (->* (fails int) shapes)
  (lambda (fail at)
    (tagcase (node-kids at)
      (k-ref (n d free) (if d (reference fail at n #t) nil))
      (else y
        (let* ((s (node-syn at)) (items (proper-items s)) (h (head-of s)) (e (elems at))
               (k (len items))
               (at-e (lambda ((i int)) (int-at e i))))
          (cond
            ;; A template's free description name, the top level's,
            ;; qualified.
            ((and (syn-symbol? s) (> (string-length (syn-name s)) 11)
                  (string=? (substring (syn-name s) 0 11) "#%toplevel:"))
             (let ((m (names-find (string->symbol (substring (syn-name s) 11
                                                             (string-length (syn-name s))))
                                  (get top-descs))))
               (if (null? m) nil (extract (car m) 2))))
            ((= k 0) nil)
            ((string=? h "moduleof") (moduleof-shape fail (cdr items) (cdr e) nil nil))
            ;; A shape written (`binding-shapes.md`): the names it gives.
            ((string=? h "modnames") (modnames-shape (cdr items)))
            ((or (string=? h "load-moduleof") (string=? h "load-input-moduleof"))
             (load-shape (syn-start-of-list s) #t))
            ((string=? h "restrict")
             (let ((m (ty-shape fail (at-e 1))) (kept (symbols-of (cdr (cdr items)))))
               (if (null? m)
                   nil
                   (tagcase (car m)
                     (sh-module (vs ds)
                       (one (sh-module (members-kept vs kept) (members-kept ds kept))))
                     (else y nil)))))
            ((string=? h "poly") (ty-shape fail (at-e (- k 1))))
            ;; A type a module gives: its own shape, if it is a module's.
            ((and (string=? h "select") (= k 3) (syn-symbol? (nth items 2)))
             (member-shape (exp-shape fail (at-e 1)) (syn-symbol (nth items 2)) #t))
            ((and (string=? h "->") (= k 3))
             (if (< (at-e 1) 0) nil
                 (sh-fun-of (param-types fail (at-e 1)) (ty-shape fail (at-e 2)))))
            ((string=? h "subr")
             (let* ((conv (and (> k 1) (string=? (head-of (nth items 1)) "conv")))
                    (j (if conv 4 3)))
               (if (< (at-e (- j 1)) 0)
                   nil
                   (sh-fun-of (param-types fail (at-e (- j 1))) (ty-shape fail (at-e j))))))
            ;; A description function applied: what it makes, whatever it
            ;; is given.
            ((and (>= (at-e 0) 0) (tagcase (node-kids (at-e 0)) (k-ref (n d free) d) (else y #f)))
             (ty-shape fail (at-e 0)))
            (else nil)))))))
;; The shape of `(modnames member …)`, its members `ms`: each value's name
;; (`x`, `(val x)`), a module's with its own shape (`(modnames m member
;; …)`), each description's (`(abs t)`, `(desc u)`, `(eff e)`).
(define modnames-shape (->* (syns-a) shapes)
  (lambda (ms) (modnames-from ms nil nil)))
(define modnames-from (->* (syns-a members members) shapes)
  (lambda (ms vs ds)
    (if (null? ms)
        (one (sh-module (reverse vs) (reverse ds)))
        (let* ((m (car ms)) (parts (proper-items m))
               (w (if (and (> (len parts) 1) (syn-symbol? (car parts))) (syn-name (car parts)) ""))
               (n (if (> (len parts) 1) (nth parts 1) m)))
          (cond ((syn-symbol? m)
                 (modnames-from (cdr ms) (cons (tuple (syn-symbol m) (the shapes nil)) vs) ds))
                ((not (syn-symbol? n)) nil)
                ((string=? w "val")
                 (modnames-from (cdr ms) (cons (tuple (syn-symbol n) (the shapes nil)) vs) ds))
                ((string=? w "modnames")
                 (modnames-from (cdr ms)
                                (cons (tuple (syn-symbol n) (modnames-shape (cdr (cdr parts)))) vs)
                                ds))
                ((or (string=? w "abs") (string=? w "desc") (string=? w "eff"))
                 (modnames-from (cdr ms) vs (cons (tuple (syn-symbol n) (the shapes nil)) ds)))
                (else nil))))))
;; The shapes of a procedure type's parameters, node `ps` their list, each
;; a type or a dependent `(c : T)`.
(define param-types (->* (fails int) (listof shapes acyclic))
  (lambda (fail ps) (param-types-of fail (elems ps))))
(define param-types-of (->* (fails (listof int acyclic)) (listof shapes acyclic))
  (lambda (fail ps)
    (if (null? ps)
        nil
        (cons (let ((p (car ps)))
                (cond ((< p 0) nil)
                      ((dependent? (node-syn p)) (ty-shape fail (elem p 2)))
                      (else (ty-shape fail p))))
              (param-types-of fail (cdr ps))))))
(define symbols-of (->* ((listof syn acyclic)) (listof symbol acyclic))
  (lambda (xs)
    (cond ((null? xs) nil)
          ((syn-symbol? (car xs)) (cons (syn-symbol (car xs)) (symbols-of (cdr xs))))
          (else (symbols-of (cdr xs))))))
(define all-symbols? (->* ((listof syn acyclic)) bool)
  (lambda (xs) (or (null? xs) (and (syn-symbol? (car xs)) (all-symbols? (cdr xs))))))
(define members-kept (->* (members (listof symbol acyclic)) members)
  (lambda (ms kept)
    (cond ((null? ms) nil)
          ((symbol-in? (extract (car ms) 1) kept) (cons (car ms) (members-kept (cdr ms) kept)))
          (else (members-kept (cdr ms) kept)))))
(define symbol-in? (->* (symbol (listof symbol acyclic)) bool)
  (lambda (n xs) (and (not (null? xs)) (or (symbol=? n (car xs)) (symbol-in? n (cdr xs))))))
;; A `moduleof`'s shape, from its members `ms` (their nodes `es`): each
;; `val`'s and `desc`'s by its type, an `abs`'s not known.
(define moduleof-shape
  (->* (fails (listof syn acyclic) (listof int acyclic) members members) shapes)
  (lambda (fail ms es vs ds)
    (if (null? ms)
        (one (sh-module (reverse vs) (reverse ds)))
        (let* ((parts (proper-items (car ms))) (x (if (null? es) -1 (car es)))
               (word (if (and (not (null? parts)) (syn-symbol? (car parts))) (syn-name (car parts))
                         ""))
               (second (if (> (len parts) 1) (nth parts 1) (car ms)))
               (names (cond ((syn-symbol? second) (list (syn-symbol second)))
                            ((null? (proper-items second)) nil)
                            ((string=? word "abs")
                             (if (all-symbols? (proper-items second))
                                 (symbols-of (proper-items second))
                                 (symbols-of (list (car (proper-items second))))))
                            (else (symbols-of (list (car (proper-items second)))))))
               (t (lambda ()
                          (if (< x 0) nil
                              (let ((y (elem x 2))) (if (< y 0) nil (ty-shape fail y)))))))
          (cond
            ((or (< (len parts) 2) (and (null? names) (not (string=? word "abs")))) nil)
            ((string=? word "val")
             (moduleof-shape fail (cdr ms) (if (null? es) nil (cdr es))
                             (cons (tuple (car names) (t)) vs) ds))
            ((string=? word "abs")
             (moduleof-shape fail (cdr ms) (if (null? es) nil (cdr es)) vs (abs-onto names ds)))
            ((string=? word "desc")
             (moduleof-shape fail (cdr ms) (if (null? es) nil (cdr es)) vs
                             (cons (tuple (car names) (t)) ds)))
            (else nil))))))
(define abs-onto (->* ((listof symbol acyclic) members) members)
  (lambda (ns ds)
          (if (null? ns) ds (abs-onto (cdr ns) (cons (tuple (car ns) (the shapes nil)) ds)))))
;; What exports `ex` bind: levels, innermost first.
(define exported (->* (fails rooted syn) levels)
  (lambda (fail ex s)
    (if (null? ex)
        nil
        (append (evaluate fail (extract (car ex) 1) (extract (car ex) 2) s)
                (exported fail (cdr ex) s)))))
