;;; Binding shapes written, in FX-26 (`docs/research/binding-shapes.md`,
;;; step 2; `macros/shapes.rs`'s `Macros::shaped`): each form that opens a
;;; module, with what the module was relied on for, as `macros-shaper.fx`
;;; finds it; each loaded file's shape found first. Part of the expander:
;;; loaded by `parser-top.fx`, and loading `macros-shaper.fx`.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define shaper-module ((proj (load-module "fx26:macros-shaper.fx") rs re rm rc rp)))
(define walk-module (with shaper-module walk-module))
(define scopes-module (with walk-module scopes-module))
(define align-module (with scopes-module align-module))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted (type syn))
(import parser-module parse-tag p-ok p-err syn-symbol? syn-symbol syn-name mk-symbol mk-list len nth
        syn-string? syn-string syn-datums (type syns-a presult loaded-file loaded-files))
(import types-module proper-items fail-at name-in? (type fails addr atms))
(import align-module node-export node-imports node-syn node-kids node-path nnodes program-walk
        lv-rib lv-shape
        k-binder k-ref k-form atm-lit lv-earlier def-env-top
        env-any-shape? env-lookup binder-name
        (type levels found def-env def-envs env))
(import walk-module walked pfail-walk walked-out show-renamed falses addr=?)
(import shaper-module asked-of binder-shape elem exp-shape exported file-given-at file-key
        file-shape-keyed file-shapes files-given form-node? head-of head-is? head-sym no-head
        inputs-at input-key?
        load-input-at? members-onto member-shape
        name-in-list? resolve result-of sh-fun sh-fun-of sh-module shaper-begin! shapes-reset!
        shaping-top top-descs top-vals names-with names-onto names-empty? nm-leaf
        globals-given! binder-named
        (type asked file-shape shapes members name-tree))

;;; ------------------------------------------------------------ a form's shapes written

;; Form `form`, a program's after expansion (a top-level form if `top`; or,
;; a file's items, a `module` of them): each `with`, `extend` and `include`
;; in it with what its module was relied on for written in, `#:relied
;; ((value …) (description …))`, the names asked of it that it gives, or
;; `#:relied #f` where its shape was not known where asked
;; (`binding-shapes.md`, step 2; `Macros::shaped`); and, at the top level,
;; what its definitions bind kept for the forms after it. Its own shape, as
;; an expression's, in the second.
(define shaped (->* (fails syn bool) (tupleof syn shapes))
  (lambda (fail form top)
    (let* ((w (walked fail form top)) (root (extract w 1)) (found (extract w 2)))
      (begin
        (set shaping-top top)
        (shaper-begin! root found)
        (asked-all fail found)
        (let ((written (writings 0 (get nnodes) nil)))
          (if top
              (begin (defined-kept fail root form) (tuple (with-written form written) nil))
              (tuple (with-written form written) (exp-shape fail root))))))))
;; Every reference that reaches a module's names asks the module.
(define asked-all (->* (fails found) unit)
  (lambda (fail fs)
    (if (null? fs)
        #u
        (begin
          (let ((at (extract (car fs) 1)))
            (tagcase (node-kids at)
              (k-ref (n d free)
                (if (env-any-shape? (extract (car fs) 2)) (begin (resolve fail at n d) #u) #u))
              (else y #u)))
          (asked-all fail (cdr fs))))))
;; What to write into each form that opens a module, by its path: what its
;; module was asked, or none (`#f`) where its shape was not known.
(define-type writing (tupleof addr (listof syn acyclic)))
(define writings (->* (int int (listof writing acyclic)) (listof writing acyclic))
  (lambda (k n out)
    (if (= k n)
        out
        (writings (+ k 1) n
          (let ((s (node-syn k)))
            (if (and (form-node? k) (opens? s) (null? (writing-at (node-path k) out))
                     (not (toplevel-or-fx? s)) (>= (elem k 1) 0))
                (let ((a (asked-of (elem k 1))))
                  (cons (tuple (node-path k) (if (extract a 2) nil (list (asked-written a s))))
                        out))
                out))))))
(define opens? (->* (syn) bool)
  (lambda (s)
    (or (head-is? s 'with) (head-is? s 'extend) (head-is? s 'include)
        (head-is? s 'import-with-syntax))))
(define toplevel-or-fx? (->* (syn) bool)
  (lambda (s)
    (let ((items (proper-items s)))
      (and (> (len items) 1) (syn-symbol? (nth items 1))
           (or (string=? (syn-name (nth items 1)) "#%fx")
               (string=? (syn-name (nth items 1)) "#%toplevel"))))))
(define writing-at (->* (addr (listof writing acyclic)) (listof writing acyclic))
  (lambda (p ws)
    (cond ((null? ws) nil)
          ((addr=? p (extract (car ws) 1)) (list (car ws)))
          (else (writing-at p (cdr ws))))))
(define asked-written (->* (asked syn) syn)
  (lambda (a s)
    (let ((ab (syn-span s)))
      (mk-list (list (mk-list (given-names (extract a 1) #f (extract ab 1) (extract ab 2))
                              (extract ab 1) (extract ab 2))
                     (mk-list (given-names (extract a 1) #t (extract ab 1) (extract ab 2))
                              (extract ab 1) (extract ab 2)))
               (extract ab 1) (extract ab 2)))))
(define given-names (->* ((listof (tupleof symbol bool bool) acyclic) bool int int) syns-a)
  (lambda (xs d a b)
    (cond ((null? xs) nil)
          ((and (eq? d (extract (car xs) 2)) (extract (car xs) 3))
           (cons (mk-symbol (symbol->string (extract (car xs) 1)) a b)
                 (given-names (cdr xs) d a b)))
          (else (given-names (cdr xs) d a b)))))
(define syn-span (->* (syn) (tupleof int int))
  (lambda (s)
    (tagcase s
      (lst (items d a b x) (tuple a b))
      (dotted (items t d a b x) (tuple a b))
      (atom (d a b x) (tuple a b))
      (else y (tuple 0 0)))))
;; `s` with each of `ws` written into the form at its path, after its
;; first operand.
(define with-written (->* (syn (listof writing acyclic)) syn)
  (lambda (s ws) (written-under s (writings-from-top ws))))
;; `ws`, each its path outermost step first: what is left of it below a
;; node, as a walk down from the top takes its steps (`written-under`).
(define writings-from-top (->* ((listof writing acyclic)) (listof writing acyclic))
  (lambda (ws)
    (if (null? ws)
        nil
        (cons (tuple (the addr (reverse (extract (car ws) 1))) (extract (car ws) 2))
              (writings-from-top (cdr ws))))))
;; `s` with each of `ws`, under it by the steps left of each, written:
;; itself where none is. Each step of each path taken once, at its list
;; (`written-items`), so that a long list costs no more than its length.
(define written-under (->* (syn (listof writing acyclic)) syn)
  (lambda (s ws)
    (if (null? ws)
        s
        (tagcase s
          (lst (items d a b x)
            (let ((items2 (written-items items ws (written-here s ws) 0 a b)))
              (lst items2 (syn-datums items2) a b x)))
          (dotted (items tail d a b x)
            (let ((items2 (written-items items ws (written-here s ws) 0 a b)))
              (dotted items2 (written-under tail (steps-taken ws (len items))) (syn-datums items2)
                      a b x)))
          (else y s)))))
;; Those of `ws` whose next step is `step`, past it.
(define step-taken (->* ((listof writing acyclic) bool) (listof writing acyclic))
  (lambda (ws step)
    (cond ((null? ws) nil)
          ((let ((p (extract (car ws) 1))) (and (not (null? p)) (eq? (car p) step)))
           (cons (tuple (cdr (extract (car ws) 1)) (extract (car ws) 2))
                 (step-taken (cdr ws) step)))
          (else (step-taken (cdr ws) step)))))
;; Those of `ws` past `k` cdrs: a dotted list's tail's.
(define steps-taken (->* ((listof writing acyclic) int) (listof writing acyclic))
  (lambda (ws k) (if (= k 0) ws (steps-taken (step-taken ws #f) (- k 1)))))
;; What to write into list `s`, in a list of one, if it is a form that
;; opens a module and one of `ws` is at it, no step left.
(define written-here (->* (syn (listof writing acyclic)) (listof (listof syn acyclic) acyclic))
  (lambda (s ws)
    (if (opens? s)
        (let ((w (writing-at nil ws))) (if (null? w) nil (list (extract (car w) 2))))
        nil)))
;; List items `items`, from the `k`th, each with those of `ws` under it
;; written (its first step `#t`, after `k` cdrs taken), the record `here`
;; after the first operand.
(define written-items
  (->* (syns-a (listof writing acyclic) (listof (listof syn acyclic) acyclic) int int int)
       syns-a)
  (lambda (items ws here k a b)
    (let ((record (if (null? here)
                      (the syns-a nil)
                      (list (atom (symbol->keyword 'relied) a b 0)
                            (if (null? (car here)) (mk-symbol "#f" a b) (car (car here)))))))
      (cond ((null? items) (if (= k 2) record nil))
            ((and (= k 2) (not (null? here)))
             (append record (written-items items ws nil k a b)))
            (else (cons (written-under (car items) (step-taken ws #t))
                        (written-items (cdr items) (step-taken ws #f) here (+ k 1) a b)))))))
;; What the top level's definitions in `form` bind, kept for the forms
;; after it.
(define defined-kept (->* (fails int syn) unit)
  (lambda (fail root form)
    (tagcase (node-kids root)
      (k-form (x)
        (let ((ex (node-export x)))
          (if (null? ex) #u (defined-onto fail (exported fail ex form)))))
      (else y #u))))
(define defined-onto (->* (fails levels) unit)
  (lambda (fail ls)
    (if (null? ls)
        #u
        (begin
          (tagcase (car ls)
            (lv-rib (as) (defined-atoms fail as))
            (lv-shape (m)
              (let ((s (exp-shape fail m)))
                (if (null? s)
                    #u
                    (tagcase (car s)
                      (sh-module (vs ds) (begin (set top-vals (names-onto vs (get top-vals)))
                                                (set top-descs (names-onto ds (get top-descs)))))
                      (else y #u)))))
            (else y #u))
          (defined-onto fail (cdr ls))))))
(define defined-atoms (->* (fails atms) unit)
  (lambda (fail as)
    (if (null? as)
        #u
        (begin
          (tagcase (car as)
            (atm-lit (b d)
              (tagcase (node-kids b)
                (k-binder (n e)
                  (let ((s (binder-shape fail b)))
                    (if d (set top-descs (names-with (get top-descs) n s))
                        (set top-vals (names-with (get top-vals) n s)))))
                (else y #u)))
            (else y #u))
          (defined-atoms fail (cdr as))))))

;; Each of `forms`, a program's top-level forms after expansion, with what
;; each module it opens was relied on for written in (`shaped`), written:
;; for `tests/scopes.rs`, which holds the two expanders' records to one
;; another; the files read for its loads `fs`.
(define shaped-forms (->* (syns-a loaded-files) (listof string acyclic))
  (lambda (forms fs) (begin (shapes-reset! fs) (shaped-each forms))))
(define shaped-each (->* (syns-a) (listof string acyclic))
  (lambda (forms)
    (if (null? forms)
        nil
        (cons (show-renamed (top-shaped (car forms))) (shaped-each (cdr forms))))))

;;; ------------------------------------------------------------ files' shapes

;; Each file a load in `s` reads, its shape found and kept, those it loads
;; first (`Checker::file_shapes_for`): as its forms are given, before
;; expansion, as the Rust checker reads them.
(define files-shaped! (->* (syn) unit)
  (lambda (s) (loads-shaped! (loads-in s nil))))
(define loads-shaped! (->* ((listof (tupleof int bool) acyclic)) unit)
  (lambda (ls)
    (if (null? ls)
        #u
        (begin
          (let ((f (file-given-at (extract (car ls) 1) (get files-given))))
            (if (null? f) #u (file-shaped! (car f) (extract (car ls) 2))))
          (loads-shaped! (cdr ls))))))
;; Each load in `s`, where it starts and whether it is an input's, onto
;; `out`.
(define loads-in (->* (syn (listof (tupleof int bool) acyclic)) (listof (tupleof int bool) acyclic))
  (lambda (s out)
    (tagcase s
      (lst (items d a b x)
        (let* ((h (head-sym s))
               ;; A hidden global's definition, `(%loaded "key" "path")`
               ;; (`parse-loaded`), an input's if its key says so.
               (hoisted (and (symbol=? h '%loaded) (> (len items) 1) (syn-string? (nth items 1))))
               (input (or (symbol=? h 'load-input) (symbol=? h 'load-input-moduleof)
                          (and hoisted (input-key? (syn-string (nth items 1))))))
               (load (or hoisted
                         (and (or input (symbol=? h 'load-module) (symbol=? h 'load-moduleof))
                              (> (len items) 1) (syn-string? (nth items 1)))))
               (out2 (if load
                         (begin (if input (set inputs-at (cons a (get inputs-at))) #u)
                                (append out (list (tuple a input))))
                         out)))
          (loads-in-each items out2)))
      (dotted (items t d a b x) (loads-in t (loads-in-each items out)))
      (else y out))))
(define loads-in-each
        (->* (syns-a (listof (tupleof int bool) acyclic)) (listof (tupleof int bool) acyclic))
  (lambda (xs out) (if (null? xs) out (loads-in-each (cdr xs) (loads-in (car xs) out)))))
;; File `f`'s shape, loaded as an input's if `input?`, found and kept, if
;; it was not: none while it is found, so that a cycle finds none; none if
;; it was not read, or is read from its `.fasl`, or does not walk.
(define file-shaped! (->* (loaded-file bool) unit)
  (lambda (f input?)
    (let ((key (file-key f input?)))
      (if (not (null? (file-shape-keyed key (get file-shapes))))
          #u
          (begin
            (set file-shapes (cons (tuple key (the shapes nil) (the shapes nil) (extract f 5))
                                   (get file-shapes)))
            (cond ((<= (extract f 2) 0) #u)
                  ((extract f 8) (fasl-kept! key (extract f 5) input?))
                  (else
                   (begin
                     (loads-shaped! (loads-in-each (extract f 5) nil))
                     (file-kept! key (extract f 5) input?)))))))))
;; A file read from its `.fasl`, its forms the one expression the Rust
;; checker read it as (`(the T %fasl-value)`; a file of parameters', a
;; function of them; an input's, a module of the item `input`): its shape
;; that expression's (an input's, its `input`'s); its module's, what a
;; function makes.
(define fasl-kept! (->* (string syns-a bool) unit)
  (lambda (key forms input?)
    (if (or (null? forms) (not (null? (cdr forms))))
        #u
        (let* ((form (unshaped (car forms)))
               (r (prompt parse-tag
                          (begin (set file-out (shaped pfail-walk form #f)) (p-ok nil))
                          (lambda ((r presult)) r)))
               (ok (begin (set program-walk #f) (tagcase r (p-err (why a b) #f) (else y #t))))
               (whole (if ok (extract (get file-out) 2) nil))
               (m (if input? (member-shape whole 'input #f) whole))
               (fun (and (not (null? m)) (tagcase (car m) (sh-fun (ps r) #t) (else y #f)))))
          (set file-shapes
               (file-shape-replaced key (tuple key m (if fun (result-of m) m) forms)
                                    (get file-shapes)))))))
(define file-kept! (->* (string syns-a bool) unit)
  (lambda (key forms0 input?)
   (let ((forms (sealed-items (unshaped-items forms0))))
    (let* ((params (and (not (null? forms)) (string=? (head-of (car forms)) "module-parameters")))
           (wrapped (not (and input? (not params))))
           (form (cond ((null? forms) nil)
                       (wrapped
                        (let* ((ab (syn-span (car forms))) (a (extract ab 1)) (b (extract ab 2)))
                          (list (mk-list (cons (mk-symbol "module" a b) forms) a b))))
                       ((null? (cdr forms)) (list (car forms)))
                       (else nil))))
      (if (null? form)
          #u
          (let* ((r (prompt parse-tag
                            (begin (set file-out (shaped pfail-walk (car form) #f)) (p-ok nil))
                            (lambda ((r presult)) r)))
                 (ok (begin (set program-walk #f) (tagcase r (p-err (why a b) #f) (else y #t))))
                 (m (if ok (extract (get file-out) 2) nil))
                 (written (if ok (extract (get file-out) 1) (car form)))
                 (vm (cond (params (tuple (sh-fun-of nil m) m))
                           ((and input? (not (null? m))
                                 (tagcase (car m) (sh-fun (ps r) #t) (else y #f)))
                            (tuple m (result-of m)))
                           (else (tuple m m)))))
            (set file-shapes
                 (file-shape-replaced key (tuple key (extract vm 1) (extract vm 2)
                                                 (if wrapped (cdr (proper-items written))
                                                     (list written)))
                                      (get file-shapes)))))))))
(define file-out (ref (tupleof syn shapes) rs) (new (tuple (mk-symbol "-" 0 0) (the shapes nil))))
(define file-shape-replaced
  (->* (string file-shape (listof file-shape acyclic)) (listof file-shape acyclic))
  (lambda (key x fs)
    (cond ((null? fs) nil)
          ((string=? key (extract (car fs) 1)) (cons x (cdr fs)))
          (else (cons (car fs) (file-shape-replaced key x (cdr fs)))))))
;; File `f`'s forms, loaded as an input's if `input?`, with what each
;; module they open was relied on for written in: its shape found first, if
;; it was not.
(define file-forms-written (->* (loaded-file bool) syns-a)
  (lambda (f input?)
    (begin
      (file-shaped! f input?)
      (let ((s (file-shape-keyed (file-key f input?) (get file-shapes))))
        (if (null? s) (extract f 5) (extract (car s) 4))))))
;; Top-level form `x`, after expansion, with what each module it opens was
;; relied on for written in, the files it loads shaped first; as it is if
;; it does not walk, for the checkers to say why.
(define top-shaped (->* (syn) syn)
  (lambda (x0)
    (let ((x (unshaped x0)))
     (begin
      (files-shaped! x)
      (let ((r (prompt parse-tag
                       (begin (set file-out (shaped pfail-walk x #t)) (p-ok nil))
                       (lambda ((r presult)) r))))
        (begin
          (set program-walk #f)
          (tagcase r (p-err (why a b) x) (else y (extract (get file-out) 1)))))))))
;; `s` without what was written into it of the modules it opens (`#:relied
;; …`), as it was expanded: what a walk reads, whatever a program wrote
;; (`macros/shapes.rs`'s `unshaped`). Itself if nothing was.
(define unshaped (->* (syn) syn)
  (lambda (s) (if (relied-in? s) (unshaped-in s) s)))
(define relied-in? (->* (syn) bool)
  (lambda (s)
    (tagcase s
      (lst (items d a b x) (or (relied-at-2? items) (any-relied? items)))
      (dotted (items t d a b x) (or (relied-at-2? items) (any-relied? items) (relied-in? t)))
      (else y #f))))
(define any-relied? (->* (syns-a) bool)
  (lambda (xs) (and (not (null? xs)) (or (relied-in? (car xs)) (any-relied? (cdr xs))))))
(define relied-at-2? (->* (syns-a) bool)
  (lambda (xs)
    (and (> (len xs) 2)
         (tagcase (nth xs 2)
           (atom (d a b x) (and (keyword? d) (symbol=? (keyword->symbol d) 'relied)))
           (else y #f)))))
(define unshaped-in (->* (syn) syn)
  (lambda (s)
    (tagcase s
      (lst (items d a b x)
        (let ((xs (unshaped-items (if (relied-at-2? items) (cut-record items) items))))
          (lst xs (syn-datums xs) a b x)))
      (dotted (items t d a b x)
        (let ((xs (unshaped-items (if (relied-at-2? items) (cut-record items) items))))
          (dotted xs (unshaped t) (syn-datums xs) a b x)))
      (else y s))))
(define unshaped-items (->* (syns-a) syns-a)
  (lambda (xs) (if (null? xs) nil (cons (unshaped (car xs)) (unshaped-items (cdr xs))))))
;; `xs` without its third and fourth, a record's keyword and what follows.
(define cut-record (->* (syns-a) syns-a)
  (lambda (xs)
    (cons (car xs) (cons (nth xs 1) (if (> (len xs) 3) (cdr (cdr (cdr (cdr xs)))) nil)))))
;; Files `fs` (`parser-loads.fx`'s), each with its forms as its shape wrote
;; them, where it was shaped: what the parser reads of a load.
(define forms-written-in (->* (loaded-files) loaded-files)
  (lambda (fs)
    (if (null? fs)
        nil
        (cons (let* ((f (car fs))
                     (s (file-shape-keyed (file-key f (load-input-at? (extract f 1)))
                                          (get file-shapes))))
                (if (null? s)
                    f
                    (product (1 (extract f 1)) (2 (extract f 2)) (3 (extract f 3)) (4 (extract f 4))
                             (5 (extract (car s) 4)) (6 (extract f 6)) (7 (extract f 7))
                             (8 (extract f 8)))))
              (forms-written-in (cdr fs))))))
;; The top level's shapes by the reading state each form left, as the
;; expander keeps its macros (`macros-at!`, `macros-after!`); and the shapes
;; named (`named-shapes`).
(define-type named (listof (tupleof symbol syn) acyclic))
(define-type shapes-state (tupleof int name-tree name-tree named))
(define shapes-by-state (ref (listof shapes-state acyclic) rs) (new nil))
;; The top level's shapes as reading state `s` left them; the files read
;; for the forms to come, `fs`, none shaped yet: their forms are this
;; reading's, at its places, as the parser reads each file again.
(define shapes-at! (->* (int loaded-files) unit)
  (lambda (s fs)
    (let ((at (state-shapes s (get shapes-by-state))))
      (begin
        (set files-given fs)
        (set file-shapes nil)
        (set inputs-at nil)
        (if (null? at)
            (begin (set top-vals (nm-leaf)) (set top-descs (nm-leaf)) (set named-shapes nil))
            (begin (set top-vals (extract (car at) 2)) (set top-descs (extract (car at) 3))
                   (set named-shapes (extract (car at) 4))))))))
(define state-shapes (->* (int (listof shapes-state acyclic)) (listof shapes-state acyclic))
  (lambda (s xs)
    (cond ((null? xs) nil)
          ((= s (extract (car xs) 1)) (list (car xs)))
          (else (state-shapes s (cdr xs))))))
(define shapes-after! (->* (int) unit)
  (lambda (s)
    (if (and (names-empty? (get top-vals)) (names-empty? (get top-descs))
             (null? (get named-shapes)))
        #u
        (set shapes-by-state
             (cons (tuple s (get top-vals) (get top-descs) (get named-shapes))
                   (get shapes-by-state))))))
;; The shapes named by `define-syntax` (`(define-syntax s (modnames …))`,
;; `binding-shapes.md`), each its `modnames` form, by its name.
(define named-shapes (ref named rs) (new nil))
;; Whether `x` is `(define-syntax s (modnames …))`.
(define shape-definition? (->* (syn) bool)
  (lambda (x)
    (let ((items (proper-items x)))
      (and (= (len items) 3) (string=? (head-of x) "define-syntax") (syn-symbol? (nth items 1))
           (string=? (head-of (nth items 2)) "modnames")))))
;; `(define-syntax s (modnames …))`, `x`: the shape kept, by its name.
(define shape-defined! (->* (syn) unit)
  (lambda (x)
    (let ((items (proper-items x)))
      (set named-shapes (cons (tuple (syn-symbol (nth items 1)) (nth items 2))
                              (named-without (syn-symbol (nth items 1)) (get named-shapes)))))))
(define named-without (->* (symbol named) named)
  (lambda (n ns)
    (cond ((null? ns) nil)
          ((symbol=? n (extract (car ns) 1)) (named-without n (cdr ns)))
          (else (cons (car ns) (named-without n (cdr ns)))))))
(define shape-named (->* (symbol) (listof syn acyclic))
  (lambda (n) (named-shape-in n (get named-shapes))))
(define named-shape-in (->* (symbol named) (listof syn acyclic))
  (lambda (n ns)
    (cond ((null? ns) nil)
          ((symbol=? n (extract (car ns) 1)) (list (extract (car ns) 2)))
          (else (named-shape-in n (cdr ns))))))
;; Form `s` with each shape a name stands for written where a value supplies
;; its types, a `define`'s or `the`'s type, and each such `define` made
;; `(define x (the (modnames …) e))`, which the checkers seal there; outside
;; quotes. A shape used as a form's head, refused. As
;; `Macros::sealed_written`. Itself where nothing in it is written.
(define sealed-written (->* (fails syn) syn)
  (lambda (fail s)
    (tagcase s
      (lst (items d a b x)
        (let ((h (head-sym s)))
          (cond
            ((or (symbol=? h 'quote) (symbol=? h 'quasiquote) (symbol=? h '%datum)) s)
            ((and (not (symbol=? h no-head)) (not (null? (shape-named h))))
             (begin (fail (string-append "`" (symbol->string h) "` is a shape, not a macro: it is "
                                         "written as a `define`'s or `the`'s type")
                          a b)
                    s))
            (else
             (let* ((xs (sealed-each fail items))
                    (n (len xs))
                    (ys (cond ((and (symbol=? h 'define) (= n 4)
                                    (not (null? (shape-of (nth xs 2)))))
                               (list (car xs) (nth xs 1)
                                     (mk-list (list (mk-symbol "the" a b)
                                                    (car (shape-of (nth xs 2))) (nth xs 3))
                                              a b)))
                              ((and (symbol=? h 'the) (= n 3) (not (null? (shape-of (nth xs 1)))))
                               (list (car xs) (car (shape-of (nth xs 1))) (nth xs 2)))
                              (else xs))))
               (if (same-items? ys items) s (lst ys (syn-datums ys) a b x)))))))
      (dotted (items t d a b x)
        (let ((xs (sealed-each fail items)) (t2 (sealed-written fail t)))
          (if (and (same-items? xs items) (eq? t2 t)) s (dotted xs t2 (syn-datums xs) a b x))))
      (else y s))))
(define sealed-each (->* (fails syns-a) syns-a)
  (lambda (fail xs)
    (if (null? xs) nil (cons (sealed-written fail (car xs)) (sealed-each fail (cdr xs))))))
;; Whether `xs` are `ys`, each the same object.
(define same-items? (->* (syns-a syns-a) bool)
  (lambda (xs ys)
    (cond ((null? xs) (null? ys))
          ((null? ys) #f)
          (else (and (eq? (car xs) (car ys)) (same-items? (cdr xs) (cdr ys)))))))
;; The `modnames` form type `t` is: itself, or the shape its name names; in
;; a list of one, none if neither.
(define shape-of (->* (syn) (listof syn acyclic))
  (lambda (t)
    (cond ((syn-symbol? t) (shape-named (syn-symbol t)))
          ((string=? (head-of t) "modnames") (list t))
          (else nil))))
;; File forms `xs`, sealed (`sealed-written`); as they are if that fails.
(define sealed-items (->* (syns-a) syns-a)
  (lambda (xs)
    (let ((r (prompt parse-tag (begin (set sealed-out (sealed-each pfail-walk xs)) (p-ok nil))
                     (lambda ((r presult)) r))))
      (tagcase r (p-err (why a b) xs) (else y (get sealed-out))))))
(define sealed-out (ref syns-a rs) (new nil))
;; How many files have been shaped (or are being).
(define files-shaped (->* () int)
  (lambda () (shapes-count (get file-shapes) 0)))
(define shapes-count (->* ((listof file-shape acyclic) int) int)
  (lambda (fs n) (if (null? fs) n (shapes-count (cdr fs) (+ n 1)))))
;; Hidden global `n`, `%shared:key`, defined as its file's module: its
;; shape the file's, for the forms after (as the Rust checker finds it from
;; its type), whose own parses forget the files'.
(define shared-shaped! (->* (symbol) unit)
  (lambda (n)
    (let* ((name (symbol->string n))
           (f (if (> (string-length name) 8)
                  (file-shape-keyed (substring name 8 (string-length name)) (get file-shapes))
                  nil)))
      (if (null? f) #u (set top-vals (names-with (get top-vals) n (extract (car f) 2)))))))

;;; ------------------------------------------------------------ aliases resolved

;; Hygiene, one mechanism (`binding-shapes.md`, step 3; `macros/hygiene.rs`):
;; top-level form `x`, after expansion, each alias an expansion left free,
;; `%~N:x`, made the name it stands for where its macro is defined
;; (`def-env-of`): a top-level macro's the top level's, written so (`(with
;; #%toplevel x)`, `#%toplevel:x`); a file's macro's the file's value,
;; `(with %shared:key x)`, else the standard one, `(with #%fx x)`; a module
;; file's own macro's the plain name, a binder at the use that would capture
;; it renamed, `%x~N`, and each reference to that binder; an alias the
;; expansion bound, here or at the top level before, a name of its own.
;; Itself if it has no alias. No alias reaches the checker.
(define aliases-resolved (->* (fails syn def-envs) syn)
  (lambda (fail x hs)
    (if (not (alias-in? x))
        x
        (let* ((w (walked fail x #t)) (root (extract w 1)) (found (extract w 2))
               (made (aliases-written fail found hs (root-binders fail root x)
                                      (tuple (the parts nil) (the ints nil))))
               (fresh (captors-named (extract made 2) nil))
               (written (append (captors-renamed found fresh (binders-renamed fresh nil))
                                (extract made 1))))
          (begin (aliases-defined-in fail root x)
                 (with-parts x nil written))))))
(define-type ints (listof int acyclic))
;; Whether `s` holds an alias, outside quotes.
(define alias-in? (->* (syn) bool)
  (lambda (s)
    (tagcase s
      (atom (d a b x) (and (syn-symbol? s) (not (string=? (alias-base (syn-name s)) ""))))
      (lst (items d a b x)
        (let ((h (head-sym s)))
          (and (not (or (symbol=? h 'quote) (symbol=? h 'quasiquote) (symbol=? h '%datum)))
               (aliases-in? items))))
      (dotted (items t d a b x) (or (aliases-in? items) (alias-in? t)))
      (else y #f))))
(define aliases-in? (->* (syns-a) bool)
  (lambda (xs) (and (not (null? xs)) (or (alias-in? (car xs)) (aliases-in? (cdr xs))))))
;; Each free alias `found` reaches, by its node's path, what it is written
;; as, onto `out`'s; and onto its binders, each binder at a use that would
;; capture a name a module file's own macro introduces (none of `top`, the
;; form's own definitions, which are the file's items).
(define-type parts (listof (tupleof addr syn) acyclic))
(define-type written-of (tupleof parts ints))
(define aliases-written (->* (fails found def-envs ints written-of) written-of)
  (lambda (fail fs hs top out)
    (if (null? fs)
        out
        (aliases-written
          fail (cdr fs) hs top
          (let ((at (extract (car fs) 1)) (env (extract (car fs) 2)))
            (tagcase (node-kids at)
              (k-ref (n d free)
                (let* ((base (alias-base (symbol->string n)))
                       (h (def-env-of (alias-made (symbol->string n)) hs))
                       (within (= (extract h 1) 2)))
                  (if (or (string=? base "") (bound-in? n d env)
                          (and (not within) (alias-defined? n d)))
                      out
                      (let ((parts (cons (tuple (node-path at)
                                                (alias-written fail base d free h (node-syn at)))
                                         (extract out 1))))
                        (if within
                            (tuple parts (captor-noted fail (captor-of (string->symbol base) d env)
                                                       top base (node-syn at) (extract out 2)))
                            (tuple parts (extract out 2)))))))
              (else y out)))))))
;; Binder `c` (`captor-of`'s) onto `cs`, if it captures `base`, which a
;; module file's own macro introduces at `s`: not if it is none, or one of
;; `top`; refused where a module's names come first, which may give it.
(define captor-noted (->* (fails int ints string syn ints) ints)
  (lambda (fail c top base s cs)
    (cond ((= c -1) cs)
          ((= c -2)
           (begin (fail-at fail (string-append "`" base "`, which a macro of this file names, "
                                               "where a `with` or `include` around its use may "
                                               "give it: not yet")
                           s)
                  cs))
          ((or (int-in? c top) (int-in? c cs)) cs)
          (else (cons c cs)))))
(define int-in? (->* (int ints) bool)
  (lambda (k ks) (and (not (null? ks)) (or (= k (car ks)) (int-in? k (cdr ks))))))
;; The binder `n` (a description's if `d`) refers to in `env`, innermost
;; first: -1 if none; -2 if a module's names come first, which may have it.
(define captor-of (->* (symbol bool env) int)
  (lambda (n d env)
    (let ((l (env-lookup env n d 0 binder-name)))
      (case (extract l 1) ((0) (extract l 2)) ((1) -2) (else -1)))))
;; The binders a form's definitions bind (its root `root`'s export).
(define root-binders (->* (fails int syn) ints)
  (lambda (fail root x)
    (tagcase (node-kids root)
      (k-form (f)
        (let ((ex (node-export f)))
          (if (null? ex) nil (levels-binders (exported fail ex x)))))
      (else y nil))))
(define levels-binders (->* (levels) ints)
  (lambda (ls)
    (if (null? ls)
        nil
        (append (tagcase (car ls) (lv-rib (as) (atms-binders as)) (else y nil))
                (levels-binders (cdr ls))))))
(define atms-binders (->* (atms) ints)
  (lambda (as)
    (if (null? as)
        nil
        (append (tagcase (car as) (atm-lit (b d) (list b)) (else y nil))
                (atms-binders (cdr as))))))
;; Each captor, `cs`, with its fresh name, `%x~N`: spelled apart from a
;; template's fresh names, which another count makes.
(define-type captors (listof (tupleof int symbol) acyclic))
(define captors-made (ref int rs) (new 0))
(define captors-named (->* (ints captors) captors)
  (lambda (cs out)
    (if (null? cs)
        out
        (tagcase (node-kids (car cs))
          (k-binder (n e)
            (begin
              (set captors-made (+ (get captors-made) 1))
              (captors-named (cdr cs)
                             (cons (tuple (car cs)
                                          (string->symbol
                                           (string-append "%" (symbol->string n) "~"
                                                          (int->string (get captors-made)))))
                                   out))))
          (else y (captors-named (cdr cs) out))))))
;; Each captor of `fresh` written as its fresh name, onto `out`.
(define binders-renamed (->* (captors parts) parts)
  (lambda (fresh out)
    (if (null? fresh)
        out
        (binders-renamed (cdr fresh)
                         (cons (tuple (node-path (extract (car fresh) 1))
                                      (renamed-at (extract (car fresh) 2)
                                                  (node-syn (extract (car fresh) 1))))
                               out)))))
;; Each reference `fs` reaches to a captor of `fresh`, written as its fresh
;; name, onto `out`.
(define captors-renamed (->* (found captors parts) parts)
  (lambda (fs fresh out)
    (if (or (null? fs) (null? fresh))
        out
        (captors-renamed
          (cdr fs) fresh
          (let ((at (extract (car fs) 1)))
            (tagcase (node-kids at)
              (k-ref (n d free)
                (let ((f (if (string=? (alias-base (symbol->string n)) "")
                             (captor-name (captor-of n d (extract (car fs) 2)) fresh)
                             nil)))
                  (if (null? f)
                      out
                      (cons (tuple (node-path at) (renamed-at (car f) (node-syn at))) out))))
              (else y out)))))))
(define captor-name (->* (int captors) (listof symbol acyclic))
  (lambda (b fresh)
    (cond ((null? fresh) nil)
          ((= b (extract (car fresh) 1)) (list (extract (car fresh) 2)))
          (else (captor-name b (cdr fresh))))))
(define renamed-at (->* (symbol syn) syn)
  (lambda (n s)
    (let ((ab (syn-span s))) (mk-symbol (symbol->string n) (extract ab 1) (extract ab 2)))))
;; Alias `base`, of a description's if `d`, written as `free` says (0 a
;; value, 1 qualified, 2 as written, 3 a `with`'s module) where its macro
;; is defined, `h`, at `s`'s place (`macros/hygiene.rs`'s `top_made`).
(define alias-written (->* (fails string bool int def-env syn) syn)
  (lambda (fail base d free h s)
    (let* ((ab (syn-span s)) (a (extract ab 1)) (b (extract ab 2))
           (with-of (lambda ((m string))
                      (mk-list (list (mk-symbol "with" a b) (mk-symbol m a b) (mk-symbol base a b))
                               a b))))
      (case (extract h 1)
        ((0)
          (cond ((or (= free 0) (and (= free 3) (not d))) (with-of "#%toplevel"))
                ((= free 2) (mk-symbol base a b))
                (else (mk-symbol (string-append "#%toplevel:" base) a b))))
        ((2) (mk-symbol base a b))
        (else
          (cond ((and (= free 0) (name-in? (string->symbol base) (extract h 3)))
                 (with-of (symbol->string (extract h 2))))
                ((= free 0) (with-of "#%fx"))
                ((= free 2) (mk-symbol base a b))
                ;; A file's macro writes its descriptions through its module
                ;; whole (`act-module-type`).
                (else
                 (begin (fail-at fail (string-append "`" base "`: a file's macro's description "
                                                     "named apart from its module, not yet")
                                 s)
                        s))))))))
;; Where expansion `k`'s macro was defined, of `hs`: the top level if none
;; is said.
(define def-env-of (->* (int def-envs) def-env)
  (lambda (k hs)
    (cond ((null? hs) (def-env-top))
          ((= k (extract (car hs) 1)) (extract (car hs) 2))
          (else (def-env-of k (cdr hs))))))
;; The expansion that made alias `x`, its outermost `%~N:`'s `N`; else 0.
(define alias-made (->* (string) int)
  (lambda (x)
    (let ((c (if (and (> (string-length x) 2) (string=? (substring x 0 2) "%~"))
                 (digits-end x 2)
                 -1)))
      (if (> c 2) (digits-value x 2 c 0) 0))))
(define digits-value (->* (string int int int) int)
  (lambda (s i end acc)
    (if (>= i end)
        acc
        (digits-value s (+ i 1) end
                      (+ (* acc 10) (- (char->integer (string-ref s i)) (char->integer #\0)))))))
;; Whether a binder in `env` binds `n`, a description's if `d`.
(define bound-in? (->* (symbol bool env) bool)
  (lambda (n d env) (bound-from? n d env 0)))
;; The same, looked for from place `from`, past each module's names.
(define bound-from? (->* (symbol bool env int) bool)
  (lambda (n d env from)
    (let ((l (env-lookup env n d from binder-name)))
      (case (extract l 1) ((0) #t) ((1) (bound-from? n d env (extract l 3))) (else #f)))))
;; Each alias an expansion defined at the top level, a description's if
;; marked: a name of its own wherever later forms name it.
(define aliases-defined (ref (listof (tupleof symbol bool) acyclic) rs) (new nil))
(define alias-defined? (->* (symbol bool) bool)
  (lambda (n d) (alias-defined-in? n d (get aliases-defined))))
(define alias-defined-in? (->* (symbol bool (listof (tupleof symbol bool) acyclic)) bool)
  (lambda (n d xs)
    (and (not (null? xs))
         (or (and (symbol=? n (extract (car xs) 1)) (eq? d (extract (car xs) 2)))
             (alias-defined-in? n d (cdr xs))))))
;; The aliases form `x`'s definitions (its root `root`'s export) bind, noted.
(define aliases-defined-in (->* (fails int syn) unit)
  (lambda (fail root x)
    (tagcase (node-kids root)
      (k-form (f)
        (let ((ex (node-export f)))
          (if (null? ex) #u (aliases-noted (exported fail ex x)))))
      (else y #u))))
(define aliases-noted (->* (levels) unit)
  (lambda (ls)
    (if (null? ls)
        #u
        (begin
          (tagcase (car ls) (lv-rib (as) (atms-aliases-noted as)) (else y #u))
          (aliases-noted (cdr ls))))))
(define atms-aliases-noted (->* (atms) unit)
  (lambda (as)
    (if (null? as)
        #u
        (begin
          (tagcase (car as)
            (atm-lit (b d)
              (tagcase (node-kids b)
                (k-binder (n e)
                  (if (string=? (alias-base (symbol->string n)) "")
                      #u
                      (set aliases-defined (cons (tuple n d) (get aliases-defined)))))
                (else y #u)))
            (else y #u))
          (atms-aliases-noted (cdr as))))))
;; `s`, at `path` (innermost step first, as a walk's), each part of `ws` at
;; its path written so.
(define with-parts (->* (syn addr (listof (tupleof addr syn) acyclic)) syn)
  (lambda (s path ws) (parts-under s (parts-from-top ws))))
;; `ws`, each its path outermost step first (`writings-from-top`).
(define parts-from-top (->* (parts) parts)
  (lambda (ws)
    (if (null? ws)
        nil
        (cons (tuple (the addr (reverse (extract (car ws) 1))) (extract (car ws) 2))
              (parts-from-top (cdr ws))))))
;; `s` with each of `ws`, under it by the steps left of each, put in place:
;; itself where none is; each step taken once (`written-under`).
(define parts-under (->* (syn parts) syn)
  (lambda (s ws)
    (let ((w (part-at nil ws)))
      (cond ((not (null? w)) (car w))
            ((null? ws) s)
            (else
             (tagcase s
               (lst (items d a b x)
                 (let ((xs (parts-items items ws))) (lst xs (syn-datums xs) a b x)))
               (dotted (items t d a b x)
                 (let ((xs (parts-items items ws)))
                   (dotted xs (parts-under t (parts-past ws (len items))) (syn-datums xs) a b x)))
               (else y s)))))))
(define parts-items (->* (syns-a parts) syns-a)
  (lambda (xs ws)
    (if (null? xs)
        nil
        (cons (parts-under (car xs) (part-step ws #t)) (parts-items (cdr xs) (part-step ws #f))))))
;; Those of `ws` whose next step is `step`, past it; past `k` cdrs.
(define part-step (->* (parts bool) parts)
  (lambda (ws step)
    (cond ((null? ws) nil)
          ((let ((p (extract (car ws) 1))) (and (not (null? p)) (eq? (car p) step)))
           (cons (tuple (cdr (extract (car ws) 1)) (extract (car ws) 2)) (part-step (cdr ws) step)))
          (else (part-step (cdr ws) step)))))
(define parts-past (->* (parts int) parts)
  (lambda (ws k) (if (= k 0) ws (parts-past (part-step ws #f) (- k 1)))))
(define part-at (->* (addr parts) (listof syn acyclic))
  (lambda (p ws)
    (cond ((null? ws) nil)
          ((addr=? p (extract (car ws) 1)) (list (extract (car ws) 2)))
          (else (part-at p (cdr ws))))))
;; `x`'s name as where its alias's macro was defined, if it is an alias
;; (`%~N:x`): every `%~N:` taken off; else "" (`macros-procedural.fx`'s).
(define alias-base (->* (string) string)
  (lambda (n) (alias-base-from n #f)))
(define alias-base-from (->* (string bool) string)
  (lambda (n any)
    (let ((c (if (and (> (string-length n) 2) (string=? (substring n 0 2) "%~"))
                 (digits-end n 2)
                 -1)))
      (if (and (> c 2) (< c (string-length n)) (char=? (string-ref n c) #\:))
          (alias-base-from (substring n (+ c 1) (string-length n)) #t)
          (if any n "")))))
(define digits-end (->* (string int) int)
  (lambda (s i)
    (if (and (< i (string-length s)) (char-numeric? (string-ref s i))) (digits-end s (+ i 1)) i)))
