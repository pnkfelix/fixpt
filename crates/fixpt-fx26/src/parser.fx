;;; The FX-26 parser, in FX-26 (PLAN.md §11, step 9a).
;;;
;;; What the eager reader read (`syn`, with positions) to an abstract syntax
;;; tree, with the Rust parser's desugarings (`crates/fixpt-fx26/src/parse.rs`),
;;; node for node and span for span, so the two can be compared. Descriptions
;;; (types, effects, regions, binders) are kept as the syntax they were
;;; written in: the evaluator and the compiler do not need them, and the
;;; checker written in FX-26 (`check-*.fx`) reads them itself.
;;;
;;; A module file of the reader's regions and its own (`rp`), loading the
;;; reader's types at those, not the reader: `syn` is in the reader's
;;; region `rs`. The trees are
;;; `acyclic`: made by `cons` straight into the frozen region, never written,
;;; so a walk of one ends (`docs/fx26.md`, "Well-founded recursion"). A parse
;;; that fails aborts to a prompt in `rp`; it touches no other region, so
;;; `parse-program` is licensed as the reader's entry points are.
(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
;; The reader's types, and `syn->datum` (`syn.fx`), at these regions, and
;; what this file uses of them.
(define reader-types ((proj (load-module "fx26:eager-reader-types.fx") rs re rm rc)))
(import reader-types atom lst dotted vec (type syn))
(define syn-module ((proj (load-module "fx26:syn.fx") rs re rm rc)))
(import syn-module syn->datum)
;; Its types, at these regions (`parser-types.fx`), and the names it uses
;; of them.
(define parser-types ((proj (load-module "fx26:parser-types.fx") rs re rm rc rp)))
(import parser-types e-var e-int e-bool e-str e-char e-float e-sym e-unit e-lambda e-app e-plambda
        e-proj e-if e-letrec e-let e-begin e-prompt e-letregion e-rlambda e-the e-convention
        e-bloblet e-product e-extract e-sum e-tagcase e-module e-with t-define t-define-rec
        t-define-type t-define-effect t-define-convention t-define-syscall t-define-generative
        t-exp p-ok p-err
        (type syns-a names exp top exp-list param-list letrec-list let-list arm-list top-list
              mod-item mod-items presult loaded-file loaded-files) (effect tree-builds parses))

(define parse-tag (prompt-tag presult presult (maxeff tree-builds (write rs) spin) rp)
  (make-continuation-prompt-tag))

;;; -------------------------------------------------------- looking at syn

(define syn-start (->* (syn) int)
  (lambda (s)
    (tagcase s (atom (d a b) a) (lst (i d a b) a) (dotted (i t d a b) a) (vec (i d a b) a))))
(define syn-end (->* (syn) int)
  (lambda (s)
    (tagcase s (atom (d a b) b) (lst (i d a b) b) (dotted (i t d a b) b) (vec (i d a b) b))))

(define pfail (->* (string syn) void)
  (lambda (message s)
    (abort-current-continuation parse-tag (p-err message (syn-start s) (syn-end s)))))
(define pfail-at (->* (string int int) void)
  (lambda (message a b) (abort-current-continuation parse-tag (p-err message a b))))

(define syn-symbol? (->* (syn) bool)
  (lambda (s) (tagcase s (atom (d a b) (symbol? d)) (else x #f))))
(define syn-name (->* (syn) string)
  (lambda (s)
    (tagcase s
      (atom (d a b) (if (symbol? d) (symbol->string d) ""))
      (else x ""))))
;; A form's head as a symbol, to compare with the keywords: any that is
;; not a name is taken as `()`, which is none of them.
(define syn-head (->* (syn) symbol)
  (lambda (s)
    (tagcase s
      (atom (d a b) (if (symbol? d) d '|()|))
      (else x '|()|))))
(define syn-symbol (->* (syn) symbol)
  (lambda (s) (if (syn-symbol? s) (syn-head s) (pfail "a name" s))))
;; `#t`, `#f` and `#u` as the FX-26 reader gives them: symbols.
(define sym-true symbol (string->symbol "#t"))
(define sym-false symbol (string->symbol "#f"))
(define sym-unit symbol (string->symbol "#u"))
;; `()`, which reads as an empty list.
(define syn-nil? (->* (syn) bool)
  (lambda (s) (tagcase s (lst (items d a b) (null? items)) (else x #f))))
;; A proper list's items; `what`, when it is not one.
(define syn-items (->* (syn string) syns-a)
  (lambda (s what)
    (tagcase s
      (lst (items d a b) items)
      (else x (pfail (string-append what ": expected a list") s)))))
(define syn-int (->* (syn) int)
  (lambda (s) (tagcase s (atom (d a b) (if (datum-int? d) d -1)) (else x -1))))

(define len (->* (syns-a) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (len (cdr xs))))))
(define nth (->* (syns-a int) syn)
  (lambda (xs i) (if (= i 0) (car xs) (nth (cdr xs) (- i 1)))))
(define drop (->* (syns-a int) syns-a)
  (lambda (xs i) (if (= i 0) xs (drop (cdr xs) (- i 1)))))

;; A label or tag: a name, or a natural number, which is its digits.
(define label (->* (syn) symbol)
  (lambda (s)
    (cond ((syn-symbol? s) (syn-head s))
          ((>= (syn-int s) 0) (string->symbol (int->string (syn-int s))))
          (else (pfail "a label is a name or a natural number" s)))))

(define keep (->* (syns-a) syns-a)
  (lambda (xs) (if (null? xs) nil (cons (car xs) (keep (cdr xs))))))

;; `(tag x …)` with `n` items, or fail with `shape`.
(define arity (->* (syns-a int string int int) unit)
  (lambda (items n shape a b) (if (= (len items) n) #u (pfail-at shape a b))))
(define at-least (->* (syns-a int string int int) unit)
  (lambda (items n shape a b) (if (< (len items) n) (pfail-at shape a b) #u)))

(define mk-symbol (->* (string int int) syn)
  (lambda (n a b) (atom (string->symbol n) a b)))
(define syn-datums (->* (syns-a) (listof datum acyclic))
  (lambda (xs) (if (null? xs) nil (cons (syn->datum (car xs)) (syn-datums (cdr xs))))))
(define mk-list (->* (syns-a int int) syn)
  (lambda (items a b) (lst items (syn-datums items) a b)))
;; A parameter: `name`, or `(name type)`.
(define parse-param (->* (syn) (tupof (1 symbol) (2 syns-a)))
  (lambda (p)
    (if (syn-symbol? p)
        (tup (1 (syn-symbol p)) (2 (the syns-a nil)))
        (let ((pair (syn-items p "a parameter")))
          (if (= (len pair) 2)
              (tup (1 (syn-symbol (car pair))) (2 (the syns-a (cons (nth pair 1) nil))))
              (pfail "a parameter is `name` or `(name type)`" p))))))
(define parse-params (->* (syn) param-list)
  (lambda (ps)
    (if (syn-nil? ps)
        nil
        (letrec ((each (subr (maxeff (read @globals) parses) (syns-a) param-list)
                   (lambda (xs)
                     (if (null? xs)
                         nil
                         (let ((p (parse-param (car xs))))
                           (cons p (each (cdr xs))))))))
          (each (syn-items ps "parameters"))))))

;; A bloblet form's field index: a literal, non-negative integer.
(define field-index (->* (syn) int)
  (lambda (s)
    (if (>= (syn-int s) 0)
        (syn-int s)
        (pfail "a field index is a literal, non-negative integer" s))))

;; A form's head, as `syn-head` gives it: `()` if it is not a list, or is
;; empty.
(define form-head (->* (syn) symbol)
  (lambda (s)
    (tagcase s
      (lst (items d a b) (if (null? items) '|()| (syn-head (car items))))
      (else x '|()|))))
;; Whether `s` is a form headed `keyword`.
(define form-of? (->* (syn symbol) bool)
  (lambda (s keyword) (symbol=? (form-head s) keyword)))

(define arm-else? (->* (syn) bool)
  (lambda (c) (form-of? c 'else)))

(define parse-names (->* (syns-a) names)
  (lambda (xs) (if (null? xs) nil (cons (syn-symbol (car xs)) (parse-names (cdr xs))))))

;; `(listof t acyclic)`, spanning `a`..`b`.
(define mk-listof-acyclic (->* (syn int int) syn)
  (lambda (t a b)
    (let ((listof (mk-symbol "listof" a b)) (acyclic (mk-symbol "acyclic" a b)))
      (mk-list (list listof t acyclic) a b))))
(define vlambda-usage string "`(vlambda name body …)` or `(vlambda (name type) body …)`")
;; A `vlambda`'s parameter: `xs`, or `(xs T)`, whose type is then
;; `(listof T acyclic)`.
(define parse-vparam (->* (syn int int) (tupof (1 symbol) (2 syns-a)))
  (lambda (given a b)
    (if (syn-symbol? given)
        (tup (1 (syn-symbol given)) (2 (the syns-a nil)))
        (let ((pair (syn-items given "a parameter")))
          (if (= (len pair) 2)
              (let ((ty (mk-listof-acyclic (nth pair 1) a b)))
                (tup (1 (syn-symbol (car pair))) (2 (the syns-a (cons ty nil)))))
              (pfail vlambda-usage given))))))

;; Whether `head` is a region form's, and what that makes besides the
;; region, as `e-letregion` has it.
(define region-form? (->* (symbol) bool)
  (lambda (head)
    (or (or (symbol=? head 'letregion) (symbol=? head 'letfreeze))
        (or (symbol=? head 'letrena) (symbol=? head 'letreap)))))
(define region-kind (->* (symbol) int)
  (lambda (head)
    (case head ((letregion) 0)
               ((letrena) 1)
               ((letreap) 2)
               (else 3))))
;; `(r p)`'s items, if a `letfreeze` binds that as `given`; else none.
(define freeze-pair (->* (symbol syn) syns-a)
  (lambda (head given)
    (tagcase given
      (lst (xs d a2 b2) (if (and (symbol=? head 'letfreeze) (= (len xs) 2)) xs (the syns-a nil)))
      (else x (the syns-a nil)))))

;; A call `(f tmp more …)`, spanning `a`..`b`; and a `let`'s one binding.
;; `(with #%fx f)`: what an expansion calls, the standard binding, whatever
;; shadows or redefines `f` where it is (`TODO.md` §46).
(define standard-ref (->* (symbol int int) exp)
  (lambda (f a b) (e-with '#%fx (e-var f a b 0) a b 0)))
(define call-tmp (->* (symbol symbol exp-list int int) exp)
  (lambda (f tmp more a b)
    (e-app (standard-ref f a b) (the exp-list (cons (e-var tmp a b 0) more)) a b 0)))
(define one-let (->* (symbol exp) let-list)
  (lambda (name e) (the let-list (cons (tup (1 name) (2 e)) nil))))

;; Whether `head` is a bloblet form's; and whether `op` with `n` arguments
;; is one that takes no field index, with the right number.
(define bloblet-form? (->* (symbol) bool)
  (lambda (head)
    (or (symbol=? head 'make-bloblet) (symbol=? head 'rmake-bloblet) (symbol=? head 'bloblet-ref)
        (symbol=? head 'bloblet-set!) (symbol=? head 'bloblet-freeze) (symbol=? head 'bloblet-byte)
        (symbol=? head 'bloblet-set-byte!) (symbol=? head 'bloblet-bytes) (blobref-form? head))))
;; Whether `head` is a `blobref` form's (`TODO.md` §77).
(define blobref-form? (->* (symbol) bool)
  (lambda (head)
    (or (symbol=? head 'blobref-at) (symbol=? head 'blobref+) (symbol=? head 'blobref-owner)
        (symbol=? head 'blobref-offset) (symbol=? head 'blobref-get)
        (symbol=? head 'blobref-set!) (symbol=? head 'blobref-index)
        (symbol=? head 'blobref-length) (symbol=? head 'blobref-variant!))))
(define bloblet-untagged? (->* (symbol int) bool)
  (lambda (op n)
    (or (and (symbol=? op 'bloblet-freeze) (= n 1)) (and (symbol=? op 'bloblet-byte) (= n 2))
        (and (symbol=? op 'bloblet-set-byte!) (= n 3)) (and (symbol=? op 'bloblet-bytes) (= n 1))
        (and (blobref-form? op)
             (= n (if (or (symbol=? op 'blobref-owner) (symbol=? op 'blobref-offset)
                          (symbol=? op 'blobref-get) (symbol=? op 'blobref-length))
                      1
                      2))))))

;; A `confirm-length`'s length, `n`: a natural literal, or -1 for a
;; variable holding a `nat`.
(define confirm-length-k (->* (syn) int)
  (lambda (n)
    (cond ((>= (syn-int n) 0) (syn-int n))
          ((syn-symbol? n) -1)
          (else (pfail "a length is a natural number, or a variable holding one" n)))))
;; What a region form says when its name is not one, or has an `@`.
(define region-name-error (->* (symbol) string)
  (lambda (head)
    (string-append "a `" (symbol->string head) "` binds a region variable's name, without `@`")))

;; The names a `tagcase` arm binds, `bind`: a product's fields, `(name
;; …)`, if `fields`; else the one value's name.
(define arm-names (->* (bool syn) names)
  (lambda (fields bind)
    (if fields
        (parse-names (syn-items bind "the names an arm binds"))
        (the names (cons (syn-symbol bind) nil)))))
;; An integer literal past a fixnum, `v`, as arithmetic on fixnums, which
;; every path does, bignums included (PLAN.md Q2): `(- 0 x)` for a
;; negative; else, in base 10⁹, `(+ (* rest 1000000000) last)`, `rest`
;; again so until it is a fixnum. The Rust parser's `big_literal`, node for
;; node: here the limbs are peeled off, least first, then built outwards.
(define big-literal (->* (int int int) exp)
  (lambda (v a b)
    (letrec ((call (subr (maxeff (read @globals) spin) (symbol exp exp) exp)
                   (lambda (f x y)
                     (e-app (e-var f a b 0) (the exp-list (cons x (the exp-list (cons y nil))))
                            a b 0)))
             (fixnum? (subr spin (int) bool)
                      (lambda (n) (and (<= n 1152921504606846975) (>= n -1152921504606846976))))
             ;; The limbs below the first fixnum, most significant first.
             (peel (subr (maxeff (read @globals) spin) (int (listof int acyclic)) exp)
                   (lambda (n limbs)
                     (if (fixnum? n)
                         (build (e-int n a b 0) limbs)
                         (peel (quotient n 1000000000) (cons (remainder n 1000000000) limbs)))))
             (build (subr (maxeff (read @globals) spin) (exp (listof int acyclic)) exp)
                    (lambda (acc limbs)
                      (if (null? limbs)
                          acc
                          (let ((scaled (call '* acc (e-int 1000000000 a b 0))))
                            (build (call '+ scaled (e-int (car limbs) a b 0)) (cdr limbs)))))))
      (cond ((fixnum? v) (e-int v a b 0))
            ((< v 0) (call '- (e-int 0 a b 0) (peel (- 0 v) nil)))
            (else (peel v nil))))))

;; Whether `s` is a string literal; and the string it is.
(define syn-string? (->* (syn) bool)
  (lambda (s) (tagcase s (atom (d a b) (string? d)) (else x #f))))
(define syn-string (->* (syn) string)
  (lambda (s)
    (tagcase s (atom (d a b) (if (string? d) d "")) (else x ""))))
;; `t` alone in a list.
(define one-syn (->* (syn) syns-a) (lambda (t) (cons t nil)))
;; A module's item, of one name.
(define mod-item-of (->* (int symbol syns-a exp-list) mod-item)
  (lambda (k name ts xs) (tup (1 k) (2 (the names (cons name nil))) (3 ts) (4 xs))))
;; Whether a `define-type`'s head is `(d (p k) …)`: a name with parameters.
(define param-head? (->* (syn) bool)
  (lambda (head)
    (tagcase head
      (lst (xs d a b) (and (not (null? xs)) (not (null? (cdr xs)))))
      (else x #f))))
;; `(define-type (d (p k) …) T)` in a module, at `a`..`b`: `(define-type d
;; (dlambda ((p k) …) T))`, what a `define-datatype` with parameters expands
;; to, in a `load-module`'s file too, as the Rust parser's `parse_module_in`.
(define param-desc-item (->* (int int syn syn) mod-item)
  (lambda (a b head t)
    (let* ((hs (tagcase head (lst (xs d a b) xs) (else x (the syns-a nil))))
           (ha (syn-start head))
           (hb (syn-end head))
           (params (mk-list (cdr hs) ha hb))
           (fun (mk-list (list (mk-symbol "dlambda" ha hb) params t) a b)))
      (mod-item-of 1 (syn-symbol (car hs)) (one-syn fun) nil))))
;;; ------------------------------------------------------------ include

;; A module's `(include m)`s (`TODO.md` §69), as `parse.rs`'s
;; `with_includes`: one hidden item first, `%include`, a module of hidden
;; items `%include-0`, … that are the modules included, made before the
;; module's own items and seeing none of them; each own item's value in a
;; `(with %include …)` (a lambda's body, so that it stays a lambda), its
;; place the item's, as the compilers find facts by place. An `include`
;; is read as an item of kind 9, its form kept for its place.
(define include-form? (->* (syn) bool)
  (lambda (f)
    (tagcase f
      (lst (xs d a b) (and (not (null? xs)) (symbol=? (syn-head (car xs)) 'include)))
      (else y #f))))
(define any-include? (->* (syns-a) bool)
  (lambda (fs)
    (and (not (null? fs))
         (or (include-form? (car fs)) (any-include? (hide-forms (car fs)))
             (any-include? (cdr fs))))))
;; `(hide item …)` (`TODO.md` §69): its items, each hidden; none if `f` is
;; not one.
(define hide-forms (->* (syn) syns-a)
  (lambda (f)
    (tagcase f
      (lst (xs d a b) (if (and (not (null? xs)) (symbol=? (syn-head (car xs)) 'hide)) (cdr xs) nil))
      (else y nil))))
(define hide-form? (->* (syn) bool)
  (lambda (f)
    (tagcase f
      (lst (xs d a b) (and (not (null? xs)) (symbol=? (syn-head (car xs)) 'hide)))
      (else y #f))))
;; Each name hidden item `it` (read from `f`) defines, marked by a type of
;; its own, onto `rest`: a type's `%hidden:name`, a value's `%hiddenv:name`
;; (a type and a value may share a name); types, so that no compiler makes
;; a value of them; the checkers leave them out of the module's type. A
;; hidden `include` is `%hinclude`. As `parse.rs`.
(define hidden-marks (->* (mod-item syn mod-items) mod-items)
  (lambda (it f rest)
    (let* ((k (extract it 1)) (ns (extract it 2)) (a (syn-start f)) (b (syn-end f)))
      (cond ((= k 9)
             (cons (tup (1 9) (2 (the names (list '%hinclude))) (3 (extract it 3))
                            (4 (extract it 4)))
                   rest))
            ((= k 0)
             (let ((t (symbol->string (car ns))))
               (cons it (hidden-marks-of "%hidden:" (the names (list (car ns))) a b
                                         (hidden-marks-of "%hiddenv:"
                                                          (the names
                                                               (list (string->symbol
                                                                      (string-append "up-" t))
                                                                     (string->symbol
                                                                      (string-append "down-" t))))
                                                          a b rest)))))
            (else (cons it (hidden-marks-of (if (= k 1) "%hidden:" "%hiddenv:") ns a b rest)))))))
(define hidden-marks-of
  (->* (string names int int mod-items) mod-items)
  (lambda (prefix ns a b rest)
    (if (null? ns)
        rest
        (cons (mod-item-of 1 (string->symbol (string-append prefix (symbol->string (car ns))))
                           (one-syn (mk-symbol "unit" a b)) nil)
              (hidden-marks-of prefix (cdr ns) a b rest)))))
;; `x` in `(with %include …)` at `a`..`b`: a lambda's body, under any
;; `plambda`, `the` or region lambda.
(define in-includes (->* (exp int int) exp)
  (lambda (x a b)
    (tagcase x
      (e-lambda (ps body la lb lalbk) (e-lambda ps (e-with '%include body a b 0) la lb lalbk))
      (e-plambda (bs body la lb lalbk) (e-plambda bs (in-includes body a b) la lb lalbk))
      (e-the (t e la lb lalbk) (e-the t (in-includes e a b) la lb lalbk))
      (e-rlambda (r l la lb lalbk) (e-rlambda r (in-includes l a b) la lb lalbk))
      (else y (e-with '%include x a b 0)))))
;; Each of `xs` so, at the place of the binding of `bs` it is.
(define inits-in-includes (->* (exp-list syns-a) exp-list)
  (lambda (xs bs)
    (if (or (null? xs) (null? bs))
        xs
        (cons (in-includes (car xs) (syn-start (car bs)) (syn-end (car bs)))
              (inits-in-includes (cdr xs) (cdr bs))))))
;; Item `it`, read from form `f`, its values so.
(define item-in-includes (->* (mod-item syn) mod-item)
  (lambda (it f)
    (let ((k (extract it 1)) (xs (extract it 4)))
      (tup (1 k) (2 (extract it 2)) (3 (extract it 3))
               (4 (cond ((= k 2) (inits-in-includes xs (one-syn f)))
                        ((= k 3) (tagcase f (lst (bs d a b) (inits-in-includes xs (cdr bs)))
                                   (else y xs)))
                        (else xs)))))))
;; The included modules of `items`, from `%include-k` on.
(define include-items (->* (mod-items int) mod-items)
  (lambda (items k)
    (cond ((null? items) nil)
          ((= (extract (car items) 1) 9)
           (cons (mod-item-of 2 (include-name (car (extract (car items) 2)) k) nil
                              (extract (car items) 4))
                 (include-items (cdr items) (+ k 1))))
          (else (include-items (cdr items) k)))))
;; The `k`th included module's item's name: `%hinclude-k` if hidden.
(define include-name (->* (symbol int) symbol)
  (lambda (n k)
    (string->symbol
     (string-append (if (symbol=? n '%hinclude) "%hinclude-" "%include-") (int->string k)))))
;; `items` but their includes; and the first include's form.
(define own-items (->* (mod-items) mod-items)
  (lambda (items)
    (cond ((null? items) nil)
          ((= (extract (car items) 1) 9) (own-items (cdr items)))
          (else (cons (car items) (own-items (cdr items)))))))
(define first-include (->* (mod-items) syns-a)
  (lambda (items)
    (cond ((null? items) nil)
          ((= (extract (car items) 1) 9) (extract (car items) 3))
          (else (first-include (cdr items))))))
;; A module's items, its includes made one `%include` first.
(define with-includes (->* (mod-items) mod-items)
  (lambda (items)
    (let ((f (first-include items)))
      (if (null? f)
          items
          (cons (mod-item-of 2 '%include nil
                             (list (e-module (include-items items 0) (syn-start (car f))
                                             (syn-end (car f)) 0)))
                (own-items items))))))

;; `(lambda (x) x)`, spanning `a`..`b`: an abstract type's conversion.
(define identity-at (->* (int int) exp)
  (lambda (a b)
    (let ((x (tup (1 'x) (2 (the syns-a nil)))))
      (e-lambda (the param-list (cons x nil)) (e-var 'x a b 0) a b 0))))
(define module-usage string
  (string-append "a module holds `(define-generative t T)`, `(define-type d T)`, "
                 "`(define-effect e E)`, `(define x [T] e)`, `(define* f T e)`, "
                 "`(define-rec (f T e) …)`, `(include m)` and `(hide item …)`"))
;; A `define-rec`'s names, types and expressions, each in order.
(define rec-names (->* (letrec-list) names)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 1) (rec-names (cdr bs))))))
(define rec-types (->* (letrec-list) syns-a)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 2) (rec-types (cdr bs))))))
(define rec-inits (->* (letrec-list) exp-list)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 3) (rec-inits (cdr bs))))))

;;; ------------------------------------------------------------ expressions

;;; FX-91's `(define-datatype name (tag type …) …)`, expanded as the Rust
;;; reader expands it (`top.rs`'s `expand_datatype`), as syntax, into the
;;; forms it stands for: a sum of products, each variant's members labelled
;;; from 1, `(define-type name (oneof (tag (tupof (1 T) …)) …))`, and a
;;; constructor per tag, `(define tag (subr pure (T …) name) (lambda (%x1 …)
;;; (one tag (tup (1 %x1) …))))`. Where the form is: a program's, a
;;; module's, or a module file's, each parsing what it is made into.

(define datatype? (->* (syn) bool)
  (lambda (s) (form-of? s 'define-datatype)))

(define mk-int (->* (int int int) syn) (lambda (i a b) (atom i a b)))
;; `(keyword item …)`; `(subr pure (member …) result)`; and `(poly (binder
;; …) body)`: each spanning `a`..`b`.
(define mk-form (->* (string syns-a int int) syn)
  (lambda (keyword items a b) (mk-list (cons (mk-symbol keyword a b) items) a b)))
(define mk-pure-subr (->* (syns-a syn int int) syn)
  (lambda (members result a b)
    (let ((pure (mk-symbol "pure" a b)) (args (mk-list members a b)))
      (mk-form "subr" (list pure args result) a b))))
(define mk-poly (->* (syns-a syn int int) syn)
  (lambda (binders body a b)
    (mk-form "poly" (list (mk-list binders a b) body) a b)))
;; A constructor's parameters, `%x1 …`, from `i`.
(define dt-vars (->* (syns-a int int int) syns-a)
  (lambda (ms i a b)
    (if (null? ms)
        nil
        (let ((x (mk-symbol (string-append "%x" (int->string i)) a b)))
          (cons x (dt-vars (cdr ms) (+ i 1) a b))))))
;; `(1 m1) (2 m2) …`, from `i`.
(define dt-labelled (->* (syns-a int int int) syns-a)
  (lambda (ms i a b)
    (if (null? ms)
        nil
        (let* ((pair (mk-list (list (mk-int i a b) (car ms)) a b))
               (rest (dt-labelled (cdr ms) (+ i 1) a b)))
          (cons pair rest)))))
;; Each variant's arm of the sum, `(tag (tupof (1 T) …))`.
(define dt-arms (->* (syns-a int int) syns-a)
  (lambda (vs a b)
    (if (null? vs)
        nil
        (let* ((v (car vs)) (parts (syn-items v "a variant")))
          (if (or (null? parts) (not (syn-symbol? (car parts))))
              (pfail "a variant is `(tag type …)`" v)
              (let* ((prod (mk-form "tupof" (dt-labelled (cdr parts) 1 a b) a b))
                     (arm (mk-list (list (car parts) prod) a b))
                     (rest (dt-arms (cdr vs) a b)))
                (cons arm rest)))))))
;; Each constructor: of type `(subr pure (member …) used)`, where `used` is
;; the type as it is used, `name` or `(name param …)`; polymorphic in the
;; parameters if there are any (`family?`).
(define dt-constructors (->* (syn bool syns-a syns-a int int) syns-a)
  (lambda (used family? params vs a b)
    (if (null? vs)
        nil
        (let* ((parts (syn-items (car vs) "a variant"))
               (tag (car parts))
               (members (cdr parts))
               (mono (mk-pure-subr members used a b))
               (ty (if family? (mk-poly params mono a b) mono))
               (xs (dt-vars members 1 a b))
               (fields (mk-form "tup" (dt-labelled xs 1 a b) a b))
               ;; At its variant: no two constructors' bodies at one place.
               (body (mk-form "one" (list tag fields) (syn-start (car vs)) (syn-end (car vs))))
               (make (mk-form "lambda" (list (mk-list xs a b) body) a b))
               (ctor (mk-form "define" (list tag ty make) a b))
               (rest (dt-constructors used family? params (cdr vs) a b)))
          (cons ctor rest)))))
;; The parameters' names, from `(name kind) …`.
(define dt-param-names (->* (syns-a) syns-a)
  (lambda (ps)
    (if (null? ps)
        nil
        (let ((p (syn-items (car ps) "a parameter")))
          (if (and (= (len p) 2) (syn-symbol? (car p)))
              (cons (car p) (dt-param-names (cdr ps)))
              (pfail "a parameter is `(name kind)`" (car ps)))))))
;; `(define-datatype name (tag type …) …)`, or with parameters,
;; `(define-datatype (name (param kind) …) …)`, a type family, which its
;; variants may mention with the same parameters: the forms it stands for.
(define expand-datatype (->* (syn) syns-a)
  (lambda (s)
    (let* ((items (syn-items s "a datatype")) (a (syn-start s)) (b (syn-end s))
           (usage "`(define-datatype name (tag type …) …)`"))
      (if (< (len items) 3)
          (pfail usage s)
          (let* ((head (nth items 1))
                 (family? (not (syn-symbol? head)))
                 (hs (if family? (syn-items head "a datatype's name") (the syns-a nil)))
                 (name (cond ((not family?) head)
                             ((and (not (null? hs)) (syn-symbol? (car hs))) (car hs))
                             (else (pfail usage s))))
                 (params (if family? (cdr hs) (the syns-a nil)))
                 (used (if family? (mk-list (cons name (dt-param-names params)) a b) name))
                 (sum (mk-form "oneof" (dt-arms (drop items 2) a b) a b))
                 (ctors (dt-constructors used family? params (drop items 2) a b)))
            (cons (mk-form "define-type" (list head sum) a b) ctors))))))

;; `(import m item …)`: what module `m` gives, by name, defined here, each
;; as it is there, as the Rust reader expands it (`top.rs`'s
;; `expand_import`): a value `x`, `(define x (with m x))`; each of `(type t
;; …)`, `(define-type t (select m t))`; each of `(effect e …)`,
;; `(define-effect e (select m e))`; each at its name.
(define import? (->* (syn) bool)
  (lambda (s) (form-of? s 'import)))
(define import-usage string "`(import module name … (type name …) (effect name …))`")
(define expand-import (->* (syn) syns-a)
  (lambda (s)
    (let ((items (syn-items s "an import")))
      (cond ((< (len items) 2) (pfail import-usage s))
            ((not (syn-symbol? (nth items 1)))
             (pfail (string-append import-usage ": the module, named by a variable") (nth items 1)))
            (else (import-items (nth items 1) (drop items 2)))))))
(define import-items (->* (syn syns-a) syns-a)
  (lambda (m ns)
    (if (null? ns)
        nil
        (let* ((n (car ns))
               (group (lambda () (cdr (syn-items n import-usage))))
               (made (cond ((form-of? n 'type) (import-each "define-type" m (group)))
                           ((form-of? n 'effect) (import-each "define-effect" m (group)))
                           (else (the syns-a (cons (import-one "define" "with" m n) nil))))))
          (append made (import-items m (cdr ns)))))))
(define import-each (->* (string syn syns-a) syns-a)
  (lambda (define m ns)
    (if (null? ns)
        nil
        (cons (import-one define "select" m (car ns)) (import-each define m (cdr ns))))))
;; `(define n (wrap m n))`, at `n`.
(define import-one (->* (string string syn syn) syn)
  (lambda (define wrap m n)
    (if (syn-symbol? n)
        (let ((a (syn-start n)) (b (syn-end n)))
          (mk-form define (list n (mk-form wrap (list m n) a b)) a b))
        (pfail (string-append import-usage ": a name") n))))

;; What builds datum `x`, quoted (`depth` -1) or quasiquoted at `depth`
;; (TODO §51), as `Checker::quoted` builds it: atoms as themselves, symbols
;; quoted, `()` as `nil`, lists as `cons`es, a vector from its list; a list
;; or vector in `(the datum …)`. Under `quasiquote`, `(unquote e)` at depth
;; 1 is `e`, and `(unquote-splicing e)` is `e` appended to what follows.
(define quoted (->* (syn int) syn)
  (lambda (x depth)
    (let ((built (quoted-in x depth)) (a (syn-start x)) (b (syn-end x)))
      (if (and (tagcase x (atom (d c e) #f) (lst (items d c e) (not (null? items))) (else y #t))
               (null? (unquoted x depth)))
          ;; A quote's, not a quasiquote's, marked (`%quote`): everything in
          ;; it the rewrite's, made once where it is all literals.
          (mk-form "the" (list (mk-symbol "datum" a b)
                               (if (< depth 0) (fx-call "%quote" (list built) a b) built))
                   a b)
          built))))
;; `(with #%fx name)`: the standard `name`, whatever a program binds it to.
(define fx-named (->* (string int int) syn)
  (lambda (n a b) (mk-form "with" (list (mk-symbol "#%fx" a b) (mk-symbol n a b)) a b)))
;; `((with #%fx op) arg …)`.
(define fx-call (->* (string syns-a int int) syn)
  (lambda (op args a b) (mk-list (cons (fx-named op a b) args) a b)))
;; `(form e)`: `e`, as a list of none or one.
(define unquote-of (->* (syn string) syns-a)
  (lambda (x form)
    (tagcase x
      (lst (items d a b)
        (if (and (= (len items) 2) (string=? (syn-name (car items)) form)) (cdr items) nil))
      (else y nil))))
(define unquoted (->* (syn int) syns-a)
  (lambda (x depth) (if (= depth 1) (unquote-of x "unquote") nil)))
;; The depth a list's items after its head are at: a nested `quasiquote`
;; deepens, an `unquote` (or `unquote-splicing`) not at depth 1 shallows.
(define quasi-inner (->* (syns-a int) int)
  (lambda (items depth)
    (let ((head (if (null? items) "" (syn-name (car items)))) (two (= (len items) 2)))
      (cond ((< depth 0) depth)
            ((and two (string=? head "quasiquote")) (+ depth 1))
            ((and two (> depth 1)
                  (or (string=? head "unquote") (string=? head "unquote-splicing")))
             (- depth 1))
            (else depth)))))
;; Whether no `unquote` or `unquote-splicing` at depth 1 is in `x`,
;; quasiquoted at `depth`: then it is a constant. As `Checker::unquote_free`.
(define unquote-free? (->* (syn int) bool)
  (lambda (x depth)
    (and (null? (unquoted x depth))
         (tagcase x
           (lst (items d a b) (items-free? items depth (quasi-inner items depth)))
           (dotted (items tail d a b)
             (and (items-free? items depth (quasi-inner items depth)) (unquote-free? tail depth)))
           (vec (items d a b) (items-free? items depth depth))
           (else y #t)))))
;; Whether each of `items`, the first at `depth` and the rest at `inner`, is
;; neither spliced nor reached by an `unquote`.
(define items-free? (->* (syns-a int int) bool)
  (lambda (items depth inner)
    (or (null? items)
        (and (null? (if (= depth 1) (unquote-of (car items) "unquote-splicing") nil))
             (unquote-free? (car items) depth)
             (items-free? (cdr items) inner inner)))))
(define quoted-in (->* (syn int) syn)
  (lambda (x depth)
    (let* ((u (unquoted x depth)) (a (syn-start x)) (b (syn-end x))
           ;; Under a quasiquote, a list or vector no unquote reaches is a
           ;; constant: a quote, made once (`%quote` at its opening).
           (mark? (and (null? u) (>= depth 1)
                       (tagcase x (atom (d c e) #f) (lst (items d c e) (not (null? items)))
                         (else y #t))
                       (unquote-free? x depth)))
           (dq (if mark? -1 depth)))
      (if (not (null? u))
          (car u)
          (let ((built
                 (tagcase x
                   (atom (d c e)
                     (cond ((not (symbol? d))
                            (if (bytevector? d) (pfail "a bytevector cannot be quoted yet" x) x))
                           ((or (symbol=? d sym-true) (symbol=? d sym-false)) x)
                           (else (mk-form "quote" (list x) a b))))
                   ;; `nil` at the list, each `cons` from its item, a constant
                   ;; suffix's `%quote` from its first item to the end.
                   (lst (items d c e)
                     (if (null? items)
                         (mk-symbol "nil" a b)
                         (quoted-items items #f (car items) dq a b)))
                   (dotted (items tail d c e) (quoted-items items #t tail dq a b))
                   (vec (items d c e)
                     (if (null? items)
                         (fx-call "datum-list->vector" (list (fx-named "nil" a b)) a b)
                         (fx-call "datum-list->vector"
                                  (list (quoted-items items #f (car items) dq a b)) a b))))))
            (if mark? (fx-call "%quote" (list built) a b) built))))))
;; A list of `items`, then, if `dotted?`, `tail` (else `nil`), built.
(define quoted-items (->* (syns-a bool syn int int int) syn)
  (lambda (items dotted? tail depth a b)
    (let ((inner (quasi-inner items depth)))
      (quoted-onto items dotted? tail depth
                   (and (>= depth 1) (or (not dotted?) (unquote-free? tail depth)))
                   depth inner #t a b))))
;; `items`, then, if `dotted?`, `tail` (else `nil`), quoted, not
;; quasiquoted.
(define quoted-plain (->* (syns-a bool syn int int) syn)
  (lambda (items dotted? tail a b)
    (if (null? items)
        (if dotted? (quoted-in tail -1) (fx-named "nil" a b))
        (fx-call "cons"
                 (list (quoted-in (car items) -1) (quoted-plain (cdr items) dotted? tail a b))
                 (syn-start (car items)) (syn-end (car items))))))
;; `items` onto the list's end, the first at `depth` and the rest at
;; `inner`: under a quasiquote (`free-tail?` its tail no unquote reaches),
;; the items after the first that no unquote reaches, with the tail, one
;; quote. As `Checker::quoted_in`.
(define quoted-onto (->* (syns-a bool syn int bool int int bool int int) syn)
  (lambda (items dotted? tail ldepth free-tail? depth inner first? a b)
    (cond
      ((null? items) (if dotted? (quoted-in tail ldepth) (fx-named "nil" a b)))
      ((and free-tail? (not first?) (items-free? items inner inner))
       (fx-call "%quote" (list (quoted-plain items dotted? tail a b)) (syn-start (car items)) b))
      (else
        (let ((rest (quoted-onto (cdr items) dotted? tail ldepth free-tail? inner inner #f a b))
              (spliced (if (= depth 1) (unquote-of (car items) "unquote-splicing") nil))
              (ia (syn-start (car items))) (ib (syn-end (car items))))
          (if (null? spliced)
              (fx-call "cons" (list (quoted-in (car items) depth) rest) ia ib)
              (let ((ty (mk-list (list (mk-symbol "listof" a b) (mk-symbol "datum" a b)
                                       (mk-symbol "acyclic" a b))
                                 a b)))
                (fx-call "append" (list (car spliced) (mk-form "the" (list ty rest) a b))
                         ia ib))))))))



;;; ------------------------------------------------------------ files loaded

(define loaded (ref loaded-files rs) (new nil))
;; The same, in the order a driver reads them, depth first, as the parser
;; meets the loads: the next load's, first, most often (`loaded-next-at`).
(define loaded-next (ref loaded-files rs) (new nil))
;; For a driver: what the program's `load-module`s read, the last read
;; first.
(define loaded-files! (->* (loaded-files) unit)
  (lambda (fs) (begin (set loaded fs) (set loaded-next (loaded-onto fs nil)))))
;;; ------------------------------------------------------------ top-level includes

;; For a driver: each top-level `(include m)` of the program, by where it
;; starts, and the names of what `m` gives, its values, types and effects,
;; which only a checker knows (`Checker::include_forms`); or why it is
;; refused, and where.
(define-type include-given
  (tupof (1 int) (2 names) (3 names) (4 names) (5 string) (6 int) (7 int)))
(define-type includes (listof include-given acyclic))
(define includes-given (ref includes rs) (new nil))
(define includes-given! (->* (includes) unit) (lambda (is) (set includes-given is)))
;; What was given of the `include` starting at `a`, in a list of one.
(define include-given-at (->* (includes int) includes)
  (lambda (is a)
    (cond ((null? is) nil)
          ((= (extract (car is) 1) a) (the includes (cons (car is) nil)))
          (else (include-given-at (cdr is) a)))))
;; `xs` reversed onto `ys`.
(define loaded-onto
  (->* (loaded-files loaded-files) loaded-files)
  (lambda (xs ys) (if (null? xs) ys (loaded-onto (cdr xs) (the loaded-files (cons (car xs) ys))))))
;; The positions of one file and the next apart.
(define load-base int 1000000000)

;; Every load of a path is one value, made once (`TODO.md` §68): the first
;; defines a hidden global, `%shared:` and its key (`loaded-key`), as the
;; file loaded, before the form that loads it; every load is that global.
;; The keys loaded, and the definitions not yet placed before their form.
(define shared-keys (ref (listof string acyclic) rs) (new nil))
(define shared-pending (ref top-list rs) (new nil))
;; The files being read now, by key, each with its path as its load wrote
;; it, the innermost first: a load of one of them is a cycle (`TODO.md`
;; §71).
(define loading-keys (ref (listof (pairof string string rs) acyclic) rs) (new nil))
;; A `case`'s data by halving (`TODO.md` §46): each datum's test, the
;; value it sorts by, and its clause.
(define-type case-entry (tupof (1 exp) (2 int) (3 int)))
(define-type case-entries (listof case-entry acyclic))
;; The fewest data a `case` searches by halving, by kind (the Rust parser's
;; `CASE_TREE_*`, measured): integers, strings, symbols; never characters.
;; Where the leaves give an index for a second search (`direct` false),
;; integers and symbols pay only from more.
(define case-tree-from (->* (int bool) int)
  (lambda (k direct)
    (case k ((0) (if direct 8 32)) ((2) 16) ((3) (if direct 32 64)) (else 1000000000))))
;; What datum `d`, of kind `k`, sorts by: the integer, or the runtime's hash.
(define case-sort-key (->* (int syn) int)
  (lambda (k d)
    (let ((x (syn->datum d)))
      (case k
        ((0) (if (int? x) x 0))
        ((2) (if (string? x) (string-hash x) 0))
        (else (if (symbol? x) (symbol-name-hash x) 0))))))
;; `e` into `sorted`, after those of no greater value: a stable sort.
(define case-insert (->* (case-entry case-entries) case-entries)
  (lambda (e sorted)
    (if (or (null? sorted) (< (extract e 2) (extract (car sorted) 2)))
        (the case-entries (cons e sorted))
        (the case-entries (cons (car sorted) (case-insert e (cdr sorted)))))))
(define case-sort (->* (case-entries case-entries) case-entries)
  (lambda (es sorted) (if (null? es) sorted (case-sort (cdr es) (case-insert (car es) sorted)))))
(define case-entries-length (->* (case-entries) int)
  (lambda (es) (if (null? es) 0 (+ 1 (case-entries-length (cdr es))))))
(define case-exps-length (->* (exp-list) int)
  (lambda (es) (if (null? es) 0 (+ 1 (case-exps-length (cdr es))))))
(define case-key-at (->* (case-entries int) int)
  (lambda (es i) (if (= i 0) (extract (car es) 2) (case-key-at (cdr es) (- i 1)))))
(define case-take (->* (case-entries int) case-entries)
  (lambda (es k) (if (= k 0) nil (the case-entries (cons (car es) (case-take (cdr es) (- k 1)))))))
(define case-drop (->* (case-entries int) case-entries)
  (lambda (es k) (if (= k 0) es (case-drop (cdr es) (- k 1)))))
;; Where to halve `n` sorted entries: nearest the middle, between unequal
;; values (0 if none), as the Rust parser's `case_index`.
(define case-mid-up (->* (case-entries int int) int)
  (lambda (es mid n)
    (if (and (< mid n) (> mid 0) (= (case-key-at es mid) (case-key-at es (- mid 1))))
        (case-mid-up es (+ mid 1) n)
        mid)))
(define case-mid-down (->* (case-entries int) int)
  (lambda (es mid)
    (if (and (> mid 0) (= (case-key-at es mid) (case-key-at es (- mid 1))))
        (case-mid-down es (- mid 1))
        mid)))
(define case-mid (->* (case-entries int) int)
  (lambda (es n)
    (let ((up (case-mid-up es (quotient n 2) n)))
      (if (= up n) (case-mid-down es (quotient n 2)) up))))
;; Whether `key` names a `load-input`'s file.
(define input-key? (->* (string) bool)
  (lambda (k) (and (> (string-length k) 6) (string=? (substring k 0 6) "input:"))))
;; A program's parse begins with none.
(define shared-reset! (->* () unit)
  (lambda ()
    (begin (set shared-keys nil) (set shared-pending nil) (set loading-keys nil))))
;; The files being read, as `loading-keys` keeps them.
(define-type loading-list (listof (pairof string string rs) acyclic))
;; The chain from the load of `key` on, onto `acc`, as `parse.rs` says it:
;; `a` loads `b` …; "" if `key` is not being read.
(define load-chain (->* (loading-list string string) string)
  (lambda (ks key acc)
    (cond ((null? ks) "")
          ((string=? (car (car ks)) key)
           (string-append "a load cycle: `" (cdr (car ks)) acc))
          (else (load-chain (cdr ks) key
                            (string-append "` loads `" (cdr (car ks)) acc))))))
;; If `key` is being read, the cycle a load of it at `path` makes; else "".
(define load-cycle (->* (string string) string)
  (lambda (key path)
    (load-chain (get loading-keys) key (string-append "` loads `" path "`"))))
;; The definitions not yet placed, in order, now placed: none left.
(define shared-taken (->* () top-list)
  (lambda ()
    (letrec ((onto (subr (read @globals) (top-list top-list) top-list)
                (lambda (xs ys) (if (null? xs) ys (onto (cdr xs) (cons (car xs) ys))))))
      (let ((ts (get shared-pending))) (begin (set shared-pending nil) (onto ts nil))))))
(define shared-key? (->* (string (listof string acyclic)) bool)
  (lambda (k ks) (and (not (null? ks)) (or (string=? k (car ks)) (shared-key? k (cdr ks))))))

;; What was read for the `load-module` starting at `a`, in a list of one.
(define loaded-at (->* (loaded-files int) loaded-files)
  (lambda (fs a)
    (cond ((null? fs) nil)
          ((= (extract (car fs) 1) a) (the loaded-files (cons (car fs) nil)))
          (else (loaded-at (cdr fs) a)))))
;; The same, taking it from the front of `loaded-next` where it is there,
;; as it is when the driver read the files in the order they are parsed;
;; else found as `loaded-at` finds it.
(define loaded-next-at (->* (int) loaded-files)
  (lambda (a)
    (let ((next (get loaded-next)))
      (if (and (not (null? next)) (= (extract (car next) 1) a))
          (begin (set loaded-next (cdr next)) (the loaded-files (cons (car next) nil)))
          (loaded-at (get loaded) a)))))
;; The file read at `base`, in a list of one.
(define loaded-based (->* (loaded-files int) loaded-files)
  (lambda (fs base)
    (cond ((null? fs) nil)
          ((and (> base 0) (= (extract (car fs) 2) base)) (the loaded-files (cons (car fs) nil)))
          (else (loaded-based (cdr fs) base)))))

;; Where position `at` of `text` is: `line:column`, each from 1.
(define text-place (->* (string int) string)
  (lambda (text at)
    (letrec ((go (subr (maxeff (read @globals) spin) (int int int) string)
               (lambda (i line col)
                 (cond ((or (>= i at) (>= i (string-length text)))
                        (string-append (int->string line) ":" (int->string col)))
                       ((char=? (string-ref text i) #\newline) (go (+ i 1) (+ line 1) 1))
                       (else (go (+ i 1) line (+ col 1)))))))
      (go 0 1 1))))
;; What an error `m` at `at`, in the file read at `base` (`fs`), says where
;; the `load-module` is: the file, and where in it. As it is, if `at` is
;; not in that file.
(define in-loaded
  (->* (loaded-files int string int) string)
  (lambda (fs base m at)
    (let ((f (loaded-based fs base)))
      (if (or (null? f) (< at base) (>= at (+ base load-base)))
          m
          (let ((path (extract (car f) 4)) (text (extract (car f) 6)))
            (string-append "in `" path "`, "
                           (text-place text (- at base)) ": " m))))))

;; Error `m` at `at`, said in each file on the way out to the program
;; (`TODO.md` §73): while `at` is in a file read (past `load-base`), `in
;; `path`, line:col: m`, at where that file is first loaded (in a file read
;; before it, so this ends, a load cycle too); and where it is then. As
;; Rust's `Checker::in_loaded`.
(define loaded-placed
  (->* (loaded-files string int) (tupof (1 string) (2 int)))
  (lambda (fs m at)
    (let ((f (if (< at load-base) nil (loaded-first fs (* load-base (quotient at load-base)) nil))))
      (if (null? f)
          (tup (1 m) (2 at))
          (let* ((base (extract (car f) 2))
                 (where (text-place (extract (car f) 6) (- at base))))
            (loaded-placed
             fs (string-append "in `" (extract (car f) 4) "`, " where ": " m)
             (extract (car f) 1)))))))

;; The file read at `base`, as it was first loaded, in a list of one: the
;; last of `fs`, newest first (`loaded-files!`).
(define loaded-first
  (->* (loaded-files int loaded-files) loaded-files)
  (lambda (fs base found)
    (cond ((null? fs) found)
          ((= (extract (car fs) 2) base)
           (loaded-first (cdr fs) base (the loaded-files (cons (car fs) nil))))
          (else (loaded-first (cdr fs) base found)))))

;; The same, the file named `path`, as the load being read wrote it: a
;; file read once may be loaded under more than one path (`TODO.md` §71).
(define in-loaded-as
  (->* (loaded-files int string string int) string)
  (lambda (fs base path m at)
    (let ((f (loaded-based fs base)))
      (if (or (null? f) (< at base) (>= at (+ base load-base)))
          m
          (string-append "in `" path "`, "
                         (text-place (extract (car f) 6) (- at base)) ": " m)))))

;; The items of a form that is a module.
(define module-items-of (->* (top) mod-items)
  (lambda (t)
    (tagcase t
      (t-exp (x) (tagcase x (e-module (items a b abk) items) (else y nil)))
      (else y nil))))
;; A module's item that says it was read from a file: its base, its path,
;; and its parameters' binders (`loaded-params`), which it sees.
(define loaded-mark (->* (int string syns-a) mod-item)
  (lambda (base path ps)
    (let ((bs (if (null? ps) (the syns-a nil) (syn-items (car ps) "`((name kind) …)`"))))
      (mod-item-of base (string->symbol path) bs nil))))
;; A module's item that says reading its file failed, and why: refused where
;; the module is checked, as the Rust checker refuses it where it parses
;; the form.
(define loaded-error (->* (string) mod-items)
  (lambda (m) (cons (mod-item-of -1 (string->symbol m) (the syns-a nil) nil) nil)))

;; A module's file's parameters, if its first form is `(module-parameters
;; ((name kind) …))`, in a list of one; none if not.
(define loaded-params (->* (syns-a) syns-a)
  (lambda (forms)
    (if (and (not (null? forms)) (form-of? (car forms) 'module-parameters))
        (let ((items (syn-items (car forms) "`(module-parameters ((name kind) …))`")))
          (begin (arity items 2 "`(module-parameters ((name kind) …))`"
                        (syn-start (car forms)) (syn-end (car forms)))
                 (the syns-a (cons (nth items 1) nil))))
        nil)))
;; Module `m` read from a file of parameters `ps` (`loaded-params`), whose
;; `module-parameters` form is at `a`..`b`: a `plambda` over them of a
;; `lambda` of none making it, both there, so that whoever loads it gives
;; them, and each call makes one. `m`, if none.
(define loaded-made (->* (syns-a exp int int) exp)
  (lambda (ps m a b)
    (cond ((null? ps) m)
          ;; `(module-parameters ())`: a `lambda` of none, no `plambda` of none.
          ((syn-nil? (car ps)) (e-lambda (the param-list nil) m a b 0))
          (else (e-plambda (car ps) (e-lambda (the param-list nil) m a b 0) a b 0)))))
