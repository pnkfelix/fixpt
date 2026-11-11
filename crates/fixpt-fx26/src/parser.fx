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
(import parser-types e-var e-int e-bool e-str e-char e-float e-sym e-quote e-unit e-lambda e-app
        e-plambda e-proj e-if e-letrec e-let e-begin e-prompt e-letregion e-rlambda e-the
        e-convention e-bloblet e-product e-extract e-sum e-tagcase e-module e-with rl-none
        rl-unknown rl-names sh-module sh-fun t-define
        t-define-rec t-define-type t-define-effect t-define-convention t-define-syscall
        t-define-generative t-exp p-ok p-err
        (type syns-a names relied shape shapes members exp top exp-list param-list letrec-list
              let-list arm-list top-list
              mod-item mod-items presult loaded-file loaded-files) (effect tree-builds parses))

;; Each expression's identity (`parser-ids.fx`): its walk, made once for
;; the parser, so that its count is one (`walked-total`); the checker reads
;; again what it checks again (`read-again`, `k-rerun`).
(define parser-ids-module ((proj (load-module "fx26:parser-ids.fx") rs re rm rc rp)))
(define read-again (with parser-ids-module read-again))

(define parse-tag (prompt-tag presult presult (maxeff tree-builds (write rs) spin) rp)
  (make-continuation-prompt-tag))

;;; -------------------------------------------------------- looking at syn

(define syn-start (->* (syn) int)
  (lambda (s)
    (tagcase s
      (atom (d a b x) a) (lst (i d a b x) a) (dotted (i t d a b x) a) (vec (i d a b x) a))))
(define syn-end (->* (syn) int)
  (lambda (s)
    (tagcase s
      (atom (d a b x) b) (lst (i d a b x) b) (dotted (i t d a b x) b) (vec (i d a b x) b))))
;; The expansion that made `s`, 0 if none did.
(define syn-expansion (->* (syn) int)
  (lambda (s)
    (tagcase s
      (atom (d a b x) x) (lst (i d a b x) x) (dotted (i t d a b x) x) (vec (i d a b x) x))))

(define pfail (->* (string syn) void)
  (lambda (message s)
    (abort-current-continuation parse-tag (p-err message (syn-start s) (syn-end s)))))
(define pfail-at (->* (string int int) void)
  (lambda (message a b) (abort-current-continuation parse-tag (p-err message a b))))

(define syn-symbol? (->* (syn) bool)
  (lambda (s) (tagcase s (atom (d a b xpn) (symbol? d)) (else x #f))))
(define syn-name (->* (syn) string)
  (lambda (s)
    (tagcase s
      (atom (d a b xpn) (if (symbol? d) (symbol->string d) ""))
      (else x ""))))
;; A form's head as a symbol, to compare with the keywords: any that is
;; not a name is taken as `()`, which is none of them.
(define syn-head (->* (syn) symbol)
  (lambda (s)
    (tagcase s
      (atom (d a b xpn) (if (symbol? d) d '|()|))
      (else x '|()|))))
(define syn-symbol (->* (syn) symbol)
  (lambda (s) (if (syn-symbol? s) (syn-head s) (pfail "a name" s))))
;; `#t`, `#f` and `#u` as the FX-26 reader gives them: symbols.
(define sym-true symbol (string->symbol "#t"))
(define sym-false symbol (string->symbol "#f"))
(define sym-unit symbol (string->symbol "#u"))
;; `()`, which reads as an empty list.
(define syn-nil? (->* (syn) bool)
  (lambda (s) (tagcase s (lst (items d a b xpn) (null? items)) (else x #f))))
;; A proper list's items; `what`, when it is not one.
(define syn-items (->* (syn string) syns-a)
  (lambda (s what)
    (tagcase s
      (lst (items d a b xpn) items)
      (else x (pfail (string-append what ": expected a list") s)))))
(define syn-int (->* (syn) int)
  (lambda (s) (tagcase s (atom (d a b xpn) (if (datum-int? d) d -1)) (else x -1))))

(define len (->* (syns-a) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (len (cdr xs))))))
(define nth (->* (syns-a int) syn)
  (lambda (xs i) (if (= i 0) (car xs) (nth (cdr xs) (- i 1)))))
(define drop (->* (syns-a int) syns-a)
  (lambda (xs i) (if (= i 0) xs (drop (cdr xs) (- i 1)))))

;; A label or tag: a keyword, `#:name`, or the name bare, the same label;
;; or a natural number, which is its digits (as `parse.rs`'s `label`). A
;; procedural macro's alias is its name: a label binds nothing (`TODO.md`
;; §228).
(define label (->* (syn) symbol)
  (lambda (s)
    (cond ((syn-symbol? s) (string->symbol (label-name (symbol->string (syn-head s)))))
          ((>= (syn-int s) 0) (string->symbol (int->string (syn-int s))))
          (else
           (tagcase s
             (atom (d a b xpn)
               (if (keyword? d) (keyword->symbol d) (pfail label-usage s)))
             (else x (pfail label-usage s)))))))
(define label-usage string "a label is a keyword, a name or a natural number")
;; Name `n`, a procedural macro's alias `%~N:x` its name `x`.
(define label-name (->* (string) string)
  (lambda (n)
    (let ((c (if (and (> (string-length n) 2) (string=? (substring n 0 2) "%~"))
                 (label-digits-end n 2)
                 -1)))
      (if (and (> c 2) (< c (string-length n)) (char=? (string-ref n c) #\:))
          (label-name (substring n (+ c 1) (string-length n)))
          n))))
(define label-digits-end (->* (string int) int)
  (lambda (s i)
    (if (and (< i (string-length s)) (char-numeric? (string-ref s i)))
        (label-digits-end s (+ i 1))
        i)))


(define keep (->* (syns-a) syns-a)
  (lambda (xs) (if (null? xs) nil (cons (car xs) (keep (cdr xs))))))

;; `(tag x …)` with `n` items, or fail with `shape`.
(define arity (->* (syns-a int string int int) unit)
  (lambda (items n shape a b) (if (= (len items) n) #u (pfail-at shape a b))))
(define at-least (->* (syns-a int string int int) unit)
  (lambda (items n shape a b) (if (< (len items) n) (pfail-at shape a b) #u)))

(define mk-symbol (->* (string int int) syn)
  (lambda (n a b) (atom (string->symbol n) a b 0)))
(define syn-datums (->* (syns-a) (listof datum acyclic))
  (lambda (xs) (if (null? xs) nil (cons (syn->datum (car xs)) (syn-datums (cdr xs))))))
(define mk-list (->* (syns-a int int) syn)
  (lambda (items a b) (lst items (syn-datums items) a b 0)))
;; A parameter: `name`, or `(name type)`.
(define parse-param (->* (syn) (productof (1 symbol) (2 syns-a)))
  (lambda (p)
    (if (syn-symbol? p)
        (product (1 (syn-symbol p)) (2 (the syns-a nil)))
        (let ((pair (syn-items p "a parameter")))
          (if (= (len pair) 2)
              (product (1 (syn-symbol (car pair))) (2 (the syns-a (cons (nth pair 1) nil))))
              (pfail "a parameter is `name` or `(name type)`" p))))))
(define parse-params (->* (syn) param-list)
  (lambda (ps)
    (if (syn-nil? ps)
        nil
        (letrec ((each (subr (maxeff (read @globals) spin parses) (syns-a) param-list)
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
      (lst (items d a b xpn) (if (null? items) '|()| (syn-head (car items))))
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
(define stage-usage string
  (string-append "`(stage module effect type code (procedure body …) (failure else …) "
                 "(given g …))`, the last if any"))
;; A `vlambda`'s parameter: `xs`, or `(xs T)`, whose type is then
;; `(listof T acyclic)`.
(define parse-vparam (->* (syn int int) (productof (1 symbol) (2 syns-a)))
  (lambda (given a b)
    (if (syn-symbol? given)
        (product (1 (syn-symbol given)) (2 (the syns-a nil)))
        (let ((pair (syn-items given "a parameter")))
          (if (= (len pair) 2)
              (let ((ty (mk-listof-acyclic (nth pair 1) a b)))
                (product (1 (syn-symbol (car pair))) (2 (the syns-a (cons ty nil)))))
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
      (lst (xs d a2 b2 xpn)
        (if (and (symbol=? head 'letfreeze) (= (len xs) 2)) xs (the syns-a nil)))
      (else x (the syns-a nil)))))

;; A call `(f tmp more …)`, spanning `a`..`b`; and a `let`'s one binding.
;; `(with #%fx f)`: what an expansion calls, the standard binding, whatever
;; shadows or redefines `f` where it is (`TODO.md` §46).
(define standard-ref (->* (symbol int int) exp)
  (lambda (f a b) (e-with '#%fx (e-var f a b 0 0) a b 0 0 (rl-none))))
;; A name as an expression, spanning `a`..`b`: its variable; or, `n` being
;; `#%toplevel:x`, `(with #%toplevel x)`, the top level's `x` (`parse.rs`).
(define var-ref (->* (symbol int int) exp)
  (lambda (n a b)
    (let* ((s (symbol->string n)) (k (string-length s)))
      (if (and (> k 11) (string=? (substring s 0 11) "#%toplevel:"))
          (e-with '#%toplevel (e-var (string->symbol (substring s 11 k)) a b 0 0) a b 0 0 (rl-none))
          (e-var n a b 0 0)))))
;; Whether `items`' head is a keyword, `(#:t e …)`: a sum constructed.
(define kw-head? (->* (syns-a) bool)
  (lambda (items)
    (tagcase (car items) (atom (d a b x) (keyword? d)) (else y #f))))
;; `(#:t e …)` (`docs/research/datatype-macro.md`, "Keyword constructors:
;; decided"): `(sum #:t #u)` of none, `(sum #:t e)` of one, `(sum #:t
;; (tuple e …))` of more, as `parse.rs` rewrites it.
(define kw-sum (->* (syns-a int int) syn)
  (lambda (items a b)
    (let* ((args (cdr items))
           (payload (cond ((null? args) (mk-symbol "#u" a b))
                          ((null? (cdr args)) (car args))
                          (else (mk-list (cons (mk-symbol "tuple" a b) args) a b)))))
      (mk-list (list (mk-symbol "sum" a b) (car items) payload) a b))))
(define call-tmp (->* (symbol symbol exp-list int int) exp)
  (lambda (f tmp more a b)
    (e-app (standard-ref f a b) (the exp-list (cons (e-var tmp a b 0 0) more)) a b 0 0)))
(define one-let (->* (symbol exp) let-list)
  (lambda (name e) (the let-list (cons (product (1 name) (2 e)) nil))))

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
                     (e-app (e-var f a b 0 0) (the exp-list (cons x (the exp-list (cons y nil))))
                            a b 0 0)))
             (fixnum? (subr spin (int) bool)
                      (lambda (n) (and (<= n 1152921504606846975) (>= n -1152921504606846976))))
             ;; The limbs below the first fixnum, most significant first.
             (peel (subr (maxeff (read @globals) spin) (int (listof int acyclic)) exp)
                   (lambda (n limbs)
                     (if (fixnum? n)
                         (build (e-int n a b 0 0) limbs)
                         (peel (quotient n 1000000000) (cons (remainder n 1000000000) limbs)))))
             (build (subr (maxeff (read @globals) spin) (exp (listof int acyclic)) exp)
                    (lambda (acc limbs)
                      (if (null? limbs)
                          acc
                          (let ((scaled (call '* acc (e-int 1000000000 a b 0 0))))
                            (build (call '+ scaled (e-int (car limbs) a b 0 0)) (cdr limbs)))))))
      (cond ((fixnum? v) (e-int v a b 0 0))
            ((< v 0) (call '- (e-int 0 a b 0 0) (peel (- 0 v) nil)))
            (else (peel v nil))))))

;; Whether `s` is a string literal; and the string it is.
(define syn-string? (->* (syn) bool)
  (lambda (s) (tagcase s (atom (d a b xpn) (string? d)) (else x #f))))
(define syn-string (->* (syn) string)
  (lambda (s)
    (tagcase s (atom (d a b xpn) (if (string? d) d "")) (else x ""))))
;; `t` alone in a list.
(define one-syn (->* (syn) syns-a) (lambda (t) (cons t nil)))
;; A module's item, of one name.
(define mod-item-of (->* (int symbol syns-a exp-list) mod-item)
  (lambda (k name ts xs) (product (1 k) (2 (the names (cons name nil))) (3 ts) (4 xs))))
;; Whether a `define-type`'s head is `(d (p k) …)`: a name with parameters.
(define param-head? (->* (syn) bool)
  (lambda (head)
    (tagcase head
      (lst (xs d a b xpn) (and (not (null? xs)) (not (null? (cdr xs)))))
      (else x #f))))
;; `(define-type (d (p k) …) T)` in a module, at `a`..`b`: `(define-type d
;; (dlambda ((p k) …) T))`, what a `define-datatype` with parameters expands
;; to, in a `load-module`'s file too, as the Rust parser's `parse_module_in`.
(define param-desc-item (->* (int int syn syn) mod-item)
  (lambda (a b head t)
    (let* ((hs (tagcase head (lst (xs d a b xpn) xs) (else x (the syns-a nil))))
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
      (lst (xs d a b xpn) (and (not (null? xs)) (symbol=? (syn-head (car xs)) 'include)))
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
      (lst (xs d a b xpn)
        (if (and (not (null? xs)) (symbol=? (syn-head (car xs)) 'hide)) (cdr xs) nil))
      (else y nil))))
(define hide-form? (->* (syn) bool)
  (lambda (f)
    (tagcase f
      (lst (xs d a b xpn) (and (not (null? xs)) (symbol=? (syn-head (car xs)) 'hide)))
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
             (cons (product (1 9) (2 (the names (list '%hinclude))) (3 (extract it 3))
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
      (e-lambda (ps body la lb lalbk lalbkr)
                (e-lambda ps (e-with '%include body a b 0 0 (rl-none)) la lb lalbk lalbkr))
      (e-plambda (bs body la lb lalbk lalbkr)
                 (e-plambda bs (in-includes body a b) la lb lalbk lalbkr))
      (e-the (t e la lb lalbk lalbkr) (e-the t (in-includes e a b) la lb lalbk lalbkr))
      (e-rlambda (r l la lb lalbk lalbkr) (e-rlambda r (in-includes l a b) la lb lalbk lalbkr))
      (else y (e-with '%include x a b 0 0 (rl-none))))))
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
      (product (1 k) (2 (extract it 2)) (3 (extract it 3))
               (4 (cond ((= k 2) (inits-in-includes xs (one-syn f)))
                        ((= k 3) (tagcase f (lst (bs d a b xpn) (inits-in-includes xs (cdr bs)))
                                   (else y xs)))
                        (else xs)))))))
;; The included modules of `items`, from `%include-k` on: each with its
;; `include` form for its types, if the expander wrote what it relied on of
;; the module (`#:relied`), which the checker reads (`k-resolve-item`).
(define include-items (->* (mod-items int) mod-items)
  (lambda (items k)
    (cond ((null? items) nil)
          ((= (extract (car items) 1) 9)
           (cons (mod-item-of 2 (include-name (car (extract (car items) 2)) k)
                              (if (relied-form? (car (extract (car items) 3)))
                                  (extract (car items) 3)
                                  nil)
                              (extract (car items) 4))
                 (include-items (cdr items) (+ k 1))))
          (else (include-items (cdr items) k)))))
;; Whether `include` form `f` has what the expander relied on written in,
;; `(include m #:relied S)`.
(define relied-form? (->* (syn) bool)
  (lambda (f) (tagcase f (lst (xs d a b xpn) (= (len xs) 4)) (else y #f))))
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
                                             (syn-end (car f)) 0 0)))
                (own-items items))))))

;; `(lambda (x) x)`, spanning `a`..`b`: an abstract type's conversion.
(define identity-at (->* (int int) exp)
  (lambda (a b)
    (let ((x (product (1 'x) (2 (the syns-a nil)))))
      (e-lambda (the param-list (cons x nil)) (e-var 'x a b 0 0) a b 0 0))))
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
;;; from 1, `(define-type name (sumof (tag (productof (1 T) …)) …))`, and a
;;; constructor per tag, `(define tag (subr pure (T …) name) (lambda (%x1 …)
;;; (sum tag (product (1 %x1) …))))`. Where the form is: a program's, a
;;; module's, or a module file's, each parsing what it is made into.

(define datatype? (->* (syn) bool)
  (lambda (s) (form-of? s 'define-datatype)))

(define mk-int (->* (int int int) syn) (lambda (i a b) (atom i a b 0)))
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
;; A variant's tag: a name, or a keyword, `#:circle`, which is its name (the
;; same label, and the constructor `circle`, as `top.rs` reads it).
(define dt-tag (->* (syn) syn)
  (lambda (t)
    (tagcase t
      (atom (d a b xpn) (if (keyword? d) (atom (keyword->symbol d) a b 0) t))
      (else x t))))
;; Each variant's arm of the sum, `(tag (productof (1 T) …))`.
(define dt-arms (->* (syns-a int int) syns-a)
  (lambda (vs a b)
    (if (null? vs)
        nil
        (let* ((v (car vs)) (parts (syn-items v "a variant")))
          (if (or (null? parts) (not (syn-symbol? (dt-tag (car parts)))))
              (pfail "a variant is `(tag type …)` or `(#:tag type …)`" v)
              (let* ((prod (mk-form "productof" (dt-labelled (cdr parts) 1 a b) a b))
                     (arm (mk-list (list (dt-tag (car parts)) prod) a b))
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
               (tag (dt-tag (car parts)))
               (members (cdr parts))
               (mono (mk-pure-subr members used a b))
               (ty (if family? (mk-poly params mono a b) mono))
               (xs (dt-vars members 1 a b))
               (fields (mk-form "product" (dt-labelled xs 1 a b) a b))
               ;; At its variant: no two constructors' bodies at one place.
               (body (mk-form "sum" (list tag fields) (syn-start (car vs)) (syn-end (car vs))))
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
;; The type forms, as `parse.rs`'s `TYPE_FORMS`: no variant's tag (`TODO.md`
;; §190), as `(define-datatype var (oneof symbol pat))` would be one variant
;; `oneof`, not the type.
(define dt-type-forms (listof symbol acyclic)
  (list 'arrayof 'narrayof 'bloblet 'composable 'dletrec 'icell 'listof 'mark-key 'moduleof 'mu
        'nat 'nlist 'oneshot 'pairof 'place 'poly 'productof 'prompt-tag 'proves 'ref 'select 'subr
        'sumof 'tupleof 'bool 'oneof 'union 'anyof 'allof '-> '->* 'restrict 'modnames))
(define dt-in? (->* (symbol (listof symbol acyclic)) bool)
  (lambda (x xs) (and (not (null? xs)) (or (symbol=? x (car xs)) (dt-in? x (cdr xs))))))
;; #t, once no variant of `vs` has a type form's name for its tag.
(define dt-no-type-forms (->* (syns-a syn) bool)
  (lambda (vs name)
    (if (null? vs)
        #t
        (let* ((parts (syn-items (car vs) "a variant"))
               (tag (if (null? parts) (car vs) (dt-tag (car parts)))))
          (if (and (syn-symbol? tag) (dt-in? (syn-symbol tag) dt-type-forms))
              (let ((t (syn-name tag)))
                (pfail (string-append "`" t "` is a type form: this would be a variant named `" t
                                      "`, not the type; to name a type, write `(define-type "
                                      (syn-name name) " (" t " …))`")
                       (car vs)))
              (dt-no-type-forms (cdr vs) name))))))
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
                 (named (dt-no-type-forms (drop items 2) name))
                 (sum (mk-form "sumof" (dt-arms (drop items 2) a b) a b))
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
      (if (and (tagcase x
                 (atom (d c e x2) #f) (lst (items d c e x2) (not (null? items))) (else y #t))
               (null? (unquoted x depth)))
          (mk-form "the" (list (mk-symbol "datum" a b) built) a b)
          built))))
;; `(%datum x)`: list or vector `x` as a constant (`parse-exp`'s, as
;; `Checker::datum_node`).
(define datum-node (->* (syn) syn)
  (lambda (x) (mk-form "%datum" (list x) (syn-start x) (syn-end x))))
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
      (lst (items d a b xpn)
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
           (lst (items d a b xpn) (items-free? items depth (quasi-inner items depth)))
           (dotted (items tail d a b xpn)
             (and (items-free? items depth (quasi-inner items depth)) (unquote-free? tail depth)))
           (vec (items d a b xpn) (items-free? items depth depth))
           (else y #t)))))
;; Whether each of `items`, the first at `depth` and the rest at `inner`, is
;; neither spliced nor reached by an `unquote`.
(define items-free? (->* (syns-a int int) bool)
  (lambda (items depth inner)
    (or (null? items)
        (and (null? (if (= depth 1) (unquote-of (car items) "unquote-splicing") nil))
             (unquote-free? (car items) depth)
             (items-free? (cdr items) inner inner)))))
;; What builds `x`: a list or vector a quote makes, or no unquote of a
;; quasiquote reaches, a constant (`%datum`), as `Checker::quoted_in`.
(define quoted-in (->* (syn int) syn)
  (lambda (x depth)
    (let ((u (unquoted x depth)) (a (syn-start x)) (b (syn-end x)))
      (cond
        ((not (null? u)) (car u))
        ((and (tagcase x (atom (d c e xpn) #f) (lst (items d c e xpn) (not (null? items)))
                (else y #t))
              (or (< depth 0) (unquote-free? x depth)))
         (datum-node x))
        (else
          (tagcase x
            (atom (d c e xpn)
              (cond ((not (symbol? d))
                     (if (bytevector? d) (pfail "a bytevector cannot be quoted yet" x) x))
                    ((or (symbol=? d sym-true) (symbol=? d sym-false)) x)
                    (else (mk-form "quote" (list x) a b))))
            (lst (items d c e xpn)
              (if (null? items)
                  (mk-symbol "nil" a b)
                  (quoted-items items #f (car items) depth a b)))
            (dotted (items tail d c e xpn) (quoted-items items #t tail depth a b))
            (vec (items d c e xpn)
              (if (null? items)
                  (fx-call "datum-list->vector" (list (fx-named "nil" a b)) a b)
                  (fx-call "datum-list->vector"
                           (list (quoted-items items #f (car items) depth a b)) a b)))))))))
;; A list of `items`, then, if `dotted?`, `tail` (else `nil`), built.
(define quoted-items (->* (syns-a bool syn int int int) syn)
  (lambda (items dotted? tail depth a b)
    (let ((inner (quasi-inner items depth)))
      (quoted-onto items dotted? tail depth
                   (and (>= depth 1) (or (not dotted?) (unquote-free? tail depth)))
                   depth inner #t a b))))
;; `items`, then, if `dotted?`, `tail`: a list, from the first of `items` to
;; `b`.
(define rest-list (->* (syns-a bool syn int) syn)
  (lambda (items dotted? tail b)
    (let ((a (syn-start (car items))))
      (if dotted?
          (dotted items tail (datum-dotted (syn-datums items) (syn->datum tail)) a b 0)
          (mk-list items a b)))))
;; `items` onto the list's end, the first at `depth` and the rest at
;; `inner`: under a quasiquote (`free-tail?` its tail no unquote reaches),
;; the items after the first that no unquote reaches, with the tail, one
;; constant. As `Checker::quoted_in`.
(define quoted-onto (->* (syns-a bool syn int bool int int bool int int) syn)
  (lambda (items dotted? tail ldepth free-tail? depth inner first? a b)
    (cond
      ((null? items) (if dotted? (quoted-in tail ldepth) (fx-named "nil" a b)))
      ((and free-tail? (not first?) (items-free? items inner inner))
       (datum-node (rest-list items dotted? tail b)))
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

;; The files a program loads, the `include`s it makes and the loads it
;; shares (`parser-loads.fx`), at these regions, and all it defines, given
;; on.
(define loads-module ((proj (load-module "fx26:parser-loads.fx") rs re rm rc rp)))
(import loads-module loaded loaded-next loaded-files! includes-given includes-given!
        include-given-at loaded-onto load-base shared-keys shared-pending loading-keys input-key?
        shared-reset! load-chain load-cycle shared-taken shared-key? loaded-at loaded-next-at
        loaded-based text-place in-loaded loaded-placed loaded-first in-loaded-as module-items-of
        (type include-given includes loading-list))


;; A `case`'s data by halving (`TODO.md` §46): each datum's test, the
;; value it sorts by, and its clause.
(define-type case-entry (productof (1 exp) (2 int) (3 int)))
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
          ((syn-nil? (car ps)) (e-lambda (the param-list nil) m a b 0 0))
          (else (e-plambda (car ps) (e-lambda (the param-list nil) m a b 0 0) a b 0 0)))))
;; A module file's forms without its macros, `define-syntax`es (hidden
;; or not), which are no items: what `import-with-syntax` brings (the Rust
;; checker's `read_module_file`). Each use of one after it is expanded
;; already (`parser-top.fx`'s `loaded-own-expanded!`): one left is used
;; before its file defines it, and refused.
(define without-syntax (->* (syns-a) syns-a)
  (lambda (forms)
    (letrec ((names-of (subr (maxeff (read @globals) spin parses)
                             (syns-a (listof symbol acyclic))
                             (listof symbol acyclic))
               (lambda (xs out)
                 (cond ((null? xs) out)
                       ((syntax-form-of? (car xs) 'define-syntax)
                        (names-of (cdr xs) (cons (syn-head (nth (syn-items (car xs) "") 1)) out)))
                       ((syntax-form-of? (car xs) 'define-syntax-rec)
                        (names-of (cdr xs)
                                  (append (member-heads (cdr (syn-items (car xs) ""))) out)))
                       ((syntax-form-of? (car xs) 'hide)
                        (names-of (cdr xs) (names-of (cdr (syn-items (car xs) "")) out)))
                       (else (names-of (cdr xs) out)))))
             (kept (subr (maxeff (read @globals) spin parses) (syns-a) syns-a)
               (lambda (xs)
                 (cond ((null? xs) nil)
                       ((or (syntax-form-of? (car xs) 'define-syntax)
                            (syntax-form-of? (car xs) 'define-syntax-rec))
                        (kept (cdr xs)))
                       ((syntax-form-of? (car xs) 'hide)
                        (let ((items (kept (cdr (syn-items (car xs) "")))))
                          (if (null? items)
                              (kept (cdr xs))
                              (cons (mk-list (cons (car (syn-items (car xs) "")) items)
                                             (syn-start (car xs)) (syn-end (car xs)))
                                    (kept (cdr xs))))))
                       (else (cons (car xs) (kept (cdr xs)))))))
             (used (subr (maxeff (read @globals) spin parses) (syns-a (listof symbol acyclic)) unit)
               (lambda (xs ms)
                 (if (null? xs)
                     #u
                     (begin
                       (tagcase (car xs)
                         (lst (items d a b xpn)
                           (begin
                             (if (and (not (null? items)) (name-in? (syn-head (car items)) ms))
                                 (pfail (string-append
                                         "`" (symbol->string (syn-head (car items)))
                                         "` is a macro of this file used before the file "
                                         "defines it")
                                        (car xs))
                                 #u)
                             (used items ms)))
                         (else y #u))
                       (used (cdr xs) ms))))))
      (let ((ms (names-of forms nil)))
        (if (null? ms) forms (let ((k (kept forms))) (begin (used k ms) k)))))))
(define name-in? (->* (symbol (listof symbol acyclic)) bool)
  (lambda (n ns) (and (not (null? ns)) (or (symbol=? n (car ns)) (name-in? n (cdr ns))))))
;; The names a `define-syntax-rec`'s members `ms` define.
(define member-heads (->* (syns-a) (listof symbol acyclic))
  (lambda (ms)
    (if (null? ms)
        nil
        (tagcase (car ms)
          (lst (items d a b xpn)
            (if (null? items)
                (member-heads (cdr ms))
                (cons (syn-head (car items)) (member-heads (cdr ms)))))
          (else y (member-heads (cdr ms)))))))
;; Whether `s` is a form of `keyword`.
(define syntax-form-of? (->* (syn symbol) bool)
  (lambda (s keyword)
    (tagcase s
      (lst (items d a b xpn) (and (not (null? items)) (symbol=? (syn-head (car items)) keyword)))
      (else y #f))))
