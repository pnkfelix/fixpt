;;; The FX-26 parser, in FX-26 (PLAN.md §11, step 9a).
;;;
;;; What the eager reader read (`syn`, with positions) to an abstract syntax
;;; tree, with the Rust parser's desugarings (`crates/fixpt-fx26/src/parse.rs`),
;;; node for node and span for span, so the two can be compared. Descriptions
;;; (types, effects, regions, binders) are kept as the syntax they were
;;; written in: the evaluator and the compiler do not need them, and the
;;; checker written in FX-26 (`check-*.fx`) reads them itself.
;;;
;;; Compiled with the reader, as one program: `syn` is in the reader's region
;;; @s, which only this program can name. The trees are `acyclic`: made by
;;; `cons` straight into the frozen region, never written, so a walk of one
;;; ends (`docs/fx26.md`, "Well-founded recursion"). A parse
;;; that fails aborts to a prompt in @p; both are this program's own, so
;;; `parse-program` is licensed as the reader's entry points are.

(private-regions @p)

;; What a parse may do: read what was read and build a tree
;; (`tree-builds`), and give up.
(define-effect tree-builds (maxeff (read @globals) (read @s) (alloc @s)))
(define-effect parses (maxeff tree-builds (goto @p)))

(define-type syns-a (listof syn acyclic))
(define-type names (listof symbol acyclic))

;;; ------------------------------------------------------------------ trees
;;; Each node ends with where it starts and ends. A list of none or one
;;; stands for something optional: a parameter's type, a tagcase's `else`.

(define-datatype exp
  (e-var symbol int int)
  (e-int int int int)
  (e-bool bool int int)
  (e-str string int int)
  (e-char char int int)
  (e-float f64 int int)
  (e-sym symbol int int)
  (e-unit int int)
  (e-lambda (listof (productof (1 symbol) (2 syns-a)) acyclic) exp int int)
  (e-app exp (listof exp acyclic) int int)
  (e-plambda syn exp int int)
  (e-proj exp syns-a int int)
  (e-if exp exp exp int int)
  (e-letrec (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) exp int int)
  (e-let (listof (productof (1 symbol) (2 exp)) acyclic) exp int int)
  (e-begin (listof exp acyclic) int int)
  (e-prompt exp exp exp int int)
  ;; `(letregion name body …)`, `(letrena name body …)` or `(letreap name
  ;; body …)`, or `(letfreeze name body …)`: what it makes besides the
  ;; region (0 nothing, 1 an arena, 2 a reap, 3 nothing, its region's data
  ;; frozen as it ends: `docs/research/places-and-regions.md`),
  ;; the region variable's name, the place a `letfreeze` freezes into
  ;; (`heap` unless given), and the body.
  (e-letregion int symbol symbol exp int int)
  ;; `(rlambda region (param …) body …)`: the region, and the `lambda`.
  (e-rlambda exp exp int int)
  (e-the syn exp int int)
  ;; `(convention C expression)`: the procedure converted to `C`.
  (e-convention syn exp int int)
  ;; A bloblet form, by name, with its field index, or -1.
  (e-bloblet symbol int (listof exp acyclic) int int)
  (e-product (listof (productof (1 symbol) (2 exp)) acyclic) int int)
  (e-extract exp symbol int int)
  (e-sum symbol exp int int)
  ;; Arms: the tag, whether it takes a product apart, the names, the body.
  (e-tagcase exp (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic)
             (listof (productof (1 symbol) (2 exp)) acyclic) int int)
  ;; `(module item …)` (`docs/research/first-class-modules.md`): each item
  ;; what it is (0 `define-generative`, 1 `define-type`, 2 `define`, 3
  ;; `define-rec`), the names it defines, their types (a `define`'s, none or
  ;; one), and its expressions: the values, or an abstract type's two
  ;; conversions, each `(lambda (x) x)` spanning the item.
  (e-module (listof (productof (1 int) (2 names) (3 syns-a) (4 (listof exp acyclic))) acyclic)
            int int)
  ;; `(with module body …)`: the body, with the module's values in scope.
  (e-with symbol exp int int))

;; A top-level form. A definition's type is a list of none or one; a
;; `define*`'s, of it and the `define*`.
(define-datatype top
  (t-define symbol syns-a exp int int)
  ;; `(define-rec (name type lambda) …)`: a top-level `letrec`.
  (t-define-rec (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) int int)
  (t-define-type syn syn int int)
  (t-define-effect syn syn int int)
  ;; `(define-generative head rep)`: read by the checker alone; its two
  ;; conversions follow it as definitions.
  (t-define-generative syn syn int int)
  (t-private-regions syns-a int int)
  (t-exp exp))

;; The trees' lists: of expressions, a `lambda`'s parameters, a `letrec`'s
;; and a `let`'s bindings, a `tagcase`'s arms, and top-level forms.
(define-type exp-list (listof exp acyclic))
(define-type param-list (listof (productof (1 symbol) (2 syns-a)) acyclic))
(define-type letrec-list (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic))
(define-type let-list (listof (productof (1 symbol) (2 exp)) acyclic))
(define-type arm-list (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic))
(define-type top-list (listof top acyclic))
(define-type mod-item (productof (1 int) (2 names) (3 syns-a) (4 exp-list)))
(define-type mod-items (listof mod-item acyclic))

(define-datatype presult (p-ok (listof top acyclic)) (p-err string int int))

(define parse-tag (prompt-tag presult presult (maxeff tree-builds spin) @p)
  (make-continuation-prompt-tag))

;;; -------------------------------------------------------- looking at syn

(define syn-start (subr pure (syn) int)
  (lambda (s)
    (tagcase s (atom (d a b) a) (lst (i d a b) a) (dotted (i t d a b) a) (vec (i d a b) a))))
(define syn-end (subr pure (syn) int)
  (lambda (s)
    (tagcase s (atom (d a b) b) (lst (i d a b) b) (dotted (i t d a b) b) (vec (i d a b) b))))

(define pfail (subr parses (string syn) void)
  (lambda (message s)
    (abort-current-continuation parse-tag (p-err message (syn-start s) (syn-end s)))))
(define pfail-at (subr parses (string int int) void)
  (lambda (message a b) (abort-current-continuation parse-tag (p-err message a b))))

(define syn-symbol? (subr pure (syn) bool)
  (lambda (s) (tagcase s (atom (d a b) (datum-symbol? d)) (else x #f))))
(define syn-name (subr pure (syn) string)
  (lambda (s)
    (tagcase s
      (atom (d a b) (if (datum-symbol? d) (datum-symbol-name d) ""))
      (else x ""))))
;; A form's head as a symbol, to compare with the keywords: any that is
;; not a name is taken as `()`, which is none of them.
(define syn-head (subr pure (syn) symbol)
  (lambda (s)
    (tagcase s
      (atom (d a b) (if (datum-symbol? d) (datum->symbol d) '|()|))
      (else x '|()|))))
(define syn-symbol (subr parses (syn) symbol)
  (lambda (s) (if (syn-symbol? s) (syn-head s) (pfail "a name" s))))
;; `#t`, `#f` and `#u` as the FX-26 reader gives them: symbols.
(define sym-true symbol (string->symbol "#t"))
(define sym-false symbol (string->symbol "#f"))
(define sym-unit symbol (string->symbol "#u"))
;; `()`, which reads as an empty list.
(define syn-nil? (subr (read @s) (syn) bool)
  (lambda (s) (tagcase s (lst (items d a b) (null? items)) (else x #f))))
;; A proper list's items; `what`, when it is not one.
(define syn-items (subr parses (syn string) syns-a)
  (lambda (s what)
    (tagcase s
      (lst (items d a b) items)
      (else x (pfail (string-append what ": expected a list") s)))))
(define syn-int (subr pure (syn) int)
  (lambda (s) (tagcase s (atom (d a b) (if (datum-int? d) (datum-int-value d) -1)) (else x -1))))

(define len (subr (maxeff (read @globals) (read @s)) (syns-a) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (len (cdr xs))))))
(define nth (subr parses (syns-a int) syn)
  (lambda (xs i) (if (= i 0) (car xs) (nth (cdr xs) (- i 1)))))
(define drop (subr (maxeff (read @globals) (read @s)) (syns-a int) syns-a)
  (lambda (xs i) (if (= i 0) xs (drop (cdr xs) (- i 1)))))

;; A label or tag: a name, or a positive integer, which is its digits.
(define label (subr parses (syn) symbol)
  (lambda (s)
    (cond ((syn-symbol? s) (syn-head s))
          ((> (syn-int s) 0) (string->symbol (int->string (syn-int s))))
          (else (pfail "a label is a name or a positive integer" s)))))

(define keep (subr (maxeff (read @globals) (read @s)) (syns-a) syns-a)
  (lambda (xs) (if (null? xs) nil (cons (car xs) (keep (cdr xs))))))

;; `(tag x …)` with `n` items, or fail with `shape`.
(define arity (subr parses (syns-a int string int int) unit)
  (lambda (items n shape a b) (if (= (len items) n) #u (pfail-at shape a b))))
(define at-least (subr parses (syns-a int string int int) unit)
  (lambda (items n shape a b) (if (< (len items) n) (pfail-at shape a b) #u)))

(define mk-symbol (subr (read @globals) (string int int) syn)
  (lambda (n a b) (atom (datum-symbol n) a b)))
(define syn-datums (subr (maxeff (read @globals) (read @s)) (syns-a) (listof datum acyclic))
  (lambda (xs) (if (null? xs) nil (cons (syn->datum (car xs)) (syn-datums (cdr xs))))))
(define mk-list (subr (maxeff (read @globals) (read @s)) (syns-a int int) syn)
  (lambda (items a b) (lst items (datum-list (syn-datums items)) a b)))
;; A parameter: `name`, or `(name type)`.
(define parse-param (subr parses (syn) (productof (1 symbol) (2 syns-a)))
  (lambda (p)
    (if (syn-symbol? p)
        (product (1 (syn-symbol p)) (2 (the syns-a nil)))
        (let ((pair (syn-items p "a parameter")))
          (if (= (len pair) 2)
              (product (1 (syn-symbol (car pair))) (2 (the syns-a (cons (nth pair 1) nil))))
              (pfail "a parameter is `name` or `(name type)`" p))))))
(define parse-params (subr parses (syn) param-list)
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
(define field-index (subr parses (syn) int)
  (lambda (s)
    (if (>= (syn-int s) 0)
        (syn-int s)
        (pfail "a field index is a literal, non-negative integer" s))))

;; A form's head, as `syn-head` gives it: `()` if it is not a list, or is
;; empty.
(define form-head (subr (maxeff (read @globals) (read @s)) (syn) symbol)
  (lambda (s)
    (tagcase s
      (lst (items d a b) (if (null? items) '|()| (syn-head (car items))))
      (else x '|()|))))
;; Whether `s` is a form headed `keyword`.
(define form-of? (subr (maxeff (read @globals) (read @s)) (syn symbol) bool)
  (lambda (s keyword) (symbol=? (form-head s) keyword)))

(define arm-else? (subr (maxeff (read @globals) (read @s)) (syn) bool)
  (lambda (c) (form-of? c 'else)))

(define parse-names (subr parses (syns-a) names)
  (lambda (xs) (if (null? xs) nil (cons (syn-symbol (car xs)) (parse-names (cdr xs))))))

;; `(listof t acyclic)`, spanning `a`..`b`.
(define mk-listof-acyclic (subr (maxeff (read @globals) (read @s)) (syn int int) syn)
  (lambda (t a b)
    (let ((listof (mk-symbol "listof" a b)) (acyclic (mk-symbol "acyclic" a b)))
      (mk-list (list listof t acyclic) a b))))
(define vlambda-usage string "`(vlambda name body …)` or `(vlambda (name type) body …)`")
;; A `vlambda`'s parameter: `xs`, or `(xs T)`, whose type is then
;; `(listof T acyclic)`.
(define parse-vparam (subr parses (syn int int) (productof (1 symbol) (2 syns-a)))
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
(define region-form? (subr pure (symbol) bool)
  (lambda (head)
    (or (or (symbol=? head 'letregion) (symbol=? head 'letfreeze))
        (or (symbol=? head 'letrena) (symbol=? head 'letreap)))))
(define region-kind (subr pure (symbol) int)
  (lambda (head)
    (cond ((symbol=? head 'letregion) 0)
          ((symbol=? head 'letrena) 1)
          ((symbol=? head 'letreap) 2)
          (else 3))))
;; `(r p)`'s items, if a `letfreeze` binds that as `given`; else none.
(define freeze-pair (subr (maxeff (read @globals) (read @s)) (symbol syn) syns-a)
  (lambda (head given)
    (tagcase given
      (lst (xs d a2 b2) (if (and (symbol=? head 'letfreeze) (= (len xs) 2)) xs (the syns-a nil)))
      (else x (the syns-a nil)))))

;; A call `(f tmp more …)`, spanning `a`..`b`; and a `let`'s one binding.
(define call-tmp (subr tree-builds (symbol symbol exp-list int int) exp)
  (lambda (f tmp more a b) (e-app (e-var f a b) (the exp-list (cons (e-var tmp a b) more)) a b)))
(define one-let (subr (read @globals) (symbol exp) let-list)
  (lambda (name e) (the let-list (cons (product (1 name) (2 e)) nil))))

;; Whether `head` is a bloblet form's; and whether `op` with `n` arguments
;; is one that takes no field index, with the right number.
(define bloblet-form? (subr pure (symbol) bool)
  (lambda (head)
    (or (symbol=? head 'make-bloblet) (symbol=? head 'rmake-bloblet) (symbol=? head 'bloblet-ref)
        (symbol=? head 'bloblet-set!) (symbol=? head 'bloblet-freeze) (symbol=? head 'bloblet-byte)
        (symbol=? head 'bloblet-set-byte!) (symbol=? head 'bloblet-bytes))))
(define bloblet-untagged? (subr pure (symbol int) bool)
  (lambda (op n)
    (or (and (symbol=? op 'bloblet-freeze) (= n 1)) (and (symbol=? op 'bloblet-byte) (= n 2))
        (and (symbol=? op 'bloblet-set-byte!) (= n 3)) (and (symbol=? op 'bloblet-bytes) (= n 1)))))

;; A `confirm-length`'s length, `n`: a natural literal, or -1 for a
;; variable holding a `nat`.
(define confirm-length-k (subr parses (syn) int)
  (lambda (n)
    (cond ((>= (syn-int n) 0) (syn-int n))
          ((syn-symbol? n) -1)
          (else (pfail "a length is a natural number, or a variable holding one" n)))))
;; What a region form says when its name is not one, or has an `@`.
(define region-name-error (subr (read @globals) (symbol) string)
  (lambda (head)
    (str3 "a `" (symbol->string head) "` binds a region variable's name, without `@`")))

;; The names a `tagcase` arm binds, `bind`: a product's fields, `(name
;; …)`, if `fields`; else the one value's name.
(define arm-names (subr parses (bool syn) names)
  (lambda (fields bind)
    (if fields
        (parse-names (syn-items bind "the names an arm binds"))
        (the names (cons (syn-symbol bind) nil)))))
;; An integer literal past a fixnum, `v`, as arithmetic on fixnums, which
;; every path does, bignums included (PLAN.md Q2): `(- 0 x)` for a
;; negative; else, in base 10⁹, `(+ (* rest 1000000000) last)`, `rest`
;; again so until it is a fixnum. The Rust parser's `big_literal`, node for
;; node: here the limbs are peeled off, least first, then built outwards.
(define big-literal (subr (maxeff (read @globals) spin) (int int int) exp)
  (lambda (v a b)
    (letrec ((call (subr (maxeff (read @globals) spin) (symbol exp exp) exp)
                   (lambda (f x y)
                     (e-app (e-var f a b) (the exp-list (cons x (the exp-list (cons y nil)))) a b)))
             (fixnum? (subr spin (int) bool)
                      (lambda (n) (and (<= n 1152921504606846975) (>= n -1152921504606846976))))
             ;; The limbs below the first fixnum, most significant first.
             (peel (subr (maxeff (read @globals) spin) (int (listof int acyclic)) exp)
                   (lambda (n limbs)
                     (if (fixnum? n)
                         (build (e-int n a b) limbs)
                         (peel (quotient n 1000000000) (cons (remainder n 1000000000) limbs)))))
             (build (subr (maxeff (read @globals) spin) (exp (listof int acyclic)) exp)
                    (lambda (acc limbs)
                      (if (null? limbs)
                          acc
                          (let ((scaled (call '* acc (e-int 1000000000 a b))))
                            (build (call '+ scaled (e-int (car limbs) a b)) (cdr limbs)))))))
      (cond ((fixnum? v) (e-int v a b))
            ((< v 0) (call '- (e-int 0 a b) (peel (- 0 v) nil)))
            (else (peel v nil))))))

;; Whether `s` is a string literal; and the string it is.
(define syn-string? (subr pure (syn) bool)
  (lambda (s) (tagcase s (atom (d a b) (datum-string? d)) (else x #f))))
(define syn-string (subr pure (syn) string)
  (lambda (s)
    (tagcase s (atom (d a b) (if (datum-string? d) (datum-string-value d) "")) (else x ""))))
;; A `load-module`'s items, from the file it names, read where the form is
;; (`parser-load.fx`, which sets this).
(define parse-load-module (ref (subr (maxeff parses spin) (string int int) mod-items) @s)
  (new (lambda (path a b) (the mod-items nil))))
;; `t` alone in a list.
(define one-syn (subr (read @globals) (syn) syns-a) (lambda (t) (cons t nil)))
;; A module's item, of one name.
(define mod-item-of (subr (read @globals) (int symbol syns-a exp-list) mod-item)
  (lambda (k name ts xs) (product (1 k) (2 (the names (cons name nil))) (3 ts) (4 xs))))
;; Whether a `define-type`'s head is `(d (p k) …)`: a name with parameters.
(define param-head? (subr (maxeff (read @globals) (read @s)) (syn) bool)
  (lambda (head)
    (tagcase head
      (lst (xs d a b) (and (not (null? xs)) (not (null? (cdr xs)))))
      (else x #f))))
;; `(define-type (d (p k) …) T)` in a module, at `a`..`b`: `(define-type d
;; (dlambda ((p k) …) T))`, what a `define-datatype` with parameters expands
;; to, in a `load-module`'s file too, as the Rust parser's `parse_module_in`.
(define param-desc-item (subr parses (int int syn syn) mod-item)
  (lambda (a b head t)
    (let* ((hs (tagcase head (lst (xs d a b) xs) (else x (the syns-a nil))))
           (ha (syn-start head))
           (hb (syn-end head))
           (params (mk-list (cdr hs) ha hb))
           (fun (mk-list (list (mk-symbol "dlambda" ha hb) params t) a b)))
      (mod-item-of 1 (syn-symbol (car hs)) (one-syn fun) nil))))
;; `(lambda (x) x)`, spanning `a`..`b`: an abstract type's conversion.
(define identity-at (subr (read @globals) (int int) exp)
  (lambda (a b)
    (let ((x (product (1 'x) (2 (the syns-a nil)))))
      (e-lambda (the param-list (cons x nil)) (e-var 'x a b) a b))))
(define module-usage string
  (string-append "a module holds `(define-generative t T)`, `(define-type d T)`, "
                 (string-append "`(define-effect e E)`, `(define x [T] e)`, `(define* f T e)` and "
                                "`(define-rec (f T e) …)`")))
;; A `define-rec`'s names, types and expressions, each in order.
(define rec-names (subr (read @globals) (letrec-list) names)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 1) (rec-names (cdr bs))))))
(define rec-types (subr (read @globals) (letrec-list) syns-a)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 2) (rec-types (cdr bs))))))
(define rec-inits (subr (read @globals) (letrec-list) exp-list)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 3) (rec-inits (cdr bs))))))

;;; ------------------------------------------------------------ expressions

;;; FX-91's `(define-datatype name (tag type …) …)`, expanded as the Rust
;;; reader expands it (`top.rs`'s `expand_datatype`), as syntax, into the
;;; forms it stands for: a sum of products, each variant's members labelled
;;; from 1, `(define-type name (sumof (tag (productof (1 T) …)) …))`, and a
;;; constructor per tag, `(define tag (subr pure (T …) name) (lambda (%x1 …)
;;; (sum tag (product (1 %x1) …))))`. Where the form is: a program's, a
;;; module's, or a module file's, each parsing what it is made into.

(define datatype? (subr (maxeff (read @globals) (read @s)) (syn) bool)
  (lambda (s) (form-of? s 'define-datatype)))

(define mk-int (subr (read @globals) (int int int) syn) (lambda (i a b) (atom (datum-int i) a b)))
;; `(keyword item …)`; `(subr pure (member …) result)`; and `(poly (binder
;; …) body)`: each spanning `a`..`b`.
(define mk-form (subr (maxeff (read @globals) (read @s)) (string syns-a int int) syn)
  (lambda (keyword items a b) (mk-list (cons (mk-symbol keyword a b) items) a b)))
(define mk-pure-subr (subr (maxeff (read @globals) (read @s)) (syns-a syn int int) syn)
  (lambda (members result a b)
    (let ((pure (mk-symbol "pure" a b)) (args (mk-list members a b)))
      (mk-form "subr" (list pure args result) a b))))
(define mk-poly (subr (maxeff (read @globals) (read @s)) (syns-a syn int int) syn)
  (lambda (binders body a b)
    (mk-form "poly" (list (mk-list binders a b) body) a b)))
;; A constructor's parameters, `%x1 …`, from `i`.
(define dt-vars (subr (maxeff (read @globals) (read @s) (alloc @s)) (syns-a int int int) syns-a)
  (lambda (ms i a b)
    (if (null? ms)
        nil
        (let ((x (mk-symbol (string-append "%x" (int->string i)) a b)))
          (cons x (dt-vars (cdr ms) (+ i 1) a b))))))
;; `(1 m1) (2 m2) …`, from `i`.
(define dt-labelled (subr (maxeff (read @globals) (read @s) (alloc @s)) (syns-a int int int) syns-a)
  (lambda (ms i a b)
    (if (null? ms)
        nil
        (let* ((pair (mk-list (list (mk-int i a b) (car ms)) a b))
               (rest (dt-labelled (cdr ms) (+ i 1) a b)))
          (cons pair rest)))))
;; Each variant's arm of the sum, `(tag (productof (1 T) …))`.
(define dt-arms (subr parses (syns-a int int) syns-a)
  (lambda (vs a b)
    (if (null? vs)
        nil
        (let* ((v (car vs)) (parts (syn-items v "a variant")))
          (if (or (null? parts) (not (syn-symbol? (car parts))))
              (pfail "a variant is `(tag type …)`" v)
              (let* ((prod (mk-form "productof" (dt-labelled (cdr parts) 1 a b) a b))
                     (arm (mk-list (list (car parts) prod) a b))
                     (rest (dt-arms (cdr vs) a b)))
                (cons arm rest)))))))
;; Each constructor: of type `(subr pure (member …) used)`, where `used` is
;; the type as it is used, `name` or `(name param …)`; polymorphic in the
;; parameters if there are any (`family?`).
(define dt-constructors (subr parses (syn bool syns-a syns-a int int) syns-a)
  (lambda (used family? params vs a b)
    (if (null? vs)
        nil
        (let* ((parts (syn-items (car vs) "a variant"))
               (tag (car parts))
               (members (cdr parts))
               (mono (mk-pure-subr members used a b))
               (ty (if family? (mk-poly params mono a b) mono))
               (xs (dt-vars members 1 a b))
               (fields (mk-form "product" (dt-labelled xs 1 a b) a b))
               (body (mk-form "sum" (list tag fields) a b))
               (make (mk-form "lambda" (list (mk-list xs a b) body) a b))
               (ctor (mk-form "define" (list tag ty make) a b))
               (rest (dt-constructors used family? params (cdr vs) a b)))
          (cons ctor rest)))))
;; The parameters' names, from `(name kind) …`.
(define dt-param-names (subr parses (syns-a) syns-a)
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
(define expand-datatype (subr parses (syn) syns-a)
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
                 (sum (mk-form "sumof" (dt-arms (drop items 2) a b) a b))
                 (ctors (dt-constructors used family? params (drop items 2) a b)))
            (cons (mk-form "define-type" (list head sum) a b) ctors))))))

(define-rec
  (parse-exps (subr (maxeff parses spin) (syns-a) exp-list)
    (lambda (xs) (if (null? xs) nil (cons (parse-exp (car xs)) (parse-exps (cdr xs))))))
  ;; One or more expressions, an implicit `begin` spanning `a`..`b`.
  (parse-body (subr (maxeff parses spin) (syns-a int int) exp)
    (lambda (forms a b)
      (cond ((null? forms) (pfail-at "an empty body" a b))
            ((null? (cdr forms)) (parse-exp (car forms)))
            (else (e-begin (parse-exps forms) a b)))))
  (parse-exp (subr (maxeff parses spin) (syn) exp)
    (lambda (s)
      (tagcase s
        (atom (d a b)
          (cond ((datum-int? d) (e-int (datum-int-value d) a b))
                ((datum-integer? d) (big-literal (datum-int-value d) a b))
                ((datum-string? d) (e-str (datum-string-value d) a b))
                ((datum-bool? d) (e-bool (datum-bool-value d) a b))
                ((datum-char? d) (e-char (datum-char-value d) a b))
                ((datum-f64? d) (e-float (datum-f64-value d) a b))
                ((datum-symbol? d)
                 (let ((n (datum->symbol d)))
                   (cond ((symbol=? n sym-true) (e-bool #t a b))
                         ((symbol=? n sym-false) (e-bool #f a b))
                         ((symbol=? n sym-unit) (e-unit a b))
                         (else (e-var n a b)))))
                (else (pfail "not an expression in the FX-26 kernel" s))))
        (lst (items d a b)
          (if (null? items)
              (pfail "not an expression in the FX-26 kernel" s)
              (parse-form s items (syn-head (car items)) a b)))
        (else x (pfail "not an expression in the FX-26 kernel" s)))))
  (parse-form (subr (maxeff parses spin) (syn syns-a symbol int int) exp)
    (lambda (s items head a b)
      (cond
        ((symbol=? head 'lambda)
         (begin (at-least items 3 "`(lambda ((name type) …) body …)`" a b)
                (parse-lambda-at items 1 a b)))
        ;; A variadic procedure, FX-87's: `(vlambda xs body …)`, or with the
        ;; arguments' type `(vlambda (xs T) body …)`, is
        ;; `(%vlambda (lambda ((xs (listof T acyclic))) body …))`.
        ((symbol=? head 'vlambda)
         (begin (at-least items 3 vlambda-usage a b)
                (let ((param (parse-vparam (nth items 1) a b)))
                  (e-app (e-var '%vlambda a b)
                         (cons (e-lambda (cons param nil) (parse-body (drop items 2) a b) a b) nil)
                         a b))))
        ((symbol=? head 'rlambda)
         (begin (at-least items 3 "`(rlambda region ((name type) …) body …)`" a b)
                (let ((r (parse-exp (nth items 1))))
                  (e-rlambda r (parse-lambda-at items 2 a b) a b))))
        ((region-form? head) (parse-region-form items head a b))
        ((symbol=? head 'plambda)
         (begin (at-least items 3 "`(plambda ((name kind) …) body …)`" a b)
                (e-plambda (nth items 1) (parse-body (drop items 2) a b) a b)))
        ((symbol=? head 'proj)
         (begin (at-least items 2 "`(proj expression description …)`" a b)
                (if (null? (drop items 2))
                    (pfail-at "`proj` needs at least one description" a b)
                    #u)
                (e-proj (parse-exp (nth items 1)) (keep (drop items 2)) a b)))
        ((symbol=? head 'if)
         (begin (arity items 4 "`(if test then else)`" a b)
                (e-if (parse-nth items 1) (parse-nth items 2) (parse-nth items 3) a b)))
        ((symbol=? head 'letrec)
         (begin (at-least items 3 "`(letrec ((name type expression) …) body …)`" a b)
                (e-letrec (parse-letrec-bindings (syn-items (nth items 1) "letrec bindings"))
                          (parse-body (drop items 2) a b) a b)))
        ((symbol=? head 'let)
         (begin (at-least items 3 "`(let ((name expression) …) body …)`" a b)
                (e-let (parse-let-bindings (syn-items (nth items 1) "let bindings"))
                       (parse-body (drop items 2) a b) a b)))
        ((symbol=? head 'begin) (parse-body (cdr items) a b))
        ((symbol=? head 'cond) (parse-cond (cdr items) a b))
        ;; `(confirm-length e k (x body) else)`: `(let ((%confirm-value e))
        ;; (if (length-is? %confirm-value k) (let ((x (certify-length
        ;; %confirm-value k))) body) else))`.
        ((symbol=? head 'confirm-length)
         (let ((usage "`(confirm-length expression length (name body) else)`"))
           (begin
             (arity items 5 usage a b)
             ;; A natural literal, or a variable holding a `nat`.
             (let* ((n (nth items 2))
                    (k (confirm-length-k n))
                    (length (if (< k 0) (e-var (syn-symbol n) a b) (e-int k a b))))
               (parse-confirm items 3 usage "%confirm-value" 'length-is? 'certify-length
                              (the exp-list (cons length nil)) a b)))))
        ;; `(acyclic e (x body) else)`: `(let ((%acyclic-value e)) (if
        ;; (acyclic? %acyclic-value) (let ((x (certify-acyclic
        ;; %acyclic-value))) body) else))`.
        ((symbol=? head 'acyclic)
         (let ((usage "`(acyclic expression (name body) else)`"))
           (begin
             (arity items 4 usage a b)
             (parse-confirm items 2 usage "%acyclic-value" 'acyclic? 'certify-acyclic nil a b))))
        ;; `(confirm-nat e (n body) else)`: `(let ((%nat-value e)) (if (nat?
        ;; %nat-value) (let ((n (certify-nat %nat-value))) body) else))`.
        ((symbol=? head 'confirm-nat)
         (let ((usage "`(confirm-nat expression (name body) else)`"))
           (begin
             (arity items 4 usage a b)
             (parse-confirm items 2 usage "%nat-value" 'nat? 'certify-nat nil a b))))
        ((symbol=? head 'and) (parse-and (cdr items) a b))
        ((symbol=? head 'or) (parse-or (cdr items) a b))
        ((symbol=? head 'let*)
         (begin (at-least items 3 "`(let* ((name expression) …) body …)`" a b)
                (parse-let* (syn-items (nth items 1) "let* bindings")
                            (parse-body (drop items 2) a b))))
        ((symbol=? head 'the)
         (begin (arity items 3 "`(the type expression)`" a b)
                (e-the (nth items 1) (parse-exp (nth items 2)) a b)))
        ((symbol=? head 'convention)
         (begin (arity items 3 "`(convention C expression)`" a b)
                (e-convention (nth items 1) (parse-exp (nth items 2)) a b)))
        ((bloblet-form? head) (parse-bloblet head (cdr items) a b))
        ((symbol=? head 'product) (e-product (parse-fields (cdr items)) a b))
        ((symbol=? head 'extract)
         (begin (arity items 3 "`(extract expression label)`" a b)
                (let ((l (label (nth items 2)))) (e-extract (parse-exp (nth items 1)) l a b))))
        ((symbol=? head 'sum)
         (begin (arity items 3 "`(sum tag expression)`" a b)
                (let ((t (label (nth items 1)))) (e-sum t (parse-exp (nth items 2)) a b))))
        ((symbol=? head 'tagcase)
         (begin (at-least items 2 "`(tagcase expression (tag name body …) …)`" a b)
                (let ((scrutinee (parse-exp (nth items 1))) (arms (drop items 2)))
                  (e-tagcase scrutinee (parse-arms arms) (parse-else arms) a b))))
        ((symbol=? head 'quote)
         (if (and (= (len items) 2) (syn-symbol? (nth items 1)))
             (e-sym (syn-symbol (nth items 1)) a b)
             (pfail-at "only a symbol can be quoted: `'name`" a b)))
        ((symbol=? head 'prompt)
         (begin (arity items 4 "`(prompt tag body handler)`" a b)
                (e-prompt (parse-nth items 1) (parse-nth items 2) (parse-nth items 3) a b)))
        ((symbol=? head 'module) (e-module (parse-module-items (cdr items)) a b))
        ;; `(load-module "file")`: the file's forms, a module's items
        ;; (`parser-load.fx`).
        ((symbol=? head 'load-module)
         (begin (arity items 2 "`(load-module \"file\")`" a b)
                (if (syn-string? (nth items 1))
                    (e-module ((get parse-load-module) (syn-string (nth items 1)) a b) a b)
                    (pfail (string-append "`(load-module \"file\")`: "
                                          "the file's name, as a string")
                           (nth items 1)))))
        ((symbol=? head 'with)
         (begin (at-least items 2 "`(with module body …)`" a b)
                (if (syn-symbol? (nth items 1))
                    (e-with (syn-symbol (nth items 1)) (parse-body (drop items 2) a b) a b)
                    (pfail "`with` opens a module named by a variable" (nth items 1)))))
        (else (let ((f (parse-exp (car items)))) (e-app f (parse-exps (cdr items)) a b))))))
  ;; Item `i`, an expression.
  (parse-nth (subr (maxeff parses spin) (syns-a int) exp)
    (lambda (items i) (parse-exp (nth items i))))
  ;; A `lambda` of the parameters at `i` and the body after them.
  (parse-lambda-at (subr (maxeff parses spin) (syns-a int int int) exp)
    (lambda (items i a b)
      (e-lambda (parse-params (nth items i)) (parse-body (drop items (+ i 1)) a b) a b)))
  ;; `(letregion name body …)` and the other region forms.
  (parse-region-form (subr (maxeff parses spin) (syns-a symbol int int) exp)
    (lambda (items head a b)
      (begin (at-least items 2 (str3 "`(" (symbol->string head) " name body …)`") a b)
             ;; `(letfreeze (r p) body …)` freezes into place `p`;
             ;; `(letfreeze r body …)` into the heap.
             (let* ((given (nth items 1))
                    (pair (freeze-pair head given))
                    (name (if (null? pair) given (car pair)))
                    (into (if (null? pair) 'heap (syn-symbol (nth pair 1)))))
               (if (and (syn-symbol? name) (not (char=? (string-ref (syn-name name) 0) #\@)))
                   (e-letregion (region-kind head)
                                (syn-symbol name) into (parse-body (drop items 2) a b) a b)
                   (pfail (region-name-error head) name))))))
  ;; A confirming form, `(form e … (x body) else)` with its arm at `i`:
  ;; `(let ((tmp e)) (if (test tmp more …) (let ((x (cert tmp more …)))
  ;; body) else))`, `tmp` named `tmp-name`.
  (parse-confirm
    (subr (maxeff parses spin) (syns-a int string string symbol symbol exp-list int int) exp)
    (lambda (items i usage tmp-name test cert more a b)
      (let* ((arm (syn-items (nth items i) usage))
             (shaped (if (= (len arm) 2) #u (pfail usage (nth items i))))
             (x (if (syn-symbol? (car arm)) (syn-symbol (car arm)) (pfail "a name" (car arm))))
             (e (parse-exp (nth items 1)))
             (body (parse-exp (nth arm 1)))
             (els (parse-exp (nth items (+ i 1))))
             (tmp (string->symbol tmp-name))
             (then (e-let (one-let x (call-tmp cert tmp more a b)) body a b)))
        (e-let (one-let tmp e) (e-if (call-tmp test tmp more a b) then els a b) a b))))
  (parse-letrec-bindings (subr (maxeff parses spin) (syns-a) letrec-list)
    (lambda (bs)
      (parse-typed-bindings bs "a letrec binding" "a letrec binding is `(name type expression)`")))
  ;; Bindings `(name type expression)`, a `letrec`'s or a `define-rec`'s:
  ;; each `what`, and `usage` when one is not.
  (parse-typed-bindings (subr (maxeff parses spin) (syns-a string string) letrec-list)
    (lambda (bs what usage)
      (if (null? bs)
          nil
          (let ((parts (syn-items (car bs) what)))
            (if (= (len parts) 3)
                (let* ((name (syn-symbol (car parts)))
                       (init (parse-exp (nth parts 2)))
                       (rest (parse-typed-bindings (cdr bs) what usage)))
                  (cons (product (1 name) (2 (nth parts 1)) (3 init)) rest))
                (pfail usage (car bs)))))))
  ;; `(let ((name expression) …) …)`; `()` is no bindings.
  (parse-let-bindings (subr (maxeff parses spin) (syns-a) let-list)
    (lambda (bs)
      (if (null? bs)
          nil
          (let ((parts (syn-items (car bs) "a let binding")))
            (if (= (len parts) 2)
                (let* ((name (syn-symbol (car parts))) (init (parse-exp (nth parts 1))))
                  (cons (product (1 name) (2 init)) (parse-let-bindings (cdr bs))))
                (pfail "a let binding is `(name expression)`" (car bs)))))))
  ;; `let*`: nested one-binding `let`s, each spanning its binding.
  (parse-let* (subr (maxeff parses spin) (syns-a exp) exp)
    (lambda (bs body)
      (if (null? bs)
          body
          (let ((parts (syn-items (car bs) "a let* binding")))
            (if (= (len parts) 2)
                (let* ((name (syn-symbol (car parts)))
                       (init (parse-exp (nth parts 1)))
                       (inner (parse-let* (cdr bs) body)))
                  (e-let (one-let name init) inner (syn-start (car bs)) (syn-end (car bs))))
                (pfail "a let* binding is `(name expression)`" (car bs)))))))
  ;; `(cond (test e …) … (else e …))`: nested `if`s, each spanning its clause.
  (parse-cond (subr (maxeff parses spin) (syns-a int int) exp)
    (lambda (clauses a b)
      (cond ((null? clauses) (pfail-at "a `cond` needs at least an `else` clause" a b))
            (else
             (let* ((c (car clauses)) (parts (syn-items c "a cond clause")))
               (if (null? (cdr clauses))
                   (parse-cond-else c parts)
                   (if (null? parts)
                       (pfail "a cond clause is `(test expression …)`" c)
                       (let* ((test (parse-exp (car parts)))
                              (then (parse-body (cdr parts) (syn-start c) (syn-end c)))
                              (rest (parse-cond (cdr clauses) a b)))
                         (e-if test then rest (syn-start c) (syn-end c))))))))))
  ;; A `cond`'s last clause, `c`, which must be `else`.
  (parse-cond-else (subr (maxeff parses spin) (syn syns-a) exp)
    (lambda (c parts)
      (if (symbol=? (syn-head (car parts)) 'else)
          (parse-body (cdr parts) (syn-start c) (syn-end c))
          (pfail "a `cond` must end with an `else` clause: FX has no unspecified value" c))))
  ;; `(and a b …)`: `(if a (and b …) #f)`, and `(and)` is `#t`.
  (parse-and (subr (maxeff parses spin) (syns-a int int) exp)
    (lambda (xs a b)
      (cond ((null? xs) (e-bool #t a b))
            ((null? (cdr xs)) (parse-exp (car xs)))
            (else (let* ((x (parse-exp (car xs))) (rest (parse-and (cdr xs) a b)))
                    (e-if x rest (e-bool #f a b) a b))))))
  ;; `(or a b …)`: `(if a #t (or b …))`, and `(or)` is `#f`.
  (parse-or (subr (maxeff parses spin) (syns-a int int) exp)
    (lambda (xs a b)
      (cond ((null? xs) (e-bool #f a b))
            ((null? (cdr xs)) (parse-exp (car xs)))
            (else (let* ((x (parse-exp (car xs))) (rest (parse-or (cdr xs) a b)))
                    (e-if x (e-bool #t a b) rest a b))))))
  (parse-bloblet (subr (maxeff parses spin) (symbol syns-a int int) exp)
    (lambda (op args a b)
      (let ((n (len args)))
        (cond ((and (symbol=? op 'make-bloblet) (>= n 1)) (e-bloblet op -1 (parse-exps args) a b))
              ((and (symbol=? op 'rmake-bloblet) (>= n 2)) (e-bloblet op -1 (parse-exps args) a b))
              ((and (symbol=? op 'bloblet-ref) (= n 2))
               (let* ((i (field-index (nth args 1))) (x (parse-exp (car args))))
                 (e-bloblet op i (the exp-list (cons x nil)) a b)))
              ((and (symbol=? op 'bloblet-set!) (= n 3))
               (let* ((i (field-index (nth args 1)))
                      (x (parse-exp (car args)))
                      (v (parse-exp (nth args 2))))
                 (e-bloblet op i (list x v) a b)))
              ((bloblet-untagged? op n) (e-bloblet op -1 (parse-exps args) a b))
              (else (pfail-at (str3 "`(" (symbol->string op) " …)`") a b))))))
  (parse-fields (subr (maxeff parses spin) (syns-a) let-list)
    (lambda (ps)
      (if (null? ps)
          nil
          (let ((pair (syn-items (car ps) "`(label expression)`")))
            (if (= (len pair) 2)
                (let* ((l (label (car pair))) (e (parse-exp (nth pair 1))))
                  (cons (product (1 l) (2 e)) (parse-fields (cdr ps))))
                (pfail "`(product (label expression) …)`" (car ps)))))))
  ;; The arms of a `tagcase` other than `else`.
  (parse-arms (subr (maxeff parses spin) (syns-a) arm-list)
    (lambda (cs)
      (cond ((null? cs) nil)
            ((arm-else? (car cs))
             (if (null? (cdr cs)) nil (pfail "`else` must be the last arm" (car cs))))
            (else
             (let* ((c (car cs)) (parts (syn-items c "a tagcase arm")))
               (if (< (len parts) 3)
                   (if (< (len parts) 2)
                       (pfail "a tagcase arm is `(tag name body …)`" c)
                       (pfail "a tagcase arm needs a body" c))
                   (let* ((tag (label (car parts)))
                          (bind (nth parts 1))
                          (fields (not (syn-symbol? bind)))
                          (ns (arm-names fields bind))
                          (body (parse-arm-body parts c))
                          (rest (parse-arms (cdr cs))))
                     (cons (product (1 tag) (2 fields) (3 ns) (4 body)) rest))))))))
  ;; An arm's body, `c`'s items after its first two.
  (parse-arm-body (subr (maxeff parses spin) (syns-a syn) exp)
    (lambda (parts c) (parse-body (drop parts 2) (syn-start c) (syn-end c))))
  ;; The `else` arm, as a list of none or one.
  (parse-else (subr (maxeff parses spin) (syns-a) let-list)
    (lambda (cs)
      (cond ((null? cs) nil)
            ((arm-else? (car cs))
             (let* ((c (car cs)) (parts (syn-items c "a tagcase arm")))
               (if (< (len parts) 3)
                   (pfail "a tagcase arm needs a body" c)
                   (if (syn-symbol? (nth parts 1))
                       (let* ((y (syn-symbol (nth parts 1))) (body (parse-arm-body parts c)))
                         (cons (product (1 y) (2 body)) nil))
                       (pfail "`else` binds one name" (nth parts 1))))))
            (else (parse-else (cdr cs))))))
  ;; A `module`'s items, in order.
  ;; A module's forms, its `define-datatype`s expanded.
  (parse-module-items (subr (maxeff parses spin) (syns-a) mod-items)
    (lambda (fs)
      (cond ((null? fs) nil)
            ((datatype? (car fs)) (parse-module-items (append (expand-datatype (car fs)) (cdr fs))))
            (else (let* ((item (parse-module-item (car fs))) (rest (parse-module-items (cdr fs))))
                    (cons item rest))))))
  ;; `(define-generative t T)`, `(define-type d T)`, `(define x e)`, `(define
  ;; x T e)` or `(define-rec (f T e) …)`.
  (parse-module-item (subr (maxeff parses spin) (syn) mod-item)
    (lambda (f)
      (let* ((parts (syn-items f "a module's definition"))
             (n (len parts))
             (head (if (null? parts) '|()| (syn-head (car parts)))))
        (cond ((and (symbol=? head 'define-generative) (= n 3))
               ;; `(define-generative (t (p k) …) T)`: a type constructor, its
               ;; head kept after its representation for the checker to read.
               (let* ((head (nth parts 1))
                      (hs (tagcase head (lst (xs d a b) xs) (else x (the syns-a nil))))
                      (params? (and (not (null? hs)) (not (null? (cdr hs)))))
                      (name (syn-symbol (if params? (car hs) head)))
                      (up (identity-at (syn-start f) (syn-end f)))
                      (down (identity-at (syn-start f) (syn-end f)))
                      (ts (if params?
                              (the syns-a (list (nth parts 2) head))
                              (one-syn (nth parts 2)))))
                 (mod-item-of 0 name ts (list up down))))
              ((and (symbol=? head 'define-type) (= n 3) (param-head? (nth parts 1)))
               (param-desc-item (syn-start f) (syn-end f) (nth parts 1) (nth parts 2)))
              ((and (symbol=? head 'define-type) (= n 3))
               (mod-item-of 1 (syn-symbol (nth parts 1)) (one-syn (nth parts 2)) nil))
              ((and (symbol=? head 'define) (= n 3))
               (let* ((name (syn-symbol (nth parts 1))) (init (parse-exp (nth parts 2))))
                 (mod-item-of 2 name (the syns-a nil) (the exp-list (cons init nil)))))
              ((and (symbol=? head 'define) (= n 4))
               (let* ((name (syn-symbol (nth parts 1))) (init (parse-exp (nth parts 3))))
                 (mod-item-of 2 name (one-syn (nth parts 2)) (the exp-list (cons init nil)))))
              ;; `(define-effect e E)`: a description, its types the effect
              ;; and a mark.
              ((and (symbol=? head 'define-effect) (= n 3))
               (let* ((mark (mk-symbol "effect" (syn-start f) (syn-end f)))
                      (ts (the syns-a (list (nth parts 2) mark))))
                 (mod-item-of 1 (syn-symbol (nth parts 1)) ts nil)))
              ;; `(define* f T e)`: a `define`, its types the type and a mark.
              ((and (symbol=? head 'define*) (= n 4))
               (let* ((name (syn-symbol (nth parts 1))) (init (parse-exp (nth parts 3)))
                      (mark (mk-symbol "*" (syn-start f) (syn-end f))))
                 (mod-item-of 2 name (the syns-a (list (nth parts 2) mark))
                              (the exp-list (cons init nil)))))
              ((symbol=? head 'define-rec)
               (let ((bs (parse-typed-bindings (cdr parts) "`(name type expression)`"
                                               "`(define-rec (name type expression) …)`")))
                 (product (1 3) (2 (rec-names bs)) (3 (rec-types bs)) (4 (rec-inits bs)))))
              (else (pfail module-usage f)))))))

;; A `define-rec`'s bindings, as a `letrec`'s are.
(define parse-rec-bindings (subr (maxeff parses spin) (syns-a) letrec-list)
  (lambda (bs)
    (let ((usage "a define-rec binding is `(name type lambda)`"))
      (parse-typed-bindings bs "a define-rec binding" usage))))

;; `(define name type expression)` or `(define name expression)`; for a
;; `define*` (`star?`), the type's list holds the head too.
(define parse-define (subr (maxeff parses spin) (syn bool) top)
  (lambda (s star?)
    (let* ((items (syn-items s "a definition")) (n (len items)) (a (syn-start s)) (b (syn-end s)))
      (cond ((= n 4)
             (let* ((name (syn-symbol (nth items 1)))
                    (heads (if star? (the syns-a (cons (car items) nil)) (the syns-a nil)))
                    (ty (the syns-a (cons (nth items 2) heads))))
               (t-define name ty (parse-exp (nth items 3)) a b)))
            ((= n 3)
             (let ((name (syn-symbol (nth items 1))))
               (t-define name (the syns-a nil) (parse-exp (nth items 2)) a b)))
            (else (pfail "`(define name type expression)` or `(define name expression)`" s))))))

;;; ------------------------------------------------------------- top level

(define parse-top (subr (maxeff parses spin) (syn) top)
  (lambda (s)
    (let ((head (form-head s)))
      (cond ((symbol=? head 'define) (parse-define s #f))
            ;; `(define* name type lambda)`: its type is a list of it and the
            ;; head, which says the checker finds what the lambda reads.
            ((symbol=? head 'define*) (parse-define s #t))
            ((symbol=? head 'define-rec)
             (let ((items (syn-items s "a group of definitions")))
               (if (null? (cdr items))
                   (pfail "`(define-rec (name type lambda) …)`" s)
                   (t-define-rec (parse-rec-bindings (cdr items)) (syn-start s) (syn-end s)))))
            ((symbol=? head 'define-type)
             (let ((items (syn-items s "a type definition")))
               (if (= (len items) 3)
                   (t-define-type (nth items 1) (nth items 2) (syn-start s) (syn-end s))
                   (pfail "`(define-type name type)`" s))))
            ((symbol=? head 'define-effect)
             (let ((items (syn-items s "an effect definition")))
               (if (= (len items) 3)
                   (t-define-effect (nth items 1) (nth items 2) (syn-start s) (syn-end s))
                   (pfail "`(define-effect name effect)`" s))))
            ((symbol=? head 'private-regions)
             (let ((regions (keep (cdr (syn-items s "private-regions")))))
               (t-private-regions regions (syn-start s) (syn-end s))))
            (else (t-exp (parse-exp s)))))))

(define append-tops (subr (read @globals) (top-list top-list) top-list)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (append-tops (cdr xs) ys)))))

;; `(define-generative head rep)`: the form, and its two conversions, each
;; the identity: `(define up-name (poly (param …) (subr pure (rep) (name p
;; …))) (lambda (x) x))`, and `down-name` the other way.
(define generative? (subr (maxeff (read @globals) (read @s)) (syn) bool)
  (lambda (s) (form-of? s 'define-generative)))
;; A parameter as a binder, its variance left out.
(define gen-binder (subr parses (syn int int) syn)
  (lambda (param a b)
    (let ((p (syn-items param "a parameter")))
      (if (>= (len p) 2)
          (mk-list (list (car p) (nth p 1)) a b)
          (pfail "a parameter is `(name kind)`, `(name kind +)` or `(name kind -)`" param)))))
;; The parameters as binders, and their names.
(define gen-binders (subr parses (syns-a int int) syns-a)
  (lambda (ps a b)
    (if (null? ps)
        nil
        (let ((binder (gen-binder (car ps) a b)))
          (cons binder (gen-binders (cdr ps) a b))))))
(define gen-names (subr parses (syns-a) syns-a)
  (lambda (bs)
    (if (null? bs)
        nil
        (cons (car (syn-items (car bs) "a parameter")) (gen-names (cdr bs))))))
;; A conversion, `prefix` and the name `n`, of type `ty`: the identity.
(define gen-conversion (subr (read @globals) (string string syn exp int int) top)
  (lambda (prefix n ty identity a b)
    (t-define (string->symbol (string-append prefix n)) (the syns-a (cons ty nil)) identity a b)))
(define parse-generative (subr parses (syn) top-list)
  (lambda (s)
    (let* ((items (syn-items s "a generative type")) (a (syn-start s)) (b (syn-end s))
           (usage (string-append "`(define-generative name type)` or "
                                 "`(define-generative (name (param kind) …) type)`")))
      (if (not (= (len items) 3))
          (pfail usage s)
          (let* ((head (nth items 1))
                 (rep (nth items 2))
                 (family? (tagcase head (lst (hs d ha hb) (not (null? hs))) (else x #f)))
                 (hs (if family? (syn-items head "a generative type's name") (the syns-a nil)))
                 (name (if family? (car hs) head))
                 (n (if (syn-symbol? name) (symbol->string (syn-symbol name)) (pfail usage s)))
                 (binders (if family? (gen-binders (cdr hs) a b) (the syns-a nil)))
                 (used (if family? (mk-list (cons name (gen-names binders)) a b) name))
                 (conv (lambda ((from syn) (to syn))
                         (let ((t (mk-pure-subr (the syns-a (cons from nil)) to a b)))
                           (if family? (mk-poly binders t a b) t))))
                 (x (product (1 'x) (2 (the syns-a nil))))
                 (identity (e-lambda (the param-list (cons x nil)) (e-var 'x a b) a b))
                 (up (gen-conversion "up-" n (conv rep used) identity a b))
                 (down (gen-conversion "down-" n (conv used rep) identity a b)))
            (list (t-define-generative head rep a b) up down))))))

;; Each of `xs`, parsed as a top-level form.
(define parse-each-top (subr (maxeff parses spin) (syns-a) top-list)
  (lambda (xs) (if (null? xs) nil (cons (parse-top (car xs)) (parse-each-top (cdr xs))))))
;; What top-level form `x` makes: a generative type's or a datatype's
;; several forms, or one.
(define parse-made (subr (maxeff parses spin) (syn) top-list)
  (lambda (x)
    (cond ((generative? x) (parse-generative x))
          ((datatype? x) (parse-each-top (expand-datatype x)))
          (else (the top-list (cons (parse-top x) nil))))))

(define parse-tops (subr (maxeff parses spin) (syns-a) top-list)
  (lambda (xs)
    (if (null? xs)
        nil
        (let* ((made (parse-made (car xs))) (rest (parse-tops (cdr xs))))
          (append-tops made rest)))))

;; The entry point: a program's forms, as read, to trees or an error. The
;; prompt catches every failure, but its tag is a global whose type names
;; @p, so the control effect stays in the type, as the reader's on @e do;
;; @p is this program's own, so that is still licensed.
(define parse-program (subr (maxeff (read @globals) parses spin) (syns-a) presult)
  (lambda (forms) (prompt parse-tag (p-ok (parse-tops forms)) (lambda (r) r))))
