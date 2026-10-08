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

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define parser-module (module
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
  (lambda (s) (tagcase s (atom (d a b) (symbol? d)) (else x #f))))
(define syn-name (subr pure (syn) string)
  (lambda (s)
    (tagcase s
      (atom (d a b) (if (symbol? d) (symbol->string d) ""))
      (else x ""))))
;; A form's head as a symbol, to compare with the keywords: any that is
;; not a name is taken as `()`, which is none of them.
(define syn-head (subr pure (syn) symbol)
  (lambda (s)
    (tagcase s
      (atom (d a b) (if (symbol? d) d '|()|))
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
  (lambda (s) (tagcase s (atom (d a b) (if (datum-int? d) d -1)) (else x -1))))

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
  (lambda (n a b) (atom (string->symbol n) a b)))
(define syn-datums (subr (maxeff (read @globals) (read @s)) (syns-a) (listof datum acyclic))
  (lambda (xs) (if (null? xs) nil (cons (syn->datum (car xs)) (syn-datums (cdr xs))))))
(define mk-list (subr (maxeff (read @globals) (read @s)) (syns-a int int) syn)
  (lambda (items a b) (lst items (syn-datums items) a b)))
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
    (case head ((letregion) 0)
               ((letrena) 1)
               ((letreap) 2)
               (else 3))))
;; `(r p)`'s items, if a `letfreeze` binds that as `given`; else none.
(define freeze-pair (subr (maxeff (read @globals) (read @s)) (symbol syn) syns-a)
  (lambda (head given)
    (tagcase given
      (lst (xs d a2 b2) (if (and (symbol=? head 'letfreeze) (= (len xs) 2)) xs (the syns-a nil)))
      (else x (the syns-a nil)))))

;; A call `(f tmp more …)`, spanning `a`..`b`; and a `let`'s one binding.
;; `(with #%fx f)`: what an expansion calls, the standard binding, whatever
;; shadows or redefines `f` where it is (`TODO.md` §46).
(define standard-ref (subr tree-builds (symbol int int) exp)
  (lambda (f a b) (e-with '#%fx (e-var f a b) a b)))
(define call-tmp (subr tree-builds (symbol symbol exp-list int int) exp)
  (lambda (f tmp more a b)
    (e-app (standard-ref f a b) (the exp-list (cons (e-var tmp a b) more)) a b)))
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
  (lambda (s) (tagcase s (atom (d a b) (string? d)) (else x #f))))
(define syn-string (subr pure (syn) string)
  (lambda (s)
    (tagcase s (atom (d a b) (if (string? d) d "")) (else x ""))))
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

(define mk-int (subr (read @globals) (int int int) syn) (lambda (i a b) (atom i a b)))
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

;; What builds datum `x`, quoted (`depth` -1) or quasiquoted at `depth`
;; (TODO §51), as `Checker::quoted` builds it: atoms as themselves, symbols
;; quoted, `()` as `nil`, lists as `cons`es, a vector from its list; a list
;; or vector in `(the datum …)`. Under `quasiquote`, `(unquote e)` at depth
;; 1 is `e`, and `(unquote-splicing e)` is `e` appended to what follows.
(define quoted (subr parses (syn int) syn)
  (lambda (x depth)
    (let ((built (quoted-in x depth)) (a (syn-start x)) (b (syn-end x)))
      (if (and (tagcase x (atom (d c e) #f) (lst (items d c e) (not (null? items))) (else y #t))
               (null? (unquoted x depth)))
          (mk-form "the" (list (mk-symbol "datum" a b) built) a b)
          built))))
;; `(with #%fx name)`: the standard `name`, whatever a program binds it to.
(define fx-named (subr parses (string int int) syn)
  (lambda (n a b) (mk-form "with" (list (mk-symbol "#%fx" a b) (mk-symbol n a b)) a b)))
;; `((with #%fx op) arg …)`.
(define fx-call (subr parses (string syns-a int int) syn)
  (lambda (op args a b) (mk-list (cons (fx-named op a b) args) a b)))
;; `(form e)`: `e`, as a list of none or one.
(define unquote-of (subr parses (syn string) syns-a)
  (lambda (x form)
    (tagcase x
      (lst (items d a b)
        (if (and (= (len items) 2) (string=? (syn-name (car items)) form)) (cdr items) nil))
      (else y nil))))
(define unquoted (subr parses (syn int) syns-a)
  (lambda (x depth) (if (= depth 1) (unquote-of x "unquote") nil)))
(define quoted-in (subr parses (syn int) syn)
  (lambda (x depth)
    (let ((u (unquoted x depth)) (a (syn-start x)) (b (syn-end x)))
      (if (not (null? u))
          (car u)
          (tagcase x
            (atom (d c e)
              (cond ((not (symbol? d))
                     (if (bytevector? d) (pfail "a bytevector cannot be quoted yet" x) x))
                    ((or (symbol=? d sym-true) (symbol=? d sym-false)) x)
                    (else (mk-form "quote" (list x) a b))))
            ;; Each `with` made here at a place of its own (facts are kept
            ;; by place): `nil` at the closing parenthesis, each `cons` at
            ;; its item.
            (lst (items d c e)
              (if (null? items)
                  (mk-symbol "nil" a b)
                  (quoted-items items (fx-named "nil" (- b 1) b) depth a b)))
            (dotted (items tail d c e) (quoted-items items (quoted-in tail depth) depth a b))
            (vec (items d c e)
              (fx-call "datum-list->vector"
                       (list (quoted-items items (fx-named "nil" (- b 1) b) depth a b))
                       a (+ a 2))))))))
;; A list of `items`, then `end`, built: a nested `quasiquote` deepens, an
;; `unquote` not at depth 1 shallows.
(define quoted-items (subr parses (syns-a syn int int int) syn)
  (lambda (items end depth a b)
    (let* ((head (if (null? items) "" (syn-name (car items))))
           (two (= (len items) 2))
           (inner (cond ((< depth 0) depth)
                        ((and two (string=? head "quasiquote")) (+ depth 1))
                        ((and two (> depth 1)
                              (or (string=? head "unquote") (string=? head "unquote-splicing")))
                         (- depth 1))
                        (else depth))))
      (quoted-onto items end depth inner a b))))
(define quoted-onto (subr parses (syns-a syn int int int int) syn)
  (lambda (items end depth inner a b)
    (if (null? items)
        end
        (let ((rest (quoted-onto (cdr items) end inner inner a b))
              (spliced (if (= depth 1) (unquote-of (car items) "unquote-splicing") nil))
              (ia (syn-start (car items))) (ib (syn-end (car items))))
          (if (null? spliced)
              (fx-call "cons" (list (quoted-in (car items) depth) rest) ia ib)
              (let ((ty (mk-list (list (mk-symbol "listof" a b) (mk-symbol "datum" a b)
                                       (mk-symbol "acyclic" a b))
                                 a b)))
                (fx-call "append" (list (car spliced) (mk-form "the" (list ty rest) a b))
                         ia ib)))))))


))

(define-effect parses (select parser-module parses))
(define-type syns-a (select parser-module syns-a))
(define-type names (select parser-module names))
(define-type exp (select parser-module exp))
(define-type top (select parser-module top))
(define-type exp-list (select parser-module exp-list))
(define-type param-list (select parser-module param-list))
(define-type top-list (select parser-module top-list))
(define-type mod-item (select parser-module mod-item))
(define-type mod-items (select parser-module mod-items))
(define-type presult (select parser-module presult))
(define parse-tag (with parser-module parse-tag))
(define syn-start (with parser-module syn-start))
(define syn-end (with parser-module syn-end))
(define pfail (with parser-module pfail))
(define pfail-at (with parser-module pfail-at))
(define syn-symbol? (with parser-module syn-symbol?))
(define syn-name (with parser-module syn-name))
(define syn-head (with parser-module syn-head))
(define syn-symbol (with parser-module syn-symbol))
(define syn-items (with parser-module syn-items))
(define syn-int (with parser-module syn-int))
(define len (with parser-module len))
(define nth (with parser-module nth))
(define drop (with parser-module drop))
(define label (with parser-module label))
(define keep (with parser-module keep))
(define arity (with parser-module arity))
(define mk-list (with parser-module mk-list))
(define form-head (with parser-module form-head))
(define form-of? (with parser-module form-of?))
(define big-literal (with parser-module big-literal))
(define mod-item-of (with parser-module mod-item-of))
(define datatype? (with parser-module datatype?))
(define mk-pure-subr (with parser-module mk-pure-subr))
(define mk-poly (with parser-module mk-poly))
(define expand-datatype (with parser-module expand-datatype))
(define e-var (with parser-module e-var))
(define e-int (with parser-module e-int))
(define e-bool (with parser-module e-bool))
(define e-str (with parser-module e-str))
(define e-char (with parser-module e-char))
(define e-float (with parser-module e-float))
(define e-sym (with parser-module e-sym))
(define e-unit (with parser-module e-unit))
(define e-lambda (with parser-module e-lambda))
(define e-app (with parser-module e-app))
(define e-plambda (with parser-module e-plambda))
(define e-proj (with parser-module e-proj))
(define e-if (with parser-module e-if))
(define e-letrec (with parser-module e-letrec))
(define e-let (with parser-module e-let))
(define e-begin (with parser-module e-begin))
(define e-prompt (with parser-module e-prompt))
(define e-letregion (with parser-module e-letregion))
(define e-rlambda (with parser-module e-rlambda))
(define e-the (with parser-module e-the))
(define e-convention (with parser-module e-convention))
(define e-bloblet (with parser-module e-bloblet))
(define e-product (with parser-module e-product))
(define e-extract (with parser-module e-extract))
(define e-sum (with parser-module e-sum))
(define e-tagcase (with parser-module e-tagcase))
(define e-module (with parser-module e-module))
(define e-with (with parser-module e-with))
(define t-define (with parser-module t-define))
(define t-define-rec (with parser-module t-define-rec))
(define t-define-type (with parser-module t-define-type))
(define t-define-effect (with parser-module t-define-effect))
(define t-define-generative (with parser-module t-define-generative))
(define t-private-regions (with parser-module t-private-regions))
(define t-exp (with parser-module t-exp))
(define p-ok (with parser-module p-ok))
(define p-err (with parser-module p-err))
(define-type letrec-list (select parser-module letrec-list))
(define-type let-list (select parser-module let-list))
(define-type arm-list (select parser-module arm-list))
(define sym-true (with parser-module sym-true))
(define sym-false (with parser-module sym-false))
(define sym-unit (with parser-module sym-unit))
(define at-least (with parser-module at-least))
(define vlambda-usage (with parser-module vlambda-usage))
(define parse-vparam (with parser-module parse-vparam))
(define region-form? (with parser-module region-form?))
(define confirm-length-k (with parser-module confirm-length-k))
(define bloblet-form? (with parser-module bloblet-form?))
(define syn-string? (with parser-module syn-string?))
(define syn-string (with parser-module syn-string))
(define parse-params (with parser-module parse-params))
(define freeze-pair (with parser-module freeze-pair))
(define region-kind (with parser-module region-kind))
(define region-name-error (with parser-module region-name-error))
(define one-let (with parser-module one-let))
(define call-tmp (with parser-module call-tmp))
(define standard-ref (with parser-module standard-ref))
(define field-index (with parser-module field-index))
(define bloblet-untagged? (with parser-module bloblet-untagged?))
(define arm-else? (with parser-module arm-else?))
(define arm-names (with parser-module arm-names))
(define identity-at (with parser-module identity-at))
(define one-syn (with parser-module one-syn))
(define param-head? (with parser-module param-head?))
(define param-desc-item (with parser-module param-desc-item))
(define mk-symbol (with parser-module mk-symbol))
(define quoted (with parser-module quoted))
(define rec-names (with parser-module rec-names))
(define rec-types (with parser-module rec-types))
(define rec-inits (with parser-module rec-inits))
(define module-usage (with parser-module module-usage))
