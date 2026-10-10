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
;;; reader at those: `syn` is in the reader's region `rs`. The trees are
;;; `acyclic`: made by `cons` straight into the frozen region, never written,
;;; so a walk of one ends (`docs/fx26.md`, "Well-founded recursion"). A parse
;;; that fails aborts to a prompt in `rp`; it touches no other region, so
;;; `parse-program` is licensed as the reader's entry points are.
(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
;; The reader, at these regions, and what this file uses of it.
(define eager-reader-module ((proj (load-module "fx26:eager-reader.fx") rs re rm rc)))
(define-type syn (select eager-reader-module syn))
(define syn->datum (with eager-reader-module syn->datum))
(define-type result (select eager-reader-module result))
(define str3 (with eager-reader-module str3))
(define atom (with eager-reader-module atom))
(define lst (with eager-reader-module lst))
(define dotted (with eager-reader-module dotted))
(define vec (with eager-reader-module vec))
;; Its types, at these regions (`parser-types.fx`), and the names it uses
;; of them.
(define parser-types ((proj (load-module "fx26:parser-types.fx") rs re rm rc rp)))
(define-effect tree-builds (select parser-types tree-builds))
(define-effect parses (select parser-types parses))
(define-type syns-a (select parser-types syns-a))
(define-type names (select parser-types names))
(define-type exp (select parser-types exp))
(define-type top (select parser-types top))
(define-type exp-list (select parser-types exp-list))
(define-type param-list (select parser-types param-list))
(define-type letrec-list (select parser-types letrec-list))
(define-type let-list (select parser-types let-list))
(define-type arm-list (select parser-types arm-list))
(define-type top-list (select parser-types top-list))
(define-type mod-item (select parser-types mod-item))
(define-type mod-items (select parser-types mod-items))
(define-type presult (select parser-types presult))
(define-type loaded-file (select parser-types loaded-file))
(define-type loaded-files (select parser-types loaded-files))
(define e-var (with parser-types e-var))
(define e-int (with parser-types e-int))
(define e-bool (with parser-types e-bool))
(define e-str (with parser-types e-str))
(define e-char (with parser-types e-char))
(define e-float (with parser-types e-float))
(define e-sym (with parser-types e-sym))
(define e-unit (with parser-types e-unit))
(define e-lambda (with parser-types e-lambda))
(define e-app (with parser-types e-app))
(define e-plambda (with parser-types e-plambda))
(define e-proj (with parser-types e-proj))
(define e-if (with parser-types e-if))
(define e-letrec (with parser-types e-letrec))
(define e-let (with parser-types e-let))
(define e-begin (with parser-types e-begin))
(define e-prompt (with parser-types e-prompt))
(define e-letregion (with parser-types e-letregion))
(define e-rlambda (with parser-types e-rlambda))
(define e-the (with parser-types e-the))
(define e-convention (with parser-types e-convention))
(define e-bloblet (with parser-types e-bloblet))
(define e-product (with parser-types e-product))
(define e-extract (with parser-types e-extract))
(define e-sum (with parser-types e-sum))
(define e-tagcase (with parser-types e-tagcase))
(define e-module (with parser-types e-module))
(define e-with (with parser-types e-with))
(define t-define (with parser-types t-define))
(define t-define-rec (with parser-types t-define-rec))
(define t-define-type (with parser-types t-define-type))
(define t-define-effect (with parser-types t-define-effect))
(define t-define-generative (with parser-types t-define-generative))
(define t-exp (with parser-types t-exp))
(define p-ok (with parser-types p-ok))
(define p-err (with parser-types p-err))

(define parse-tag (prompt-tag presult presult (maxeff tree-builds (write rs) spin) rp)
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
(define syn-nil? (subr (read rs) (syn) bool)
  (lambda (s) (tagcase s (lst (items d a b) (null? items)) (else x #f))))
;; A proper list's items; `what`, when it is not one.
(define syn-items (subr parses (syn string) syns-a)
  (lambda (s what)
    (tagcase s
      (lst (items d a b) items)
      (else x (pfail (string-append what ": expected a list") s)))))
(define syn-int (subr pure (syn) int)
  (lambda (s) (tagcase s (atom (d a b) (if (datum-int? d) d -1)) (else x -1))))

(define len (subr (maxeff (read @globals) (read rs)) (syns-a) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (len (cdr xs))))))
(define nth (subr parses (syns-a int) syn)
  (lambda (xs i) (if (= i 0) (car xs) (nth (cdr xs) (- i 1)))))
(define drop (subr (maxeff (read @globals) (read rs)) (syns-a int) syns-a)
  (lambda (xs i) (if (= i 0) xs (drop (cdr xs) (- i 1)))))

;; A label or tag: a name, or a positive integer, which is its digits.
(define label (subr parses (syn) symbol)
  (lambda (s)
    (cond ((syn-symbol? s) (syn-head s))
          ((> (syn-int s) 0) (string->symbol (int->string (syn-int s))))
          (else (pfail "a label is a name or a positive integer" s)))))

(define keep (subr (maxeff (read @globals) (read rs)) (syns-a) syns-a)
  (lambda (xs) (if (null? xs) nil (cons (car xs) (keep (cdr xs))))))

;; `(tag x …)` with `n` items, or fail with `shape`.
(define arity (subr parses (syns-a int string int int) unit)
  (lambda (items n shape a b) (if (= (len items) n) #u (pfail-at shape a b))))
(define at-least (subr parses (syns-a int string int int) unit)
  (lambda (items n shape a b) (if (< (len items) n) (pfail-at shape a b) #u)))

(define mk-symbol (subr (read @globals) (string int int) syn)
  (lambda (n a b) (atom (string->symbol n) a b)))
(define syn-datums (subr (maxeff (read @globals) (read rs)) (syns-a) (listof datum acyclic))
  (lambda (xs) (if (null? xs) nil (cons (syn->datum (car xs)) (syn-datums (cdr xs))))))
(define mk-list (subr (maxeff (read @globals) (read rs)) (syns-a int int) syn)
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
(define form-head (subr (maxeff (read @globals) (read rs)) (syn) symbol)
  (lambda (s)
    (tagcase s
      (lst (items d a b) (if (null? items) '|()| (syn-head (car items))))
      (else x '|()|))))
;; Whether `s` is a form headed `keyword`.
(define form-of? (subr (maxeff (read @globals) (read rs)) (syn symbol) bool)
  (lambda (s keyword) (symbol=? (form-head s) keyword)))

(define arm-else? (subr (maxeff (read @globals) (read rs)) (syn) bool)
  (lambda (c) (form-of? c 'else)))

(define parse-names (subr parses (syns-a) names)
  (lambda (xs) (if (null? xs) nil (cons (syn-symbol (car xs)) (parse-names (cdr xs))))))

;; `(listof t acyclic)`, spanning `a`..`b`.
(define mk-listof-acyclic (subr (maxeff (read @globals) (read rs)) (syn int int) syn)
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
(define freeze-pair (subr (maxeff (read @globals) (read rs)) (symbol syn) syns-a)
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
(define param-head? (subr (maxeff (read @globals) (read rs)) (syn) bool)
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
;;; ------------------------------------------------------------ include

;; A module's `(include m)`s (`TODO.md` §69), as `parse.rs`'s
;; `with_includes`: one hidden item first, `%include`, a module of hidden
;; items `%include-0`, … that are the modules included, made before the
;; module's own items and seeing none of them; each own item's value in a
;; `(with %include …)` (a lambda's body, so that it stays a lambda), its
;; place the item's, as the compilers find facts by place. An `include`
;; is read as an item of kind 9, its form kept for its place.
(define include-form? (subr (maxeff (read @globals) (read rs)) (syn) bool)
  (lambda (f)
    (tagcase f
      (lst (xs d a b) (and (not (null? xs)) (symbol=? (syn-head (car xs)) 'include)))
      (else y #f))))
(define any-include? (subr (maxeff (read @globals) (read rs)) (syns-a) bool)
  (lambda (fs) (and (not (null? fs)) (or (include-form? (car fs)) (any-include? (cdr fs))))))
;; `x` in `(with %include …)` at `a`..`b`: a lambda's body, under any
;; `plambda`, `the` or region lambda.
(define in-includes (subr (maxeff tree-builds spin) (exp int int) exp)
  (lambda (x a b)
    (tagcase x
      (e-lambda (ps body la lb) (e-lambda ps (e-with '%include body a b) la lb))
      (e-plambda (bs body la lb) (e-plambda bs (in-includes body a b) la lb))
      (e-the (t e la lb) (e-the t (in-includes e a b) la lb))
      (e-rlambda (r l la lb) (e-rlambda r (in-includes l a b) la lb))
      (else y (e-with '%include x a b)))))
;; Each of `xs` so, at the place of the binding of `bs` it is.
(define inits-in-includes (subr (maxeff tree-builds spin) (exp-list syns-a) exp-list)
  (lambda (xs bs)
    (if (or (null? xs) (null? bs))
        xs
        (cons (in-includes (car xs) (syn-start (car bs)) (syn-end (car bs)))
              (inits-in-includes (cdr xs) (cdr bs))))))
;; Item `it`, read from form `f`, its values so.
(define item-in-includes (subr (maxeff tree-builds spin) (mod-item syn) mod-item)
  (lambda (it f)
    (let ((k (extract it 1)) (xs (extract it 4)))
      (product (1 k) (2 (extract it 2)) (3 (extract it 3))
               (4 (cond ((= k 2) (inits-in-includes xs (one-syn f)))
                        ((= k 3) (tagcase f (lst (bs d a b) (inits-in-includes xs (cdr bs)))
                                   (else y xs)))
                        (else xs)))))))
;; The included modules of `items`, from `%include-k` on.
(define include-items (subr (maxeff tree-builds spin) (mod-items int) mod-items)
  (lambda (items k)
    (cond ((null? items) nil)
          ((= (extract (car items) 1) 9)
           (cons (mod-item-of 2 (string->symbol (string-append "%include-" (int->string k))) nil
                              (extract (car items) 4))
                 (include-items (cdr items) (+ k 1))))
          (else (include-items (cdr items) k)))))
;; `items` but their includes; and the first include's form.
(define own-items (subr (maxeff tree-builds spin) (mod-items) mod-items)
  (lambda (items)
    (cond ((null? items) nil)
          ((= (extract (car items) 1) 9) (own-items (cdr items)))
          (else (cons (car items) (own-items (cdr items)))))))
(define first-include (subr (maxeff tree-builds spin) (mod-items) syns-a)
  (lambda (items)
    (cond ((null? items) nil)
          ((= (extract (car items) 1) 9) (extract (car items) 3))
          (else (first-include (cdr items))))))
;; A module's items, its includes made one `%include` first.
(define with-includes (subr (maxeff tree-builds spin) (mod-items) mod-items)
  (lambda (items)
    (let ((f (first-include items)))
      (if (null? f)
          items
          (cons (mod-item-of 2 '%include nil
                             (list (e-module (include-items items 0) (syn-start (car f))
                                             (syn-end (car f)))))
                (own-items items))))))

;; `(lambda (x) x)`, spanning `a`..`b`: an abstract type's conversion.
(define identity-at (subr (read @globals) (int int) exp)
  (lambda (a b)
    (let ((x (product (1 'x) (2 (the syns-a nil)))))
      (e-lambda (the param-list (cons x nil)) (e-var 'x a b) a b))))
(define module-usage string
  (string-append "a module holds `(define-generative t T)`, `(define-type d T)`, "
                 (string-append "`(define-effect e E)`, `(define x [T] e)`, `(define* f T e)`, "
                                "`(define-rec (f T e) …)` and `(include m)`")))
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

(define datatype? (subr (maxeff (read @globals) (read rs)) (syn) bool)
  (lambda (s) (form-of? s 'define-datatype)))

(define mk-int (subr (read @globals) (int int int) syn) (lambda (i a b) (atom i a b)))
;; `(keyword item …)`; `(subr pure (member …) result)`; and `(poly (binder
;; …) body)`: each spanning `a`..`b`.
(define mk-form (subr (maxeff (read @globals) (read rs)) (string syns-a int int) syn)
  (lambda (keyword items a b) (mk-list (cons (mk-symbol keyword a b) items) a b)))
(define mk-pure-subr (subr (maxeff (read @globals) (read rs)) (syns-a syn int int) syn)
  (lambda (members result a b)
    (let ((pure (mk-symbol "pure" a b)) (args (mk-list members a b)))
      (mk-form "subr" (list pure args result) a b))))
(define mk-poly (subr (maxeff (read @globals) (read rs)) (syns-a syn int int) syn)
  (lambda (binders body a b)
    (mk-form "poly" (list (mk-list binders a b) body) a b)))
;; A constructor's parameters, `%x1 …`, from `i`.
(define dt-vars (subr (maxeff (read @globals) (read rs) (alloc rs)) (syns-a int int int) syns-a)
  (lambda (ms i a b)
    (if (null? ms)
        nil
        (let ((x (mk-symbol (string-append "%x" (int->string i)) a b)))
          (cons x (dt-vars (cdr ms) (+ i 1) a b))))))
;; `(1 m1) (2 m2) …`, from `i`.
(define dt-labelled (subr (maxeff (read @globals) (read rs) (alloc rs)) (syns-a int int int) syns-a)
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
               ;; At its variant: no two constructors' bodies at one place.
               (body (mk-form "sum" (list tag fields) (syn-start (car vs)) (syn-end (car vs))))
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
          ;; A quote's, not a quasiquote's, marked (`%quote`), at its
          ;; opening parenthesis, a place of its own: everything in it the
          ;; rewrite's, made once where it is all literals.
          (mk-form "the" (list (mk-symbol "datum" a b)
                               (if (< depth 0) (fx-call "%quote" (list built) a (+ a 1)) built))
                   a b)
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
;; The depth a list's items after its head are at: a nested `quasiquote`
;; deepens, an `unquote` (or `unquote-splicing`) not at depth 1 shallows.
(define quasi-inner (subr parses (syns-a int) int)
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
(define unquote-free? (subr parses (syn int) bool)
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
(define items-free? (subr parses (syns-a int int) bool)
  (lambda (items depth inner)
    (or (null? items)
        (and (null? (if (= depth 1) (unquote-of (car items) "unquote-splicing") nil))
             (unquote-free? (car items) depth)
             (items-free? (cdr items) inner inner)))))
(define quoted-in (subr parses (syn int) syn)
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
                   ;; Each `with` made here at a place of its own (facts are
                   ;; kept by place): `nil` at the closing parenthesis, each
                   ;; `cons` at its item, a constant suffix's `%quote` from
                   ;; its first item to the end.
                   (lst (items d c e)
                     (if (null? items)
                         (mk-symbol "nil" a b)
                         (quoted-items items #f (car items) dq a b)))
                   (dotted (items tail d c e) (quoted-items items #t tail dq a b))
                   (vec (items d c e)
                     (if (null? items)
                         (fx-call "datum-list->vector" (list (fx-named "nil" (- b 1) b)) a (+ a 2))
                         (fx-call "datum-list->vector"
                                  (list (quoted-items items #f (car items) dq a b)) a (+ a 2)))))))
            (if mark? (fx-call "%quote" (list built) a (+ a 1)) built))))))
;; A list of `items`, then, if `dotted?`, `tail` (else `nil`), built.
(define quoted-items (subr parses (syns-a bool syn int int int) syn)
  (lambda (items dotted? tail depth a b)
    (let ((inner (quasi-inner items depth)))
      (quoted-onto items dotted? tail depth
                   (and (>= depth 1) (or (not dotted?) (unquote-free? tail depth)))
                   depth inner #t a b))))
;; `items`, then, if `dotted?`, `tail` (else `nil`), quoted, not
;; quasiquoted.
(define quoted-plain (subr parses (syns-a bool syn int int) syn)
  (lambda (items dotted? tail a b)
    (if (null? items)
        (if dotted? (quoted-in tail -1) (fx-named "nil" (- b 1) b))
        (fx-call "cons"
                 (list (quoted-in (car items) -1) (quoted-plain (cdr items) dotted? tail a b))
                 (syn-start (car items)) (syn-end (car items))))))
;; `items` onto the list's end, the first at `depth` and the rest at
;; `inner`: under a quasiquote (`free-tail?` its tail no unquote reaches),
;; the items after the first that no unquote reaches, with the tail, one
;; quote. As `Checker::quoted_in`.
(define quoted-onto (subr parses (syns-a bool syn int bool int int bool int int) syn)
  (lambda (items dotted? tail ldepth free-tail? depth inner first? a b)
    (cond
      ((null? items) (if dotted? (quoted-in tail ldepth) (fx-named "nil" (- b 1) b)))
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
(define loaded-files! (subr (maxeff (read @globals) (write rs) (alloc rs)) (loaded-files) unit)
  (lambda (fs) (begin (set loaded fs) (set loaded-next (loaded-onto fs nil)))))
;; `xs` reversed onto `ys`.
(define loaded-onto
  (subr (maxeff (read @globals) (alloc rs)) (loaded-files loaded-files) loaded-files)
  (lambda (xs ys) (if (null? xs) ys (loaded-onto (cdr xs) (the loaded-files (cons (car xs) ys))))))
;; The positions of one file and the next apart.
(define load-base int 1000000000)

;; Every load of a path is one value, made once (`TODO.md` §68): the first
;; defines a hidden global, `%shared:` and its key (`loaded-key`), as the
;; file loaded, before the form that loads it; every load is that global.
;; The keys loaded, and the definitions not yet placed before their form.
(define shared-keys (ref (listof string acyclic) rs) (new nil))
(define shared-pending (ref top-list rs) (new nil))
;; A program's parse begins with none.
(define shared-reset! (subr (maxeff (read @globals) (write rs)) () unit)
  (lambda () (begin (set shared-keys nil) (set shared-pending nil))))
;; The definitions not yet placed, in order, now placed: none left.
(define shared-taken (subr (maxeff (read @globals) (read rs) (write rs)) () top-list)
  (lambda ()
    (letrec ((onto (subr (read @globals) (top-list top-list) top-list)
                (lambda (xs ys) (if (null? xs) ys (onto (cdr xs) (cons (car xs) ys))))))
      (let ((ts (get shared-pending))) (begin (set shared-pending nil) (onto ts nil))))))
(define shared-key? (subr (read @globals) (string (listof string acyclic)) bool)
  (lambda (k ks) (and (not (null? ks)) (or (string=? k (car ks)) (shared-key? k (cdr ks))))))

;; What was read for the `load-module` starting at `a`, in a list of one.
(define loaded-at (subr (maxeff (read @globals) (read rs)) (loaded-files int) loaded-files)
  (lambda (fs a)
    (cond ((null? fs) nil)
          ((= (extract (car fs) 1) a) (the loaded-files (cons (car fs) nil)))
          (else (loaded-at (cdr fs) a)))))
;; The same, taking it from the front of `loaded-next` where it is there,
;; as it is when the driver read the files in the order they are parsed;
;; else found as `loaded-at` finds it.
(define loaded-next-at (subr (maxeff (read @globals) (read rs) (write rs)) (int) loaded-files)
  (lambda (a)
    (let ((next (get loaded-next)))
      (if (and (not (null? next)) (= (extract (car next) 1) a))
          (begin (set loaded-next (cdr next)) (the loaded-files (cons (car next) nil)))
          (loaded-at (get loaded) a)))))
;; The file read at `base`, in a list of one.
(define loaded-based (subr (maxeff (read @globals) (read rs)) (loaded-files int) loaded-files)
  (lambda (fs base)
    (cond ((null? fs) nil)
          ((and (> base 0) (= (extract (car fs) 2) base)) (the loaded-files (cons (car fs) nil)))
          (else (loaded-based (cdr fs) base)))))

;; Where position `at` of `text` is: `line:column`, each from 1.
(define text-place (subr (maxeff (read @globals) spin) (string int) string)
  (lambda (text at)
    (letrec ((go (subr (maxeff (read @globals) spin) (int int int) string)
               (lambda (i line col)
                 (cond ((or (>= i at) (>= i (string-length text)))
                        (str3 (int->string line) ":" (int->string col)))
                       ((char=? (string-ref text i) #\newline) (go (+ i 1) (+ line 1) 1))
                       (else (go (+ i 1) line (+ col 1)))))))
      (go 0 1 1))))
;; What an error `m` at `at`, in the file read at `base` (`fs`), says where
;; the `load-module` is: the file, and where in it. As it is, if `at` is
;; not in that file.
(define in-loaded
  (subr (maxeff (read @globals) (read rs) spin) (loaded-files int string int) string)
  (lambda (fs base m at)
    (let ((f (loaded-based fs base)))
      (if (or (null? f) (< at base) (>= at (+ base load-base)))
          m
          (let ((path (extract (car f) 4)) (text (extract (car f) 6)))
            (string-append (str3 "in `" path "`, ")
                           (str3 (text-place text (- at base)) ": " m)))))))

;; The items of a form that is a module.
(define module-items-of (subr pure (top) mod-items)
  (lambda (t)
    (tagcase t
      (t-exp (x) (tagcase x (e-module (items a b) items) (else y nil)))
      (else y nil))))
;; A module's item that says it was read from a file: its base, its path,
;; and its parameters' binders (`loaded-params`), which it sees.
(define loaded-mark (subr parses (int string syns-a) mod-item)
  (lambda (base path ps)
    (let ((bs (if (null? ps) (the syns-a nil) (syn-items (car ps) "`((name kind) …)`"))))
      (mod-item-of base (string->symbol path) bs nil))))
;; A module's item that says reading its file failed, and why: refused where
;; the module is checked, as the Rust checker refuses it where it parses
;; the form.
(define loaded-error (subr (read @globals) (string) mod-items)
  (lambda (m) (cons (mod-item-of -1 (string->symbol m) (the syns-a nil) nil) nil)))

;; A `load-input` file's forms, loaded at `a`..`b`: its one expression,
;; as the module item `(define input expression)`; refused if not one.
(define input-items (subr parses (syns-a int int) syns-a)
  (lambda (forms a b)
    (if (and (not (null? forms)) (null? (cdr forms)))
        (let* ((one (car forms))
               (item (the syns-a (list (mk-symbol "define" a b) (mk-symbol "input" a b) one))))
          (the syns-a (cons (mk-list item (syn-start one) (syn-end one)) nil)))
        (pfail-at "a `load-input` file is one expression" a b))))
;; A module's file's parameters, if its first form is `(module-parameters
;; ((name kind) …))`, in a list of one; none if not.
(define loaded-params (subr parses (syns-a) syns-a)
  (lambda (forms)
    (if (and (not (null? forms)) (form-of? (car forms) 'module-parameters))
        (let ((items (syn-items (car forms) "`(module-parameters ((name kind) …))`")))
          (begin (arity items 2 "`(module-parameters ((name kind) …))`"
                        (syn-start (car forms)) (syn-end (car forms)))
                 (the syns-a (cons (nth items 1) nil))))
        nil)))
;; Module `m` read from a file of parameters `ps` (`loaded-params`), at
;; `a`..`b`: a `plambda` over them of a `lambda` of none making it, so that
;; whoever loads it gives them, and each call makes one. `m`, if none.
(define* loaded-made (subr pure (syns-a exp int int) exp)
  (lambda (ps m a b)
    (if (null? ps) m (e-plambda (car ps) (e-lambda (the param-list nil) m a b) a b))))
