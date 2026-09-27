;;; The FX-26 parser, in FX-26 (PLAN.md §11, step 9a).
;;;
;;; What the eager reader read (`syn`, with positions) to an abstract syntax
;;; tree, with the Rust parser's desugarings (`crates/fixpt-fx26/src/parse.rs`),
;;; node for node and span for span, so the two can be compared. Descriptions
;;; (types, effects, regions, binders) are kept as the syntax they were
;;; written in: the evaluator and the compiler do not need them, and the
;;; checker written in FX-26 (`check.fx`) reads them itself.
;;;
;;; Compiled with the reader, as one program: `syn` is in the reader's region
;;; @s, which only this program can name. The trees are `finite`: made by
;;; `cons` straight into the frozen region, never written, so a walk of one
;;; ends (`docs/fx26.md`, "Well-founded recursion"). A parse
;;; that fails aborts to a prompt in @p; both are this program's own, so
;;; `parse-program` is licensed as the reader's entry points are.

(private-regions @p)

;; What a parse may do: read what was read, build a tree, and give up.
(define-effect parses (maxeff (read @s) (alloc @s) (goto @p)))

(define-type syns-a (listof syn finite))
(define-type names (listof symbol finite))

;;; ------------------------------------------------------------------ trees
;;; Each node ends with where it starts and ends. A list of none or one
;;; stands for something optional: a parameter's type, a tagcase's `else`.

(define-datatype exp
  (e-var symbol int int)
  (e-int int int int)
  (e-bool bool int int)
  (e-str string int int)
  (e-char char int int)
  (e-sym symbol int int)
  (e-unit int int)
  (e-lambda (listof (productof (1 symbol) (2 syns-a)) finite) exp int int)
  (e-app exp (listof exp finite) int int)
  (e-plambda syn exp int int)
  (e-proj exp syns-a int int)
  (e-if exp exp exp int int)
  (e-letrec (listof (productof (1 symbol) (2 syn) (3 exp)) finite) exp int int)
  (e-let (listof (productof (1 symbol) (2 exp)) finite) exp int int)
  (e-begin (listof exp finite) int int)
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
  ;; A bloblet form, by name, with its field index, or -1.
  (e-bloblet symbol int (listof exp finite) int int)
  (e-product (listof (productof (1 symbol) (2 exp)) finite) int int)
  (e-extract exp symbol int int)
  (e-sum symbol exp int int)
  ;; Arms: the tag, whether it takes a product apart, the names, the body.
  (e-tagcase exp (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) finite)
             (listof (productof (1 symbol) (2 exp)) finite) int int))

;; A top-level form. A definition's type is a list of none or one.
(define-datatype top
  (t-define symbol syns-a exp int int)
  ;; `(define-rec (name type lambda) …)`: a top-level `letrec`.
  (t-define-rec (listof (productof (1 symbol) (2 syn) (3 exp)) finite) int int)
  (t-define-type syn syn int int)
  (t-define-effect syn syn int int)
  ;; `(define-generative head rep)`: read by the checker alone; its two
  ;; conversions follow it as definitions.
  (t-define-generative syn syn int int)
  (t-private-regions syns-a int int)
  (t-exp exp))

(define-datatype presult (p-ok (listof top finite)) (p-err string int int))

(define parse-tag (prompt-tag presult presult (maxeff spin (read @s) (alloc @s)) @p)
  (make-continuation-prompt-tag))

;;; -------------------------------------------------------- looking at syn

(define syn-start (subr pure (syn) int)
  (lambda (s) (tagcase s (atom (d a b) a) (lst (i d a b) a) (dotted (i t d a b) a) (vec (i d a b) a))))
(define syn-end (subr pure (syn) int)
  (lambda (s) (tagcase s (atom (d a b) b) (lst (i d a b) b) (dotted (i t d a b) b) (vec (i d a b) b))))

(define pfail (subr parses (string syn) void)
  (lambda (message s)
    (abort-current-continuation parse-tag (p-err message (syn-start s) (syn-end s)))))
(define pfail-at (subr parses (string int int) void)
  (lambda (message a b) (abort-current-continuation parse-tag (p-err message a b))))

(define syn-symbol? (subr pure (syn) bool)
  (lambda (s) (tagcase s (atom (d a b) (datum-symbol? d)) (else x #f))))
(define syn-name (subr pure (syn) string)
  (lambda (s) (tagcase s (atom (d a b) (if (datum-symbol? d) (datum-symbol-name d) "")) (else x ""))))
(define syn-symbol (subr parses (syn) symbol)
  (lambda (s) (tagcase s (atom (d a b) (if (datum-symbol? d) (datum->symbol d) (pfail "a name" s))) (else x (pfail "a name" s)))))
;; `#t`, `#f` and `#u` as the FX-26 reader gives them: symbols.
(define sym-true symbol (string->symbol "#t"))
(define sym-false symbol (string->symbol "#f"))
(define sym-unit symbol (string->symbol "#u"))
;; A form's head as a symbol, to compare with the keywords: any that is
;; not a name is taken as `()`, which is none of them.
(define syn-head (subr pure (syn) symbol)
  (lambda (s) (tagcase s (atom (d a b) (if (datum-symbol? d) (datum->symbol d) '|()|)) (else x '|()|))))
;; `()`, which reads as an empty list.
(define syn-nil? (subr (read @s) (syn) bool)
  (lambda (s) (tagcase s (lst (items d a b) (null? items)) (else x #f))))
;; A proper list's items; `what`, when it is not one.
(define syn-items (subr parses (syn string) (listof syn finite))
  (lambda (s what)
    (tagcase s (lst (items d a b) items) (else x (pfail (string-append what ": expected a list") s)))))
(define syn-int (subr pure (syn) int)
  (lambda (s) (tagcase s (atom (d a b) (if (datum-int? d) (datum-int-value d) -1)) (else x -1))))

(define len (subr (read @s) ((listof syn finite)) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (len (cdr xs))))))
(define nth (subr parses ((listof syn finite) int) syn)
  (lambda (xs i) (if (= i 0) (car xs) (nth (cdr xs) (- i 1)))))
(define drop (subr (read @s) ((listof syn finite) int) (listof syn finite))
  (lambda (xs i) (if (= i 0) xs (drop (cdr xs) (- i 1)))))

;; A label or tag: a name, or a positive integer, which is its digits.
(define label (subr parses (syn) symbol)
  (lambda (s)
    (cond ((syn-symbol? s) (syn-head s))
          ((> (syn-int s) 0) (string->symbol (int->string (syn-int s))))
          (else (pfail "a label is a name or a positive integer" s)))))

(define keep (subr (read @s) ((listof syn finite)) syns-a)
  (lambda (xs) (if (null? xs) nil (cons (car xs) (keep (cdr xs))))))

;; `(tag x …)` with `n` items, or fail with `shape`.
(define arity (subr parses ((listof syn finite) int string int int) unit)
  (lambda (items n shape a b) (if (= (len items) n) #u (pfail-at shape a b))))
(define at-least (subr parses ((listof syn finite) int string int int) unit)
  (lambda (items n shape a b) (if (< (len items) n) (pfail-at shape a b) #u)))

(define parse-params (subr parses (syn) (listof (productof (1 symbol) (2 syns-a)) finite))
  (lambda (ps)
    (if (syn-nil? ps)
        nil
        (letrec ((each (subr parses ((listof syn finite)) (listof (productof (1 symbol) (2 syns-a)) finite))
                   (lambda (xs)
                     (if (null? xs)
                         nil
                         (let ((p (car xs)))
                           (cons (if (syn-symbol? p)
                                     (product (1 (syn-symbol p)) (2 (the syns-a nil)))
                                     (let ((pair (syn-items p "a parameter")))
                                       (if (= (len pair) 2)
                                           (product (1 (syn-symbol (car pair))) (2 (the syns-a (cons (nth pair 1) nil))))
                                           (pfail "a parameter is `name` or `(name type)`" p))))
                                 (each (cdr xs))))))))
          (each (syn-items ps "parameters"))))))

;; A bloblet form's field index: a literal, non-negative integer.
(define field-index (subr parses (syn) int)
  (lambda (s)
    (if (>= (syn-int s) 0) (syn-int s) (pfail "a field index is a literal, non-negative integer" s))))

(define arm-else? (subr (read @s) (syn) bool)
  (lambda (c) (tagcase c (lst (items d a b) (and (not (null? items)) (symbol=? (syn-head (car items)) 'else))) (else x #f))))

(define parse-names (subr parses ((listof syn finite)) names)
  (lambda (xs) (if (null? xs) nil (cons (syn-symbol (car xs)) (parse-names (cdr xs))))))

;;; ------------------------------------------------------------ expressions

(define-rec
  (parse-exps (subr (maxeff parses spin) ((listof syn finite)) (listof exp finite))
    (lambda (xs) (if (null? xs) nil (cons (parse-exp (car xs)) (parse-exps (cdr xs))))))
  ;; One or more expressions, an implicit `begin` spanning `a`..`b`.
  (parse-body (subr (maxeff parses spin) ((listof syn finite) int int) exp)
    (lambda (forms a b)
      (cond ((null? forms) (pfail-at "an empty body" a b))
            ((null? (cdr forms)) (parse-exp (car forms)))
            (else (e-begin (parse-exps forms) a b)))))
  (parse-exp (subr (maxeff parses spin) (syn) exp)
    (lambda (s)
      (tagcase s
        (atom (d a b)
          (cond ((datum-int? d) (e-int (datum-int-value d) a b))
                ((datum-string? d) (e-str (datum-string-value d) a b))
                ((datum-bool? d) (e-bool (datum-bool-value d) a b))
                ((datum-char? d) (e-char (datum-char-value d) a b))
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
  (parse-form (subr (maxeff parses spin) (syn (listof syn finite) symbol int int) exp)
    (lambda (s items head a b)
      (cond
        ((symbol=? head 'lambda)
         (begin (at-least items 3 "`(lambda ((name type) …) body …)`" a b)
                (e-lambda (parse-params (nth items 1)) (parse-body (drop items 2) a b) a b)))
        ((symbol=? head 'rlambda)
         (begin (at-least items 3 "`(rlambda region ((name type) …) body …)`" a b)
                (let ((r (parse-exp (nth items 1))))
                  (e-rlambda r (e-lambda (parse-params (nth items 2)) (parse-body (drop items 3) a b) a b) a b))))
        ((or (or (symbol=? head 'letregion) (symbol=? head 'letfreeze)) (or (symbol=? head 'letrena) (symbol=? head 'letreap)))
         (begin (at-least items 2 (string-append "`(" (string-append (symbol->string head) " name body …)`")) a b)
                ;; `(letfreeze (r p) body …)` freezes into place `p`;
                ;; `(letfreeze r body …)` into the heap.
                (let* ((given (nth items 1))
                       (pair (the (listof syn finite)
                               (tagcase given
                                 (lst (xs d a2 b2) (if (and (symbol=? head 'letfreeze) (= (len xs) 2)) xs (the (listof syn finite) nil)))
                                 (else x (the (listof syn finite) nil)))))
                       (name (if (null? pair) given (car pair)))
                       (into (if (null? pair) 'heap (syn-symbol (nth pair 1)))))
                  (if (and (syn-symbol? name) (not (char=? (string-ref (syn-name name) 0) #\@)))
                      (e-letregion (cond ((symbol=? head 'letregion) 0) ((symbol=? head 'letrena) 1) ((symbol=? head 'letreap) 2) (else 3))
                                   (syn-symbol name) into (parse-body (drop items 2) a b) a b)
                      (pfail (string-append "a `" (string-append (symbol->string head) "` binds a region variable's name, without `@`")) name)))))
        ((symbol=? head 'plambda)
         (begin (at-least items 3 "`(plambda ((name kind) …) body …)`" a b)
                (e-plambda (nth items 1) (parse-body (drop items 2) a b) a b)))
        ((symbol=? head 'proj)
         (begin (at-least items 2 "`(proj expression description …)`" a b)
                (if (null? (drop items 2)) (pfail-at "`proj` needs at least one description" a b) #u)
                (e-proj (parse-exp (nth items 1)) (keep (drop items 2)) a b)))
        ((symbol=? head 'if)
         (begin (arity items 4 "`(if test then else)`" a b)
                (e-if (parse-exp (nth items 1)) (parse-exp (nth items 2)) (parse-exp (nth items 3)) a b)))
        ((symbol=? head 'letrec)
         (begin (at-least items 3 "`(letrec ((name type expression) …) body …)`" a b)
                (e-letrec (parse-letrec-bindings (syn-items (nth items 1) "letrec bindings"))
                          (parse-body (drop items 2) a b) a b)))
        ((symbol=? head 'let)
         (begin (at-least items 3 "`(let ((name expression) …) body …)`" a b)
                (e-let (parse-let-bindings (syn-items (nth items 1) "let bindings")) (parse-body (drop items 2) a b) a b)))
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
                    (k (cond ((>= (syn-int n) 0) (syn-int n))
                             ((syn-symbol? n) -1)
                             (else (pfail "a length is a natural number, or a variable holding one" n))))
                    (arm (syn-items (nth items 3) usage))
                    (shaped (if (= (len arm) 2) #u (pfail usage (nth items 3))))
                    (x (if (syn-symbol? (car arm)) (syn-symbol (car arm)) (pfail "a name" (car arm))))
                    (e (parse-exp (nth items 1)))
                    (body (parse-exp (nth arm 1)))
                    (els (parse-exp (nth items 4)))
                    (tmp (string->symbol "%confirm-value"))
                    (test (e-app (e-var 'length-is? a b) (the (listof exp finite) (cons (e-var tmp a b) (cons (if (< k 0) (e-var (syn-symbol n) a b) (e-int k a b)) nil))) a b))
                    (cert (e-app (e-var 'certify-length a b) (the (listof exp finite) (cons (e-var tmp a b) (cons (if (< k 0) (e-var (syn-symbol n) a b) (e-int k a b)) nil))) a b))
                    (then (e-let (the (listof (productof (1 symbol) (2 exp)) finite) (cons (product (1 x) (2 cert)) nil)) body a b)))
               (e-let (the (listof (productof (1 symbol) (2 exp)) finite) (cons (product (1 tmp) (2 e)) nil))
                      (e-if test then els a b) a b)))))
        ;; `(acyclic e (x body) else)`: `(let ((%acyclic-value e)) (if
        ;; (acyclic? %acyclic-value) (let ((x (certify-acyclic
        ;; %acyclic-value))) body) else))`.
        ((symbol=? head 'acyclic)
         (let ((usage "`(acyclic expression (name body) else)`"))
           (begin
             (arity items 4 usage a b)
             (let* ((arm (syn-items (nth items 2) usage))
                    (shaped (if (= (len arm) 2) #u (pfail usage (nth items 2))))
                    (x (if (syn-symbol? (car arm)) (syn-symbol (car arm)) (pfail "a name" (car arm))))
                    (e (parse-exp (nth items 1)))
                    (body (parse-exp (nth arm 1)))
                    (els (parse-exp (nth items 3)))
                    (tmp (string->symbol "%acyclic-value"))
                    (test (e-app (e-var 'acyclic? a b) (the (listof exp finite) (cons (e-var tmp a b) nil)) a b))
                    (cert (e-app (e-var 'certify-acyclic a b) (the (listof exp finite) (cons (e-var tmp a b) nil)) a b))
                    (then (e-let (the (listof (productof (1 symbol) (2 exp)) finite) (cons (product (1 x) (2 cert)) nil)) body a b)))
               (e-let (the (listof (productof (1 symbol) (2 exp)) finite) (cons (product (1 tmp) (2 e)) nil))
                      (e-if test then els a b) a b)))))
        ((symbol=? head 'and) (parse-and (cdr items) a b))
        ((symbol=? head 'or) (parse-or (cdr items) a b))
        ((symbol=? head 'let*)
         (begin (at-least items 3 "`(let* ((name expression) …) body …)`" a b)
                (parse-let* (syn-items (nth items 1) "let* bindings") (parse-body (drop items 2) a b))))
        ((symbol=? head 'the)
         (begin (arity items 3 "`(the type expression)`" a b)
                (e-the (nth items 1) (parse-exp (nth items 2)) a b)))
        ((or (symbol=? head 'make-bloblet) (symbol=? head 'rmake-bloblet) (symbol=? head 'bloblet-ref) (symbol=? head 'bloblet-set!)
             (symbol=? head 'bloblet-freeze) (symbol=? head 'bloblet-byte) (symbol=? head 'bloblet-set-byte!)
             (symbol=? head 'bloblet-bytes))
         (parse-bloblet head (cdr items) a b))
        ((symbol=? head 'product) (e-product (parse-fields (cdr items)) a b))
        ((symbol=? head 'extract)
         (begin (arity items 3 "`(extract expression label)`" a b)
                (let ((l (label (nth items 2)))) (e-extract (parse-exp (nth items 1)) l a b))))
        ((symbol=? head 'sum)
         (begin (arity items 3 "`(sum tag expression)`" a b)
                (let ((t (label (nth items 1)))) (e-sum t (parse-exp (nth items 2)) a b))))
        ((symbol=? head 'tagcase)
         (begin (at-least items 2 "`(tagcase expression (tag name body …) …)`" a b)
                (let ((scrutinee (parse-exp (nth items 1))))
                  (e-tagcase scrutinee (parse-arms (drop items 2)) (parse-else (drop items 2)) a b))))
        ((symbol=? head 'quote)
         (if (and (= (len items) 2) (syn-symbol? (nth items 1)))
             (e-sym (syn-symbol (nth items 1)) a b)
             (pfail-at "only a symbol can be quoted: `'name`" a b)))
        ((symbol=? head 'prompt)
         (begin (arity items 4 "`(prompt tag body handler)`" a b)
                (e-prompt (parse-exp (nth items 1)) (parse-exp (nth items 2)) (parse-exp (nth items 3)) a b)))
        (else (let ((f (parse-exp (car items)))) (e-app f (parse-exps (cdr items)) a b))))))
  (parse-letrec-bindings (subr (maxeff parses spin) ((listof syn finite)) (listof (productof (1 symbol) (2 syn) (3 exp)) finite))
    (lambda (bs)
      (if (null? bs)
          nil
          (let ((parts (syn-items (car bs) "a letrec binding")))
            (if (= (len parts) 3)
                (let* ((name (syn-symbol (car parts))) (init (parse-exp (nth parts 2))))
                  (cons (product (1 name) (2 (nth parts 1)) (3 init)) (parse-letrec-bindings (cdr bs))))
                (pfail "a letrec binding is `(name type expression)`" (car bs)))))))
  ;; `(let ((name expression) …) …)`; `()` is no bindings.
  (parse-let-bindings (subr (maxeff parses spin) ((listof syn finite)) (listof (productof (1 symbol) (2 exp)) finite))
    (lambda (bs)
      (if (null? bs)
          nil
          (let ((parts (syn-items (car bs) "a let binding")))
            (if (= (len parts) 2)
                (let* ((name (syn-symbol (car parts))) (init (parse-exp (nth parts 1))))
                  (cons (product (1 name) (2 init)) (parse-let-bindings (cdr bs))))
                (pfail "a let binding is `(name expression)`" (car bs)))))))
  ;; `let*`: nested one-binding `let`s, each spanning its binding.
  (parse-let* (subr (maxeff parses spin) ((listof syn finite) exp) exp)
    (lambda (bs body)
      (if (null? bs)
          body
          (let ((parts (syn-items (car bs) "a let* binding")))
            (if (= (len parts) 2)
                (let* ((name (syn-symbol (car parts)))
                       (init (parse-exp (nth parts 1)))
                       (inner (parse-let* (cdr bs) body)))
                  (e-let (the (listof (productof (1 symbol) (2 exp)) finite) (cons (product (1 name) (2 init)) nil))
                         inner (syn-start (car bs)) (syn-end (car bs))))
                (pfail "a let* binding is `(name expression)`" (car bs)))))))
  ;; `(cond (test e …) … (else e …))`: nested `if`s, each spanning its clause.
  (parse-cond (subr (maxeff parses spin) ((listof syn finite) int int) exp)
    (lambda (clauses a b)
      (cond ((null? clauses) (pfail-at "a `cond` needs at least an `else` clause" a b))
            (else
             (let* ((c (car clauses)) (parts (syn-items c "a cond clause")))
               (if (null? (cdr clauses))
                   (if (symbol=? (syn-head (car parts)) 'else)
                       (parse-body (cdr parts) (syn-start c) (syn-end c))
                       (pfail "a `cond` must end with an `else` clause: FX has no unspecified value" c))
                   (if (null? parts)
                       (pfail "a cond clause is `(test expression …)`" c)
                       (let* ((test (parse-exp (car parts)))
                              (then (parse-body (cdr parts) (syn-start c) (syn-end c)))
                              (rest (parse-cond (cdr clauses) a b)))
                         (e-if test then rest (syn-start c) (syn-end c))))))))))
  ;; `(and a b …)`: `(if a (and b …) #f)`, and `(and)` is `#t`.
  (parse-and (subr (maxeff parses spin) ((listof syn finite) int int) exp)
    (lambda (xs a b)
      (cond ((null? xs) (e-bool #t a b))
            ((null? (cdr xs)) (parse-exp (car xs)))
            (else (let* ((x (parse-exp (car xs))) (rest (parse-and (cdr xs) a b)))
                    (e-if x rest (e-bool #f a b) a b))))))
  ;; `(or a b …)`: `(if a #t (or b …))`, and `(or)` is `#f`.
  (parse-or (subr (maxeff parses spin) ((listof syn finite) int int) exp)
    (lambda (xs a b)
      (cond ((null? xs) (e-bool #f a b))
            ((null? (cdr xs)) (parse-exp (car xs)))
            (else (let* ((x (parse-exp (car xs))) (rest (parse-or (cdr xs) a b)))
                    (e-if x (e-bool #t a b) rest a b))))))
  (parse-bloblet (subr (maxeff parses spin) (symbol (listof syn finite) int int) exp)
    (lambda (op args a b)
      (let ((n (len args)))
        (cond ((and (symbol=? op 'make-bloblet) (>= n 1)) (e-bloblet op -1 (parse-exps args) a b))
              ((and (symbol=? op 'rmake-bloblet) (>= n 2)) (e-bloblet op -1 (parse-exps args) a b))
              ((and (symbol=? op 'bloblet-ref) (= n 2))
               (let* ((i (field-index (nth args 1))) (x (parse-exp (car args))))
                 (e-bloblet op i (the (listof exp finite) (cons x nil)) a b)))
              ((and (symbol=? op 'bloblet-set!) (= n 3))
               (let* ((i (field-index (nth args 1))) (x (parse-exp (car args))) (v (parse-exp (nth args 2))))
                 (e-bloblet op i (the (listof exp finite) (cons x (cons v nil))) a b)))
              ((or (and (symbol=? op 'bloblet-freeze) (= n 1)) (and (symbol=? op 'bloblet-byte) (= n 2))
                   (and (symbol=? op 'bloblet-set-byte!) (= n 3)) (and (symbol=? op 'bloblet-bytes) (= n 1)))
               (e-bloblet op -1 (parse-exps args) a b))
              (else (pfail-at (string-append "`(" (string-append (symbol->string op) " …)`")) a b))))))
  (parse-fields (subr (maxeff parses spin) ((listof syn finite)) (listof (productof (1 symbol) (2 exp)) finite))
    (lambda (ps)
      (if (null? ps)
          nil
          (let ((pair (syn-items (car ps) "`(label expression)`")))
            (if (= (len pair) 2)
                (let* ((l (label (car pair))) (e (parse-exp (nth pair 1))))
                  (cons (product (1 l) (2 e)) (parse-fields (cdr ps))))
                (pfail "`(product (label expression) …)`" (car ps)))))))
  ;; The arms of a `tagcase` other than `else`.
  (parse-arms (subr (maxeff parses spin) ((listof syn finite)) (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) finite))
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
                          (ns (if fields (parse-names (syn-items bind "the names an arm binds")) (the names (cons (syn-symbol bind) nil))))
                          (body (parse-body (drop parts 2) (syn-start c) (syn-end c))))
                     (cons (product (1 tag) (2 fields) (3 ns) (4 body)) (parse-arms (cdr cs))))))))))
  ;; The `else` arm, as a list of none or one.
  (parse-else (subr (maxeff parses spin) ((listof syn finite)) (listof (productof (1 symbol) (2 exp)) finite))
    (lambda (cs)
      (cond ((null? cs) nil)
            ((arm-else? (car cs))
             (let* ((c (car cs)) (parts (syn-items c "a tagcase arm")))
               (if (< (len parts) 3)
                   (pfail "a tagcase arm needs a body" c)
                   (if (syn-symbol? (nth parts 1))
                       (let* ((y (syn-symbol (nth parts 1))) (body (parse-body (drop parts 2) (syn-start c) (syn-end c))))
                         (cons (product (1 y) (2 body)) nil))
                       (pfail "`else` binds one name" (nth parts 1))))))
            (else (parse-else (cdr cs)))))))

;; A `define-rec`'s bindings, as a `letrec`'s are.
(define parse-rec-bindings (subr (maxeff parses spin) ((listof syn finite)) (listof (productof (1 symbol) (2 syn) (3 exp)) finite))
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((parts (syn-items (car bs) "a define-rec binding")))
          (if (= (len parts) 3)
              (let* ((name (syn-symbol (car parts))) (init (parse-exp (nth parts 2))))
                (cons (product (1 name) (2 (nth parts 1)) (3 init)) (parse-rec-bindings (cdr bs))))
              (pfail "a define-rec binding is `(name type lambda)`" (car bs)))))))

;;; ------------------------------------------------------------- top level

(define parse-top (subr (maxeff parses spin) (syn) top)
  (lambda (s)
    (let ((head (tagcase s (lst (items d a b) (if (null? items) '|()| (syn-head (car items)))) (else x '|()|))))
      (cond ((symbol=? head 'define)
             (let* ((items (syn-items s "a definition")) (n (len items)))
               (cond ((= n 4)
                      (let ((name (syn-symbol (nth items 1))))
                        (t-define name (the syns-a (cons (nth items 2) nil)) (parse-exp (nth items 3)) (syn-start s) (syn-end s))))
                     ((= n 3)
                      (let ((name (syn-symbol (nth items 1))))
                        (t-define name (the syns-a nil) (parse-exp (nth items 2)) (syn-start s) (syn-end s))))
                     (else (pfail "`(define name type expression)` or `(define name expression)`" s)))))
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
             (t-private-regions (keep (cdr (syn-items s "private-regions"))) (syn-start s) (syn-end s)))
            (else (t-exp (parse-exp s)))))))

;;; FX-91's `(define-datatype name (tag type …) …)`, expanded as the Rust
;;; reader expands it (`top.rs`): a sum of products, each variant's members
;;; labelled from 1, and a constructor per tag, `(tag e …)`. What it makes
;;; is written where the form is.

(define datatype? (subr (read @s) (syn) bool)
  (lambda (s) (tagcase s (lst (items d a b) (and (not (null? items)) (symbol=? (syn-head (car items)) 'define-datatype))) (else x #f))))

(define mk-symbol (subr pure (string int int) syn) (lambda (n a b) (atom (datum-symbol n) a b)))
(define mk-int (subr pure (int int int) syn) (lambda (i a b) (atom (datum-int i) a b)))
(define syn-datums (subr (read @s) ((listof syn finite)) (listof datum finite))
  (lambda (xs) (if (null? xs) nil (cons (syn->datum (car xs)) (syn-datums (cdr xs))))))
(define mk-list (subr (read @s) ((listof syn finite) int int) syn)
  (lambda (items a b) (lst items (datum-list (syn-datums items)) a b)))

;; `(1 m1) (2 m2) …`, from `i`.
(define dt-labelled (subr (maxeff (read @s) (alloc @s)) ((listof syn finite) int int int) (listof syn finite))
  (lambda (ms i a b)
    (if (null? ms)
        nil
        (let* ((pair (mk-list (cons (mk-int i a b) (cons (car ms) nil)) a b)) (rest (dt-labelled (cdr ms) (+ i 1) a b)))
          (cons pair rest)))))
(define dt-arms (subr parses ((listof syn finite) int int) (listof syn finite))
  (lambda (vs a b)
    (if (null? vs)
        nil
        (let* ((v (car vs)) (parts (syn-items v "a variant")))
          (if (or (null? parts) (not (syn-symbol? (car parts))))
              (pfail "a variant is `(tag type …)`" v)
              (let* ((prod (mk-list (cons (mk-symbol "productof" a b) (dt-labelled (cdr parts) 1 a b)) a b))
                     (arm (mk-list (cons (car parts) (cons prod nil)) a b))
                     (rest (dt-arms (cdr vs) a b)))
                (cons arm rest)))))))
(define dt-params (subr (read @s) ((listof syn finite) int) (listof (productof (1 symbol) (2 syns-a)) finite))
  (lambda (ms i)
    (if (null? ms)
        nil
        (cons (product (1 (string->symbol (string-append "%x" (int->string i)))) (2 (the syns-a nil))) (dt-params (cdr ms) (+ i 1))))))
(define dt-fields (subr (read @s) ((listof syn finite) int int int) (listof (productof (1 symbol) (2 exp)) finite))
  (lambda (ms i a b)
    (if (null? ms)
        nil
        (cons (product (1 (string->symbol (int->string i))) (2 (e-var (string->symbol (string-append "%x" (int->string i))) a b)))
              (dt-fields (cdr ms) (+ i 1) a b)))))
;; Each constructor: of type `(subr pure (member …) used)`, where `used` is
;; the type as it is used, `name` or `(name param …)`; polymorphic in the
;; parameters if there are any (`family?`).
(define dt-constructors (subr parses (syn bool (listof syn finite) (listof syn finite) int int) (listof top finite))
  (lambda (used family? params vs a b)
    (if (null? vs)
        nil
        (let* ((parts (syn-items (car vs) "a variant"))
               (tag (car parts))
               (members (cdr parts))
               (mono (mk-list (cons (mk-symbol "subr" a b) (cons (mk-symbol "pure" a b) (cons (mk-list members a b) (cons used nil)))) a b))
               (ty (if family? (mk-list (cons (mk-symbol "poly" a b) (cons (mk-list params a b) (cons mono nil))) a b) mono))
               (body (e-sum (syn-symbol tag) (e-product (dt-fields members 1 a b) a b) a b))
               (ctor (t-define (syn-symbol tag) (the syns-a (cons ty nil)) (e-lambda (dt-params members 1) body a b) a b))
               (rest (dt-constructors used family? params (cdr vs) a b)))
          (cons ctor rest)))))
;; The parameters' names, from `(name kind) …`.
(define dt-param-names (subr parses ((listof syn finite)) (listof syn finite))
  (lambda (ps)
    (if (null? ps)
        nil
        (let ((p (syn-items (car ps) "a parameter")))
          (if (and (= (len p) 2) (syn-symbol? (car p)))
              (cons (car p) (dt-param-names (cdr ps)))
              (pfail "a parameter is `(name kind)`" (car ps)))))))
;; `(define-datatype name (tag type …) …)`, or with parameters,
;; `(define-datatype (name (param kind) …) …)`: a type family, which its
;; variants may mention with the same parameters.
(define parse-datatype (subr parses (syn) (listof top finite))
  (lambda (s)
    (let* ((items (syn-items s "a datatype")) (a (syn-start s)) (b (syn-end s))
           (usage "`(define-datatype name (tag type …) …)`"))
      (if (< (len items) 3)
          (pfail usage s)
          (let* ((head (nth items 1))
                 (family? (not (syn-symbol? head)))
                 (hs (if family? (syn-items head "a datatype's name") (the (listof syn finite) nil)))
                 (name (cond ((not family?) head)
                             ((and (not (null? hs)) (syn-symbol? (car hs))) (car hs))
                             (else (pfail usage s))))
                 (params (if family? (cdr hs) (the (listof syn finite) nil)))
                 (used (if family? (mk-list (cons name (dt-param-names params)) a b) name))
                 (sum (mk-list (cons (mk-symbol "sumof" a b) (dt-arms (drop items 2) a b)) a b))
                 (ctors (dt-constructors used family? params (drop items 2) a b)))
            (cons (t-define-type head sum a b) ctors))))))

(define append-tops (subr pure ((listof top finite) (listof top finite)) (listof top finite))
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (append-tops (cdr xs) ys)))))

;; `(define-generative head rep)`: the form, and its two conversions, each
;; the identity: `(define up-name (poly (param …) (subr pure (rep) (name p
;; …))) (lambda (x) x))`, and `down-name` the other way.
(define generative? (subr (read @s) (syn) bool)
  (lambda (s) (tagcase s (lst (items d a b) (and (not (null? items)) (symbol=? (syn-head (car items)) 'define-generative))) (else x #f))))
;; The parameters as binders, variance left out, and their names.
(define gen-binders (subr parses ((listof syn finite) int int) (listof syn finite))
  (lambda (ps a b)
    (if (null? ps)
        nil
        (let ((p (syn-items (car ps) "a parameter")))
          (if (>= (len p) 2)
              (cons (mk-list (cons (car p) (cons (nth p 1) nil)) a b) (gen-binders (cdr ps) a b))
              (pfail "a parameter is `(name kind)`, `(name kind +)` or `(name kind -)`" (car ps)))))))
(define gen-names (subr parses ((listof syn finite)) (listof syn finite))
  (lambda (bs) (if (null? bs) nil (cons (car (syn-items (car bs) "a parameter")) (gen-names (cdr bs))))))
(define parse-generative (subr parses (syn) (listof top finite))
  (lambda (s)
    (let* ((items (syn-items s "a generative type")) (a (syn-start s)) (b (syn-end s))
           (usage "`(define-generative name type)` or `(define-generative (name (param kind) …) type)`"))
      (if (not (= (len items) 3))
          (pfail usage s)
          (let* ((head (nth items 1))
                 (rep (nth items 2))
                 (family? (tagcase head (lst (hs d ha hb) (not (null? hs))) (else x #f)))
                 (hs (if family? (syn-items head "a generative type's name") (the (listof syn finite) nil)))
                 (name (if family? (car hs) head))
                 (n (if (syn-symbol? name) (symbol->string (syn-symbol name)) (pfail usage s)))
                 (binders (if family? (gen-binders (cdr hs) a b) (the (listof syn finite) nil)))
                 (used (if family? (mk-list (cons name (gen-names binders)) a b) name))
                 (conv (lambda ((from syn) (to syn))
                         (let ((t (mk-list (cons (mk-symbol "subr" a b)
                                                 (cons (mk-symbol "pure" a b) (cons (mk-list (cons from nil) a b) (cons to nil))))
                                           a b)))
                           (if family? (mk-list (cons (mk-symbol "poly" a b) (cons (mk-list binders a b) (cons t nil))) a b) t))))
                 (identity (e-lambda (the (listof (productof (1 symbol) (2 syns-a)) finite) (cons (product (1 'x) (2 (the syns-a nil))) nil))
                                     (e-var 'x a b) a b))
                 (up (t-define (string->symbol (string-append "up-" n)) (the syns-a (cons (conv rep used) nil)) identity a b))
                 (down (t-define (string->symbol (string-append "down-" n)) (the syns-a (cons (conv used rep) nil)) identity a b)))
            (cons (t-define-generative head rep a b) (cons up (cons down nil))))))))

(define parse-tops (subr (maxeff parses spin) ((listof syn finite)) (listof top finite))
  (lambda (xs)
    (cond ((null? xs) nil)
          ((generative? (car xs)) (let* ((made (parse-generative (car xs))) (rest (parse-tops (cdr xs)))) (append-tops made rest)))
          ((datatype? (car xs)) (let* ((made (parse-datatype (car xs))) (rest (parse-tops (cdr xs)))) (append-tops made rest)))
          (else (let* ((t (parse-top (car xs))) (rest (parse-tops (cdr xs)))) (cons t rest))))))

;; The entry point: a program's forms, as read, to trees or an error. The
;; prompt catches every failure, but its tag is a global whose type names
;; @p, so the control effect stays in the type, as the reader's on @e do;
;; @p is this program's own, so that is still licensed.
(define parse-program (subr (maxeff parses spin) ((listof syn finite)) presult)
  (lambda (forms) (prompt parse-tag (p-ok (parse-tops forms)) (lambda (r) r))))
