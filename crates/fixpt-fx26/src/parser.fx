;;; The FX-26 parser, in FX-26 (PLAN.md §11, step 9a).
;;;
;;; What the eager reader read (`syn`, with positions) to an abstract syntax
;;; tree, with the Rust parser's desugarings (`crates/fixpt-fx26/src/parse.rs`),
;;; node for node and span for span, so the two can be compared. Descriptions
;;; (types, effects, regions, binders) are kept as the syntax they were
;;; written in: the evaluator and the compiler do not need them, and the
;;; checker written in FX-26 (step 10) will parse them.
;;;
;;; Compiled with the reader, as one program: `syn` is in the reader's region
;;; @s, which only this program can name. The trees are in @a, and a parse
;;; that fails aborts to a prompt in @p; both are this program's own, so
;;; `parse-program` is licensed as the reader's entry points are.

(private-regions @a @p)

;; What a parse may do: read what was read, build a tree, and give up.
(define-effect parses (maxeff (read @s) (read @a) (alloc @a) (goto @p)))

(define-type syns-a (listof syn @a))
(define-type names (listof symbol @a))

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
  (e-lambda (listof (productof (1 symbol) (2 syns-a)) @a) exp int int)
  (e-app exp (listof exp @a) int int)
  (e-plambda syn exp int int)
  (e-proj exp syns-a int int)
  (e-if exp exp exp int int)
  (e-letrec (listof (productof (1 symbol) (2 syn) (3 exp)) @a) exp int int)
  (e-let (listof (productof (1 symbol) (2 exp)) @a) exp int int)
  (e-begin (listof exp @a) int int)
  (e-prompt exp exp exp int int)
  (e-the syn exp int int)
  ;; A bloblet form, by name, with its field index, or -1.
  (e-bloblet symbol int (listof exp @a) int int)
  (e-product (listof (productof (1 symbol) (2 exp)) @a) int int)
  (e-extract exp symbol int int)
  (e-sum symbol exp int int)
  ;; Arms: the tag, whether it takes a product apart, the names, the body.
  (e-tagcase exp (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) @a)
             (listof (productof (1 symbol) (2 exp)) @a) int int))

;; A top-level form. A definition's type is a list of none or one.
(define-datatype top
  (t-define symbol syns-a exp int int)
  (t-define-type syn syn int int)
  (t-define-effect syn syn int int)
  (t-private-regions syns-a int int)
  (t-exp exp))

(define-datatype presult (p-ok (listof top @a)) (p-err string int int))

(define parse-tag (prompt-tag presult presult (maxeff (read @s) (read @a) (alloc @a)) @p)
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
  (lambda (s) (if (syn-symbol? s) (string->symbol (syn-name s)) (pfail "a name" s))))
;; `()`, which reads as an empty list.
(define syn-nil? (subr (read @s) (syn) bool)
  (lambda (s) (tagcase s (lst (items d a b) (null? items)) (else x #f))))
;; A proper list's items; `what`, when it is not one.
(define syn-items (subr parses (syn string) (listof syn @s))
  (lambda (s what)
    (tagcase s (lst (items d a b) items) (else x (pfail (string-append what ": expected a list") s)))))
(define syn-int (subr pure (syn) int)
  (lambda (s) (tagcase s (atom (d a b) (if (datum-int? d) (datum-int-value d) -1)) (else x -1))))

(define len (subr (read @s) ((listof syn @s)) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (len (cdr xs))))))
(define nth (subr parses ((listof syn @s) int) syn)
  (lambda (xs i) (if (= i 0) (car xs) (nth (cdr xs) (- i 1)))))
(define drop (subr (read @s) ((listof syn @s) int) (listof syn @s))
  (lambda (xs i) (if (= i 0) xs (drop (cdr xs) (- i 1)))))

;; A label or tag: a name, or a positive integer, which is its digits.
(define label (subr parses (syn) symbol)
  (lambda (s)
    (cond ((syn-symbol? s) (string->symbol (syn-name s)))
          ((> (syn-int s) 0) (string->symbol (int->string (syn-int s))))
          (else (pfail "a label is a name or a positive integer" s)))))

;;; ------------------------------------------------------------ expressions

(define parse-exps (subr parses ((listof syn @s)) (listof exp @a))
  (lambda (xs) (if (null? xs) nil (cons (parse-exp (car xs)) (parse-exps (cdr xs))))))

(define keep (subr (maxeff (read @s) (alloc @a)) ((listof syn @s)) syns-a)
  (lambda (xs) (if (null? xs) nil (cons (car xs) (keep (cdr xs))))))

;; One or more expressions, an implicit `begin` spanning `a`..`b`.
(define parse-body (subr parses ((listof syn @s) int int) exp)
  (lambda (forms a b)
    (cond ((null? forms) (pfail-at "an empty body" a b))
          ((null? (cdr forms)) (parse-exp (car forms)))
          (else (e-begin (parse-exps forms) a b)))))

(define parse-exp (subr parses (syn) exp)
  (lambda (s)
    (tagcase s
      (atom (d a b)
        (cond ((datum-int? d) (e-int (datum-int-value d) a b))
              ((datum-string? d) (e-str (datum-string-value d) a b))
              ((datum-bool? d) (e-bool (datum-bool-value d) a b))
              ((datum-char? d) (e-char (datum-char-value d) a b))
              ((datum-symbol? d)
               (let ((n (datum-symbol-name d)))
                 (cond ((string=? n "#t") (e-bool #t a b))
                       ((string=? n "#f") (e-bool #f a b))
                       ((string=? n "#u") (e-unit a b))
                       (else (e-var (datum->symbol d) a b)))))
              (else (pfail "not an expression in the FX-26 kernel" s))))
      (lst (items d a b)
        (if (null? items)
            (pfail "not an expression in the FX-26 kernel" s)
            (parse-form s items (syn-name (car items)) a b)))
      (else x (pfail "not an expression in the FX-26 kernel" s)))))

;; `(tag x …)` with `n` items, or fail with `shape`.
(define arity (subr parses ((listof syn @s) int string int int) unit)
  (lambda (items n shape a b) (if (= (len items) n) #u (pfail-at shape a b))))
(define at-least (subr parses ((listof syn @s) int string int int) unit)
  (lambda (items n shape a b) (if (< (len items) n) (pfail-at shape a b) #u)))

(define parse-form (subr parses (syn (listof syn @s) string int int) exp)
  (lambda (s items head a b)
    (cond
      ((string=? head "lambda")
       (begin (at-least items 3 "`(lambda ((name type) …) body …)`" a b)
              (e-lambda (parse-params (nth items 1)) (parse-body (drop items 2) a b) a b)))
      ((string=? head "plambda")
       (begin (at-least items 3 "`(plambda ((name kind) …) body …)`" a b)
              (e-plambda (nth items 1) (parse-body (drop items 2) a b) a b)))
      ((string=? head "proj")
       (begin (at-least items 2 "`(proj expression description …)`" a b)
              (if (null? (drop items 2)) (pfail-at "`proj` needs at least one description" a b) #u)
              (e-proj (parse-exp (nth items 1)) (keep (drop items 2)) a b)))
      ((string=? head "if")
       (begin (arity items 4 "`(if test then else)`" a b)
              (e-if (parse-exp (nth items 1)) (parse-exp (nth items 2)) (parse-exp (nth items 3)) a b)))
      ((string=? head "letrec")
       (begin (at-least items 3 "`(letrec ((name type expression) …) body …)`" a b)
              (e-letrec (parse-letrec-bindings (syn-items (nth items 1) "letrec bindings"))
                        (parse-body (drop items 2) a b) a b)))
      ((string=? head "let")
       (begin (at-least items 3 "`(let ((name expression) …) body …)`" a b)
              (e-let (parse-let-bindings (syn-items (nth items 1) "let bindings")) (parse-body (drop items 2) a b) a b)))
      ((string=? head "begin") (parse-body (cdr items) a b))
      ((string=? head "cond") (parse-cond (cdr items) a b))
      ((string=? head "and") (parse-and (cdr items) a b))
      ((string=? head "or") (parse-or (cdr items) a b))
      ((string=? head "let*")
       (begin (at-least items 3 "`(let* ((name expression) …) body …)`" a b)
              (parse-let* (syn-items (nth items 1) "let* bindings") (parse-body (drop items 2) a b))))
      ((string=? head "the")
       (begin (arity items 3 "`(the type expression)`" a b)
              (e-the (nth items 1) (parse-exp (nth items 2)) a b)))
      ((or (string=? head "make-bloblet") (string=? head "bloblet-ref") (string=? head "bloblet-set!")
           (string=? head "bloblet-freeze") (string=? head "bloblet-byte") (string=? head "bloblet-set-byte!")
           (string=? head "bloblet-bytes"))
       (parse-bloblet head (cdr items) a b))
      ((string=? head "product") (e-product (parse-fields (cdr items)) a b))
      ((string=? head "extract")
       (begin (arity items 3 "`(extract expression label)`" a b)
              (let ((l (label (nth items 2)))) (e-extract (parse-exp (nth items 1)) l a b))))
      ((string=? head "sum")
       (begin (arity items 3 "`(sum tag expression)`" a b)
              (let ((t (label (nth items 1)))) (e-sum t (parse-exp (nth items 2)) a b))))
      ((string=? head "tagcase")
       (begin (at-least items 2 "`(tagcase expression (tag name body …) …)`" a b)
              (let ((scrutinee (parse-exp (nth items 1))))
                (e-tagcase scrutinee (parse-arms (drop items 2)) (parse-else (drop items 2)) a b))))
      ((string=? head "quote")
       (if (and (= (len items) 2) (syn-symbol? (nth items 1)))
           (e-sym (syn-symbol (nth items 1)) a b)
           (pfail-at "only a symbol can be quoted: `'name`" a b)))
      ((string=? head "prompt")
       (begin (arity items 4 "`(prompt tag body handler)`" a b)
              (e-prompt (parse-exp (nth items 1)) (parse-exp (nth items 2)) (parse-exp (nth items 3)) a b)))
      (else (let ((f (parse-exp (car items)))) (e-app f (parse-exps (cdr items)) a b))))))

(define parse-params (subr parses (syn) (listof (productof (1 symbol) (2 syns-a)) @a))
  (lambda (ps)
    (if (syn-nil? ps)
        nil
        (letrec ((each (subr parses ((listof syn @s)) (listof (productof (1 symbol) (2 syns-a)) @a))
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

(define parse-letrec-bindings (subr parses ((listof syn @s)) (listof (productof (1 symbol) (2 syn) (3 exp)) @a))
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((parts (syn-items (car bs) "a letrec binding")))
          (if (= (len parts) 3)
              (let* ((name (syn-symbol (car parts))) (init (parse-exp (nth parts 2))))
                (cons (product (1 name) (2 (nth parts 1)) (3 init)) (parse-letrec-bindings (cdr bs))))
              (pfail "a letrec binding is `(name type expression)`" (car bs)))))))

;; `(let ((name expression) …) …)`; `()` is no bindings.
(define parse-let-bindings (subr parses ((listof syn @s)) (listof (productof (1 symbol) (2 exp)) @a))
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((parts (syn-items (car bs) "a let binding")))
          (if (= (len parts) 2)
              (let* ((name (syn-symbol (car parts))) (init (parse-exp (nth parts 1))))
                (cons (product (1 name) (2 init)) (parse-let-bindings (cdr bs))))
              (pfail "a let binding is `(name expression)`" (car bs)))))))

;; `let*`: nested one-binding `let`s, each spanning its binding.
(define parse-let* (subr parses ((listof syn @s) exp) exp)
  (lambda (bs body)
    (if (null? bs)
        body
        (let ((parts (syn-items (car bs) "a let* binding")))
          (if (= (len parts) 2)
              (let* ((name (syn-symbol (car parts)))
                     (init (parse-exp (nth parts 1)))
                     (inner (parse-let* (cdr bs) body)))
                (e-let (the (listof (productof (1 symbol) (2 exp)) @a) (cons (product (1 name) (2 init)) nil))
                       inner (syn-start (car bs)) (syn-end (car bs))))
              (pfail "a let* binding is `(name expression)`" (car bs)))))))

;; `(cond (test e …) … (else e …))`: nested `if`s, each spanning its clause.
(define parse-cond (subr parses ((listof syn @s) int int) exp)
  (lambda (clauses a b)
    (cond ((null? clauses) (pfail-at "a `cond` needs at least an `else` clause" a b))
          (else
           (let* ((c (car clauses)) (parts (syn-items c "a cond clause")))
             (if (null? (cdr clauses))
                 (if (string=? (syn-name (car parts)) "else")
                     (parse-body (cdr parts) (syn-start c) (syn-end c))
                     (pfail "a `cond` must end with an `else` clause: FX has no unspecified value" c))
                 (if (null? parts)
                     (pfail "a cond clause is `(test expression …)`" c)
                     (let* ((test (parse-exp (car parts)))
                            (then (parse-body (cdr parts) (syn-start c) (syn-end c)))
                            (rest (parse-cond (cdr clauses) a b)))
                       (e-if test then rest (syn-start c) (syn-end c))))))))))

;; `(and a b …)`: `(if a (and b …) #f)`, and `(and)` is `#t`.
(define parse-and (subr parses ((listof syn @s) int int) exp)
  (lambda (xs a b)
    (cond ((null? xs) (e-bool #t a b))
          ((null? (cdr xs)) (parse-exp (car xs)))
          (else (let* ((x (parse-exp (car xs))) (rest (parse-and (cdr xs) a b)))
                  (e-if x rest (e-bool #f a b) a b))))))

;; `(or a b …)`: `(if a #t (or b …))`, and `(or)` is `#f`.
(define parse-or (subr parses ((listof syn @s) int int) exp)
  (lambda (xs a b)
    (cond ((null? xs) (e-bool #f a b))
          ((null? (cdr xs)) (parse-exp (car xs)))
          (else (let* ((x (parse-exp (car xs))) (rest (parse-or (cdr xs) a b)))
                  (e-if x (e-bool #t a b) rest a b))))))

;; A bloblet form's field index: a literal, non-negative integer.
(define field-index (subr parses (syn) int)
  (lambda (s)
    (if (>= (syn-int s) 0) (syn-int s) (pfail "a field index is a literal, non-negative integer" s))))

(define parse-bloblet (subr parses (string (listof syn @s) int int) exp)
  (lambda (name args a b)
    (let ((n (len args)) (op (string->symbol name)))
      (cond ((and (string=? name "make-bloblet") (>= n 1)) (e-bloblet op -1 (parse-exps args) a b))
            ((and (string=? name "bloblet-ref") (= n 2))
             (let* ((i (field-index (nth args 1))) (x (parse-exp (car args))))
               (e-bloblet op i (the (listof exp @a) (cons x nil)) a b)))
            ((and (string=? name "bloblet-set!") (= n 3))
             (let* ((i (field-index (nth args 1))) (x (parse-exp (car args))) (v (parse-exp (nth args 2))))
               (e-bloblet op i (the (listof exp @a) (cons x (cons v nil))) a b)))
            ((or (and (string=? name "bloblet-freeze") (= n 1)) (and (string=? name "bloblet-byte") (= n 2))
                 (and (string=? name "bloblet-set-byte!") (= n 3)) (and (string=? name "bloblet-bytes") (= n 1)))
             (e-bloblet op -1 (parse-exps args) a b))
            (else (pfail-at (string-append "`(" (string-append name " …)`")) a b))))))

(define parse-fields (subr parses ((listof syn @s)) (listof (productof (1 symbol) (2 exp)) @a))
  (lambda (ps)
    (if (null? ps)
        nil
        (let ((pair (syn-items (car ps) "`(label expression)`")))
          (if (= (len pair) 2)
              (let* ((l (label (car pair))) (e (parse-exp (nth pair 1))))
                (cons (product (1 l) (2 e)) (parse-fields (cdr ps))))
              (pfail "`(product (label expression) …)`" (car ps)))))))

(define arm-else? (subr (read @s) (syn) bool)
  (lambda (c) (tagcase c (lst (items d a b) (and (not (null? items)) (string=? (syn-name (car items)) "else"))) (else x #f))))

;; The arms of a `tagcase` other than `else`.
(define parse-arms (subr parses ((listof syn @s)) (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) @a))
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

(define parse-names (subr parses ((listof syn @s)) names)
  (lambda (xs) (if (null? xs) nil (cons (syn-symbol (car xs)) (parse-names (cdr xs))))))

;; The `else` arm, as a list of none or one.
(define parse-else (subr parses ((listof syn @s)) (listof (productof (1 symbol) (2 exp)) @a))
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
          (else (parse-else (cdr cs))))))

;;; ------------------------------------------------------------- top level

(define parse-top (subr parses (syn) top)
  (lambda (s)
    (let ((head (tagcase s (lst (items d a b) (if (null? items) "" (syn-name (car items)))) (else x ""))))
      (cond ((string=? head "define")
             (let* ((items (syn-items s "a definition")) (n (len items)))
               (cond ((= n 4)
                      (let ((name (syn-symbol (nth items 1))))
                        (t-define name (the syns-a (cons (nth items 2) nil)) (parse-exp (nth items 3)) (syn-start s) (syn-end s))))
                     ((= n 3)
                      (let ((name (syn-symbol (nth items 1))))
                        (t-define name (the syns-a nil) (parse-exp (nth items 2)) (syn-start s) (syn-end s))))
                     (else (pfail "`(define name type expression)` or `(define name expression)`" s)))))
            ((string=? head "define-type")
             (let ((items (syn-items s "a type definition")))
               (if (= (len items) 3)
                   (t-define-type (nth items 1) (nth items 2) (syn-start s) (syn-end s))
                   (pfail "`(define-type name type)`" s))))
            ((string=? head "define-effect")
             (let ((items (syn-items s "an effect definition")))
               (if (= (len items) 3)
                   (t-define-effect (nth items 1) (nth items 2) (syn-start s) (syn-end s))
                   (pfail "`(define-effect name effect)`" s))))
            ((string=? head "private-regions")
             (t-private-regions (keep (cdr (syn-items s "private-regions"))) (syn-start s) (syn-end s)))
            (else (t-exp (parse-exp s)))))))

(define parse-tops (subr parses ((listof syn @s)) (listof top @a))
  (lambda (xs) (if (null? xs) nil (cons (parse-top (car xs)) (parse-tops (cdr xs))))))

;; The entry point: a program's forms, as read, to trees or an error. The
;; prompt catches every failure, but its tag is a global whose type names
;; @p, so the control effect stays in the type, as the reader's on @e do;
;; @p is this program's own, so that is still licensed.
(define parse-program (subr parses ((listof syn @s)) presult)
  (lambda (forms) (prompt parse-tag (p-ok (parse-tops forms)) (lambda (r) r))))
