;;; The FX-26 parser, in FX-26: expressions, and `(load-module "file")`
;;; (`docs/research/first-class-modules.md`, M7), as the Rust parser's
;;; `parse_load_module` reads it: the file's forms a module's items, as an
;;; inline module's are (`parse-module-items`: its `define-datatype`s
;;; expanded, its `define-generative`s left a module's own); one recursive
;;; group, since a module is an expression and a file's items hold them.
;;; After `parser.fx`.
;;;
;;; FX-26 code reads no files: the driver reads each file a program's
;;; `load-module`s name, with the reader written in FX-26, before the
;;; program is parsed (`loaded-files!`), as a system call would. A file's
;;; positions are its own, each moved past the program's by its base, a
;;; multiple of `load-base`, so that what is said of a place in it can say
;;; which file and where.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define parser-exps-module (module
;; What the driver read for each `load-module`, by where the form starts:
;; the file's base (0 if it could not be read or read), its path, why not
;; (`cannot read …`, or where in it reading failed), its forms, and its
;; text.
(define-type loaded-file
  (productof (1 int) (2 int) (3 string) (4 string) (5 syns-a) (6 string)))
(define-type loaded-files (listof loaded-file acyclic))
(define loaded (ref loaded-files @s) (new nil))
;; For a driver: what the program's `load-module`s read.
(define loaded-files! (subr (maxeff (read @globals) (write @s)) (loaded-files) unit)
  (lambda (fs) (set loaded fs)))
;; The positions of one file and the next apart.
(define load-base int 1000000000)

;; What was read for the `load-module` starting at `a`, in a list of one.
(define loaded-at (subr (maxeff (read @globals) (read @s)) (loaded-files int) loaded-files)
  (lambda (fs a)
    (cond ((null? fs) nil)
          ((= (extract (car fs) 1) a) (the loaded-files (cons (car fs) nil)))
          (else (loaded-at (cdr fs) a)))))
;; The file read at `base`, in a list of one.
(define loaded-based (subr (maxeff (read @globals) (read @s)) (loaded-files int) loaded-files)
  (lambda (fs base)
    (cond ((null? fs) nil)
          ((and (> base 0) (= (extract (car fs) 2) base)) (the loaded-files (cons (car fs) nil)))
          (else (loaded-based (cdr fs) base)))))

;; `s`, its positions moved by `base`.
(define-rec
  (syn-moved (subr (maxeff (read @globals) (read @s) (alloc @s) spin) (syn int) syn)
    (lambda (s base)
      (tagcase s
        (atom (d a b) (atom d (+ a base) (+ b base)))
        (lst (items d a b) (lst (syns-moved items base) d (+ a base) (+ b base)))
        (dotted (items t d a b)
          (dotted (syns-moved items base) (syn-moved t base) d (+ a base) (+ b base)))
        (vec (items d a b) (vec (syns-moved items base) d (+ a base) (+ b base))))))
  (syns-moved (subr (maxeff (read @globals) (read @s) (alloc @s) spin) (syns-a int) syns-a)
    (lambda (xs base)
      (if (null? xs) nil (cons (syn-moved (car xs) base) (syns-moved (cdr xs) base))))))

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
  (subr (maxeff (read @globals) (read @s) spin) (loaded-files int string int) string)
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
;; A module's item that says it was read from a file: its base, and path.
(define loaded-mark (subr (read @globals) (int string) mod-item)
  (lambda (base path) (mod-item-of base (string->symbol path) (the syns-a nil) nil)))
;; A module's item that says reading its file failed, and why: refused where
;; the module is checked, as the Rust checker refuses it where it parses
;; the form.
(define loaded-error (subr (read @globals) (string) mod-items)
  (lambda (m) (cons (mod-item-of -1 (string->symbol m) (the syns-a nil) nil) nil)))

;;; ------------------------------------------------------------ expressions
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
        ;; (`parse-loaded`).
        ((symbol=? head 'load-module)
         (begin (arity items 2 "`(load-module \"file\")`" a b)
                (if (syn-string? (nth items 1))
                    (e-module (parse-loaded (syn-string (nth items 1)) a b) a b)
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
              (else (pfail module-usage f))))))
  ;; `(load-module "path")`, at `a`..`b`: the module's items, after its mark;
  ;; or why it could not be read.
  (parse-loaded (subr (maxeff parses spin) (string int int) mod-items)
    (lambda (path a b)
      (let ((f (loaded-at (get loaded) a)))
        (cond
          ((null? f) (loaded-error (str3 "cannot read `" path "`: it was not read")))
          ((= (extract (car f) 2) 0) (loaded-error (extract (car f) 3)))
          (else
           (let* ((base (extract (car f) 2))
                  (forms (syns-moved (extract (car f) 5) base))
                  ;; The items, as a form's, out of the prompt that catches
                  ;; what is wrong in them.
                  (made (lambda () (t-exp (e-module (parse-module-items forms) a b))))
                  (r (prompt parse-tag (p-ok (cons (made) nil)) (lambda (r) r))))
             (tagcase r
               (p-err (m x y)
                 (if (>= x base)
                     (loaded-error (in-loaded (get loaded) base m x))
                     (pfail-at m x y)))
               (p-ok (ts)
                 (cons (loaded-mark base path) (module-items-of (car ts))))))))))))
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
            (else (pfail "`(define name type expression)` or `(define name expression)`" s))))))))

(define loaded (with parser-exps-module loaded))
(define loaded-files! (with parser-exps-module loaded-files!))
(define load-base (with parser-exps-module load-base))
(define in-loaded (with parser-exps-module in-loaded))
(define parse-exp (with parser-exps-module parse-exp))
(define parse-module-item (with parser-exps-module parse-module-item))
(define parse-rec-bindings (with parser-exps-module parse-rec-bindings))
(define parse-define (with parser-exps-module parse-define))
