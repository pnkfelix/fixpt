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

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
;; The parser's first part at these regions, the reader's types in it, and
;; what this file uses of them.
(define parser-module ((proj (load-module "fx26:parser.fx") rs re rm rc rp)))
(define forms-module ((proj (load-module "fx26:parser-forms.fx") rs re rm rc rp)))
(import forms-module process-form processes)
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted vec (type data syn))
(define syn->datum (with parser-module syn->datum))
(import parser-module parse-tag syn-start syn-end pfail pfail-at syn-symbol? syn-name syn-head
        syn-symbol syn-items len nth drop label keep arity big-literal mod-item-of with-includes
        any-include? hide-forms hide-form? hidden-marks item-in-includes datatype? expand-datatype
        import? expand-import e-var e-int e-bool e-str e-char e-float e-sym e-unit e-lambda e-app
        e-plambda e-proj e-if e-letrec e-let e-begin e-prompt e-letregion e-rlambda e-the
        e-convention e-bloblet e-product e-extract e-sum e-tagcase e-module e-with t-define t-exp
        p-ok p-err sym-true sym-false sym-unit at-least vlambda-usage parse-vparam region-form?
        confirm-length-k bloblet-form? syn-string? syn-string parse-params freeze-pair region-kind
        region-name-error one-let call-tmp standard-ref field-index bloblet-untagged? arm-else?
        arm-names identity-at one-syn param-head? param-desc-item mk-symbol quoted rec-names
        rec-types rec-inits module-usage loaded loaded-next-at in-loaded loaded-mark loaded-error
        loaded-params loaded-made
        (type syns-a exp top exp-list mod-item mod-items letrec-list let-list arm-list loaded-file)
        (effect parses))
;; A `case`'s data by halving (`parser.fx`).
(import parser-module case-tree-from case-sort-key case-sort case-entries-length case-exps-length
        case-key-at case-take case-drop case-mid shared-keys shared-pending input-key? shared-key?
        load-cycle in-loaded-as loading-keys input-items (type case-entry case-entries))
;;; ------------------------------------------------------------ expressions
;; Whether `s` mentions the name `n` anywhere, quoted or not.
(define syn-mentions? (->* (symbol syn) bool)
  (lambda (n s)
    (tagcase s
      (atom (d a b) (and (symbol? d) (symbol=? d n)))
      (lst (items d a b) (syns-mention? n items))
      (dotted (items t d a b) (or (syns-mention? n items) (syn-mentions? n t)))
      (vec (items d a b) (syns-mention? n items)))))
(define syns-mention? (->* (symbol syns-a) bool)
  (lambda (n ss) (and (not (null? ss)) (or (syn-mentions? n (car ss)) (syns-mention? n (cdr ss))))))
;; A name for an expansion's own variable that `forms` never mention:
;; `base`, else `base1`, `base2` and so on. Its scope is within the form,
;; and nothing refers to a name it does not write, so it captures nothing
;; and nothing captures it.
(define fresh-name (->* (string syns-a) symbol)
  (lambda (base forms) (fresh-from base forms 0)))
(define fresh-from (->* (string syns-a int) symbol)
  (lambda (base forms i)
    (let ((n (string->symbol (if (= i 0) base (string-append base (int->string i))))))
      (if (syns-mention? n forms) (fresh-from base forms (+ i 1)) n))))
;; The shapes `typecase` tests (`check.rs`'s `SHAPES`, those with a
;; standard predicate), and the predicate of each; `||` if not one.
(define typecase-predicate (->* (symbol) symbol)
  (lambda (s)
    (case s
      ((int) 'int?) ((char) 'char?) ((bool) 'bool?) ((nil) 'null?) ((pair) 'pair?)
      ((string) 'string?) ((symbol) 'symbol?) ((procedure) 'procedure?) ((bloblet) 'array?)
      ((f64) 'f64?) ((f32) 'f32?) ((box) 'ref?) ((sum) 'sum?) ((product) 'product?)
      ((vector) 'vector?) ((bytevector) 'bytevector?)
      (else '||))))
(define typecase-usage string "`(typecase expression (shape name body) … (else name body))`")
(define typecase-needs-else string "a `typecase` needs at least an `else` clause")
(define typecase-else string
  "a `typecase` must end with an `else` clause, `(else body)` or `(else name body)`")
(define typecase-shapes string
  (string-append "a shape `typecase` tests is one of "
                 "int, char, bool, nil, pair, string, symbol, procedure, bloblet, "
                 "f64, f32, box, sum, product, vector, bytevector"))
;; A `case` datum's kind (`TODO.md` §46): 0 an integer, 1 a character, 2
;; a string, 3 a symbol, 4 a boolean, and -1 none of these.
(define case-kind (->* (syn) int)
  (lambda (s)
    (tagcase s
      (atom (d a b)
        (cond ((or (datum-int? d) (int? d)) 0)
              ((char? d) 1)
              ((string? d) 2)
              ((bool? d) 4)
              ((symbol? d)
               (let ((n d))
                 (cond ((or (symbol=? n sym-true) (symbol=? n sym-false)) 4)
                       ((symbol=? n sym-unit) -1)
                       (else 3))))
              (else -1)))
      (else x -1))))
;; A boolean datum's value, read as a literal or as `#t`.
(define case-bool (->* (datum) bool)
  (lambda (d) (typecase d (bool b b) (symbol n (symbol=? n sym-true)) (else x #f))))
;; Whether two data of kind `k` are the same.
(define case-same? (->* (int syn syn) bool)
  (lambda (k s t)
    (let ((d (syn->datum s)) (e (syn->datum t)))
      (case k ((0) (and (int? d) (int? e) (= d e)))
              ((1) (and (char? d) (char? e) (char=? d e)))
              ((2) (and (string? d) (string? e) (string=? d e)))
              ((3) (and (symbol? d) (symbol? e) (symbol=? d e)))
              (else (bool=? (case-bool d) (case-bool e)))))))
(define case-seen? (->* (int syn syns-a) bool)
  (lambda (k s seen)
    (and (not (null? seen)) (or (case-same? k s (car seen)) (case-seen? k s (cdr seen))))))
;; A clause's data, checked against those before it, `seen`, last first;
;; and `seen` with them.
(define case-datums (->* (syns-a syns-a) syns-a)
  (lambda (data seen)
    (if (null? data)
        seen
        (let* ((d (car data)) (k (case-kind d)))
          (if (= k -1)
              (pfail "a `case` datum is an integer, a character, a string, a symbol or a boolean" d)
              #u)
          (if (and (not (null? seen)) (not (= k (case-kind (car seen)))))
              (pfail (string-append "a `case`'s data are all of one kind: integers, characters, "
                                    "strings, symbols or booleans")
                     d)
              #u)
          (if (case-seen? k d seen) (pfail "a datum appears twice in this `case`" d) #u)
          (case-datums (cdr data) (cons d seen))))))
;; The clauses before a `case`'s `else`, each `((datum …) expression …)`.
(define case-clauses (->* (syns-a syns-a) unit)
  (lambda (clauses seen)
    (if (null? (cdr clauses))
        #u
        (let* ((c (car clauses)) (parts (syn-items c "a case clause")))
          (if (null? parts) (pfail "a case clause is `((datum …) expression …)`" c) #u)
          (let ((data (syn-items (car parts) "a case clause's data, `(datum …)`")))
            (if (null? data) (pfail "a case clause has at least one datum" c) #u)
            (case-clauses (cdr clauses) (case-datums data seen)))))))
;; `(or t rest)`, spanning a clause.
(define case-or (->* (exp exp int int) exp)
  (lambda (t rest ca cb) (e-if t (e-bool #t ca cb 0) rest ca cb 0)))
;; The kind of the clauses' first datum, -1 if there is none.
(define case-clauses-kind (->* (syns-a) int)
  (lambda (clauses)
    (if (null? (cdr clauses))
        -1
        (case-kind (car (syn-items (car (syn-items (car clauses) "c")) "data"))))))
(define case-data-count (->* (syns-a) int)
  (lambda (clauses)
    (if (null? (cdr clauses))
        0
        (+ (len (syn-items (car (syn-items (car clauses) "c")) "data"))
           (case-data-count (cdr clauses))))))
;; Whether every datum has a sort value: integers only if fixnums.
(define case-all-keyed? (->* (int syns-a) bool)
  (lambda (k clauses)
    (or (not (= k 0)) (null? (cdr clauses))
        (and (case-fixnums? (syn-items (car (syn-items (car clauses) "c")) "data"))
             (case-all-keyed? k (cdr clauses))))))
(define case-fixnums? (->* (syns-a) bool)
  (lambda (ds) (or (null? ds) (and (datum-int? (syn->datum (car ds))) (case-fixnums? (cdr ds))))))
;; A `case`'s `else` clause, if its body is one atom: in a list of one.
(define case-atom-else (->* (syn) syns-a)
  (lambda (c)
    (let ((parts (cdr (syn-items c "a case clause"))))
      (if (and (not (null? parts)) (null? (cdr parts)))
          (tagcase (car parts) (atom (d x y) parts) (else z nil))
          nil))))
;; The entries' tests in turn, each giving its clause (or, `bodies` given,
;; its body); `m` (or `els`) for none.
(define case-leaf (->* (case-entries int exp-list exp int int) exp)
  (lambda (es m bodies els a b)
    (cond ((and (null? es) (null? bodies)) (e-int m a b 0))
          ((null? es) els)
          (else
           (let ((then (if (null? bodies)
                           (e-int (extract (car es) 3) a b 0)
                           (case-body-at bodies (extract (car es) 3)))))
             (e-if (extract (car es) 1) then (case-leaf (cdr es) m bodies els a b) a b 0))))))
;; The clause index of sorted entries, `by` halved against their values.
(define case-index
  (->* (exp case-entries int int exp-list exp int int) exp)
  (lambda (by es n m bodies els a b)
    (if (<= n 3)
        (case-leaf es m bodies els a b)
        (let ((mid (case-mid es n)))
          (if (= mid 0)
              (case-leaf es m bodies els a b)
              (e-if (e-app (standard-ref '< a b) (list by (e-int (case-key-at es mid) a b 0)) a b 0)
                    (case-index by (case-take es mid) mid m bodies els a b)
                    (case-index by (case-drop es mid) (- n mid) m bodies els a b)
                    a b 0))))))
;; The body of index `lo`..`hi` that `i` names, by halving.
(define case-pick (->* (exp exp-list int int int int) exp)
  (lambda (i bodies lo hi a b)
    (if (= lo hi)
        (case-body-at bodies lo)
        (let ((mid (quotient (+ (+ lo hi) 1) 2)))
          (e-if (e-app (standard-ref '< a b) (list i (e-int mid a b 0)) a b 0)
                (case-pick i bodies lo (- mid 1) a b)
                (case-pick i bodies mid hi a b)
                a b 0)))))
(define case-body-at (->* (exp-list int) exp)
  (lambda (es i) (if (= i 0) (car es) (case-body-at (cdr es) (- i 1)))))
;; Whether a `case`, `xs` its key and clauses, compares its key as it is:
;; a variable (not `#t`, `#f` or `#u`), with a clause before the `else`.
(define case-direct? (->* (syns-a) bool)
  (lambda (xs)
    (and (syn-symbol? (car xs)) (not (null? (cdr (cdr xs))))
         (let ((n (syn-head (car xs))))
           (not (or (symbol=? n sym-true) (symbol=? n sym-false) (symbol=? n sym-unit)))))))
;; A `case`'s last clause, which must be `else`.
(define case-else (->* (syn) unit)
  (lambda (c)
    (let ((parts (syn-items c "a case clause")))
      (if (and (not (null? parts)) (symbol=? (syn-head (car parts)) 'else))
          #u
          (pfail "a `case` must end with an `else` clause: FX has no unspecified value" c)))))
(define case-last (->* (syns-a) syn)
  (lambda (xs) (if (null? (cdr xs)) (car xs) (case-last (cdr xs)))))
(define-rec
  (parse-exps (->* (syns-a) exp-list)
    (lambda (xs) (if (null? xs) nil (cons (parse-exp (car xs)) (parse-exps (cdr xs))))))
  ;; One or more expressions, an implicit `begin` spanning `a`..`b`.
  (parse-body (->* (syns-a int int) exp)
    (lambda (forms a b)
      (cond ((null? forms) (pfail-at "an empty body" a b))
            ((null? (cdr forms)) (parse-exp (car forms)))
            (else (e-begin (parse-exps forms) a b 0)))))
  (parse-exp (->* (syn) exp)
    (lambda (s)
      (tagcase s
        (atom (d a b)
          (cond ((datum-int? d) (e-int d a b 0))
                ((int? d) (big-literal d a b))
                ((string? d) (e-str d a b 0))
                ((bool? d) (e-bool d a b 0))
                ((char? d) (e-char d a b 0))
                ((f64? d) (e-float d a b 0))
                ((symbol? d)
                 (let ((n d))
                   (cond ((symbol=? n sym-true) (e-bool #t a b 0))
                         ((symbol=? n sym-false) (e-bool #f a b 0))
                         ((symbol=? n sym-unit) (e-unit a b 0))
                         (else (e-var n a b 0)))))
                (else (pfail "not an expression in the FX-26 kernel" s))))
        (lst (items d a b)
          (if (null? items)
              (pfail "not an expression in the FX-26 kernel" s)
              (parse-form s items (syn-head (car items)) a b)))
        (else x (pfail "not an expression in the FX-26 kernel" s)))))
  (parse-form (->* (syn syns-a symbol int int) exp)
    (lambda (s items head a b)
      (case head
        ((lambda)
         (begin (at-least items 3 "`(lambda ((name type) …) body …)`" a b)
                (parse-lambda-at items 1 a b)))
        ((vlambda)
         (begin (at-least items 3 vlambda-usage a b)
                (let ((param (parse-vparam (nth items 1) a b)))
                  (e-app (e-var '%vlambda a b 0)
                         (cons (e-lambda (cons param nil) (parse-body (drop items 2) a b) a b 0)
                               nil)
                         a b 0))))
        ((rlambda)
         (begin (at-least items 3 "`(rlambda region ((name type) …) body …)`" a b)
                (let ((r (parse-exp (nth items 1))))
                  (e-rlambda r (parse-lambda-at items 2 a b) a b 0))))
        ((plambda)
         (begin (at-least items 3 "`(plambda ((name kind) …) body …)`" a b)
                (e-plambda (nth items 1) (parse-body (drop items 2) a b) a b 0)))
        ((proj)
         (begin (at-least items 2 "`(proj expression description …)`" a b)
                (if (null? (drop items 2))
                    (pfail-at "`proj` needs at least one description" a b)
                    #u)
                (e-proj (parse-exp (nth items 1)) (keep (drop items 2)) a b 0)))
        ((if)
         (begin (arity items 4 "`(if test then else)`" a b)
                (e-if (parse-nth items 1) (parse-nth items 2) (parse-nth items 3) a b 0)))
        ((letrec)
         (begin (at-least items 3 "`(letrec ((name type expression) …) body …)`" a b)
                (e-letrec (parse-letrec-bindings (syn-items (nth items 1) "letrec bindings"))
                          (parse-body (drop items 2) a b) a b 0)))
        ((let)
         (begin (at-least items 3 "`(let ((name expression) …) body …)`" a b)
                (e-let (parse-let-bindings (syn-items (nth items 1) "let bindings"))
                       (parse-body (drop items 2) a b) a b 0)))
        ((begin) (parse-body (cdr items) a b))
        ;; A syscall declared: its hidden global, whether the runtime has it
        ;; (`docs/research/syscalls.md`). Not of one name, the form, or what
        ;; is no name, is the name `syscall-available?`, which the checker
        ;; refuses as the Rust checker does the form.
        ((syscall-available?)
         (cond ((not (= (len items) 2)) (e-var 'syscall-available? a b 0))
               ((not (syn-symbol? (nth items 1)))
                (e-var 'syscall-available? (syn-start (nth items 1)) (syn-end (nth items 1)) 0))
               (else (e-var (string->symbol (string-append "%syscall-available:"
                                                           (syn-name (nth items 1))))
                            a b 0))))
        ;; Processes and `par` (`parser-forms.fx`).
        ((spawn spawn-monitored send receive self par race pselect icell-get icell-put!)
         (parse-exp (process-form pfail-at items (parse-loaded processes #f #f a b) a b)))
        ((cond) (parse-cond (cdr items) a b))
        ((case) (parse-case (cdr items) a b))
        ((typecase) (parse-typecase items a b))
        ((confirm-length)
         (let ((usage "`(confirm-length expression length (name body) else)`"))
           (begin
             (arity items 5 usage a b)
             ;; A natural literal, or a variable holding a `nat`.
             (let* ((n (nth items 2))
                    (k (confirm-length-k n))
                    (length (if (< k 0) (e-var (syn-symbol n) a b 0) (e-int k a b 0))))
               (parse-confirm items 3 usage "%confirm-value" 'length-is? 'certify-length
                              (the exp-list (cons length nil)) a b)))))
        ((acyclic)
         (let ((usage "`(acyclic expression (name body) else)`"))
           (begin
             (arity items 4 usage a b)
             (parse-confirm items 2 usage "%acyclic-value" 'acyclic? 'certify-acyclic nil a b))))
        ((confirm-nat)
         (let ((usage "`(confirm-nat expression (name body) else)`"))
           (begin
             (arity items 4 usage a b)
             (parse-confirm items 2 usage "%nat-value" 'nat? 'certify-nat nil a b))))
        ((and) (parse-and (cdr items) a b))
        ((or) (parse-or (cdr items) a b))
        ((let*)
         (begin (at-least items 3 "`(let* ((name expression) …) body …)`" a b)
                (parse-let* (syn-items (nth items 1) "let* bindings")
                            (parse-body (drop items 2) a b))))
        ((the)
         (begin (arity items 3 "`(the type expression)`" a b)
                (e-the (nth items 1) (parse-exp (nth items 2)) a b 0)))
        ((convention)
         (begin (arity items 3 "`(convention C expression)`" a b)
                (e-convention (nth items 1) (parse-exp (nth items 2)) a b 0)))
        ((product) (e-product (parse-fields (cdr items)) a b 0))
        ((extract)
         (begin (arity items 3 "`(extract expression label)`" a b)
                (let ((l (label (nth items 2))))
                  (e-extract (parse-exp (nth items 1)) l nil a b 0))))
        ((sum)
         (begin (arity items 3 "`(sum tag expression)`" a b)
                (let ((t (label (nth items 1)))) (e-sum t (parse-exp (nth items 2)) a b 0))))
        ((tagcase)
         (begin (at-least items 2 "`(tagcase expression (tag name body …) …)`" a b)
                (let ((scrutinee (parse-exp (nth items 1))) (arms (drop items 2)))
                  (e-tagcase scrutinee (parse-arms arms) (parse-else arms) nil a b 0))))
        ((quote)
         (begin (arity items 2 "`(quote datum)`" a b)
                (if (syn-symbol? (nth items 1))
                    (e-sym (syn-symbol (nth items 1)) a b 0)
                    (parse-exp (quoted (nth items 1) -1)))))
        ((quasiquote)
         (begin (arity items 2 "`(quasiquote datum)`" a b)
                (parse-exp (quoted (nth items 1) 1))))
        ((prompt)
         (begin (arity items 4 "`(prompt tag body handler)`" a b)
                (e-prompt (parse-nth items 1) (parse-nth items 2) (parse-nth items 3) a b 0)))
        ((module) (e-module (parse-module-items (cdr items)) a b 0))
        ;; `(extend e0 e1)` (`TODO.md` §69): a module of the two, made of
        ;; their values by the checker (`k-extended`), as `parse.rs`; `e1`
        ;; sees `e0`'s bindings, `(with %extend-0 e1)`, as FX-91's, made at
        ;; the form.
        ((extend)
         (begin (arity items 3 "`(extend module module)`" a b)
                (e-module (the mod-items
                            (list (mod-item-of 2 '%extend-0 nil (list (parse-nth items 1)))
                                  (mod-item-of 2 '%extend-1 nil
                                               (list (e-with '%extend-0 (parse-nth items 2)
                                                             a b 0)))))
                          a b 0)))
        ((load-module load-input)
         (let* ((input? (eq? head 'load-input))
                (usage (string-append "`(" (if input? "load-input" "load-module") " \"file\")`")))
           (begin (arity items 2 usage a b)
                  (if (syn-string? (nth items 1))
                      (parse-loaded (syn-string (nth items 1)) input? #f a b)
                      (pfail (string-append usage ": the file's name, as a string")
                             (nth items 1))))))
        ;; `(%loaded "key" "path")`: the module of the file `key` names, as a
        ;; hidden global's definition is (`parse_loaded`).
        ((%loaded)
         (begin (arity items 3 "`(%loaded \"key\" \"path\")`" a b)
                (parse-loaded (syn-string (nth items 2)) (input-key? (syn-string (nth items 1)))
                              #t a b)))
        ((with)
         (begin (at-least items 2 "`(with module body …)`" a b)
                (if (syn-symbol? (nth items 1))
                    (e-with (syn-symbol (nth items 1)) (parse-body (drop items 2) a b) a b 0)
                    (pfail "`with` opens a module named by a variable" (nth items 1)))))
        (else
         (cond ((region-form? head) (parse-region-form items head a b))
               ((bloblet-form? head) (parse-bloblet head (cdr items) a b))
               (else (let ((f (parse-exp (car items))))
                       (e-app f (parse-exps (cdr items)) a b 0))))))))
  ;; Item `i`, an expression.
  (parse-nth (->* (syns-a int) exp)
    (lambda (items i) (parse-exp (nth items i))))
  ;; A `lambda` of the parameters at `i` and the body after them.
  (parse-lambda-at (->* (syns-a int int int) exp)
    (lambda (items i a b)
      (e-lambda (parse-params (nth items i)) (parse-body (drop items (+ i 1)) a b) a b 0)))
  ;; `(letregion name body …)` and the other region forms.
  (parse-region-form (->* (syns-a symbol int int) exp)
    (lambda (items head a b)
      (begin (at-least items 2 (string-append "`(" (symbol->string head) " name body …)`") a b)
             ;; `(letfreeze (r p) body …)` freezes into place `p`;
             ;; `(letfreeze r body …)` into the heap.
             (let* ((given (nth items 1))
                    (pair (freeze-pair head given))
                    (name (if (null? pair) given (car pair)))
                    (into (if (null? pair) 'heap (syn-symbol (nth pair 1)))))
               (if (and (syn-symbol? name) (not (char=? (string-ref (syn-name name) 0) #\@)))
                   (e-letregion (region-kind head)
                                (syn-symbol name) into (parse-body (drop items 2) a b) a b 0)
                   (pfail (region-name-error head) name))))))
  ;; A confirming form, `(form e … (x body) else)` with its arm at `i`:
  ;; `(let ((tmp e)) (if (test tmp more …) (let ((x (cert tmp more …)))
  ;; body) else))`, `tmp` named `tmp-name`.
  (parse-confirm
    (->* (syns-a int string string symbol symbol exp-list int int) exp)
    (lambda (items i usage tmp-name test cert more a b)
      (let* ((arm (syn-items (nth items i) usage))
             (shaped (if (= (len arm) 2) #u (pfail usage (nth items i))))
             (x (if (syn-symbol? (car arm)) (syn-symbol (car arm)) (pfail "a name" (car arm))))
             (e (parse-exp (nth items 1)))
             (body (parse-exp (nth arm 1)))
             (els (parse-exp (nth items (+ i 1))))
             (tmp (fresh-name tmp-name items))
             (then (e-let (one-let x (call-tmp cert tmp more a b)) body a b 0)))
        (e-let (one-let tmp e) (e-if (call-tmp test tmp more a b) then els a b 0) a b 0))))
  (parse-letrec-bindings (->* (syns-a) letrec-list)
    (lambda (bs)
      (parse-typed-bindings bs "a letrec binding" "a letrec binding is `(name type expression)`")))
  ;; Bindings `(name type expression)`, a `letrec`'s or a `define-rec`'s:
  ;; each `what`, and `usage` when one is not.
  (parse-typed-bindings (->* (syns-a string string) letrec-list)
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
  (parse-let-bindings (->* (syns-a) let-list)
    (lambda (bs)
      (if (null? bs)
          nil
          (let ((parts (syn-items (car bs) "a let binding")))
            (if (= (len parts) 2)
                (let* ((name (syn-symbol (car parts))) (init (parse-exp (nth parts 1))))
                  (cons (product (1 name) (2 init)) (parse-let-bindings (cdr bs))))
                (pfail "a let binding is `(name expression)`" (car bs)))))))
  ;; `let*`: nested one-binding `let`s, each spanning its binding.
  (parse-let* (->* (syns-a exp) exp)
    (lambda (bs body)
      (if (null? bs)
          body
          (let ((parts (syn-items (car bs) "a let* binding")))
            (if (= (len parts) 2)
                (let* ((name (syn-symbol (car parts)))
                       (init (parse-exp (nth parts 1)))
                       (inner (parse-let* (cdr bs) body)))
                  (e-let (one-let name init) inner (syn-start (car bs)) (syn-end (car bs)) 0))
                (pfail "a let* binding is `(name expression)`" (car bs)))))))
  ;; `(cond (test e …) … (else e …))`: nested `if`s, each spanning its clause.
  (parse-cond (->* (syns-a int int) exp)
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
                         (e-if test then rest (syn-start c) (syn-end c) 0)))))))))
  ;; A `cond`'s last clause, `c`, which must be `else`.
  (parse-cond-else (->* (syn syns-a) exp)
    (lambda (c parts)
      (if (symbol=? (syn-head (car parts)) 'else)
          (parse-body (cdr parts) (syn-start c) (syn-end c))
          (pfail "a `cond` must end with an `else` clause: FX has no unspecified value" c))))
  ;; `(and a b …)`: `(if a (and b …) #f)`, and `(and)` is `#t`.
  (parse-and (->* (syns-a int int) exp)
    (lambda (xs a b)
      (cond ((null? xs) (e-bool #t a b 0))
            ((null? (cdr xs)) (parse-exp (car xs)))
            (else (let* ((x (parse-exp (car xs))) (rest (parse-and (cdr xs) a b)))
                    (e-if x rest (e-bool #f a b 0) a b 0))))))
  ;; `(or a b …)`: `(if a #t (or b …))`, and `(or)` is `#f`.
  (parse-or (->* (syns-a int int) exp)
    (lambda (xs a b)
      (cond ((null? xs) (e-bool #f a b 0))
            ((null? (cdr xs)) (parse-exp (car xs)))
            (else (let* ((x (parse-exp (car xs))) (rest (parse-or (cdr xs) a b)))
                    (e-if x (e-bool #t a b 0) rest a b 0))))))
  ;; `(typecase e (shape name body) … (else name body))` on a union's members
  ;; (`docs/research/logical-types.md`, L1): `(let ((%typecase-value e)) (if
  ;; (int? %typecase-value) (let ((name %typecase-value)) body) … else))`,
  ;; each arm's test its shape's standard predicate, which narrows the value
  ;; for the arm and those after it. The `else` is required, as `case`'s is.
  (parse-typecase (->* (syns-a int int) exp)
    (lambda (items a b)
      (cond ((< (len items) 2) (pfail-at typecase-usage a b))
            ((null? (cdr (cdr items))) (pfail-at typecase-needs-else a b))
            ;; A variable, which nothing assigns, is tested as it is, so
            ;; that what each test narrows it to holds of it after.
            ((case-direct? (cdr items))
             (parse-typecase-arms (drop items 2) (syn-head (nth items 1)) a b))
            (else
             (let* ((e (parse-exp (nth items 1))) (tmp (fresh-name "%typecase-value" items)))
               (e-let (one-let tmp e) (parse-typecase-arms (drop items 2) tmp a b) a b 0))))))
  (parse-typecase-arms (->* (syns-a symbol int int) exp)
    (lambda (arms tmp a b)
      (if (null? (cdr arms))
          ;; `(else body)`, or `(else name body)`, `name` the value as what
          ;; the arms leave it.
          (let* ((parts (syn-items (car arms) typecase-usage))
                 (n (len parts))
                 (shaped (if (or (= n 2) (= n 3)) #u (pfail typecase-else (car arms))))
                 (name (if (= n 3)
                           (if (syn-symbol? (nth parts 1))
                               (syn-symbol (nth parts 1))
                               (pfail "a name" (nth parts 1)))
                           '||))
                 (is-else (if (and (syn-symbol? (car parts))
                                   (symbol=? (syn-symbol (car parts)) 'else))
                              #u
                              (pfail typecase-else (car arms))))
                 (body (parse-exp (nth parts (- n 1)))))
            (if (= n 3) (e-let (one-let name (e-var tmp a b 0)) body a b 0) body))
          (let* ((parts (syn-items (car arms) typecase-usage))
                 (shaped (if (= (len parts) 3) #u (pfail typecase-usage (car arms))))
                 (shape (car parts))
                 (pred (if (syn-symbol? shape) (typecase-predicate (syn-symbol shape)) '||))
                 (known (if (symbol=? pred '||) (pfail typecase-shapes shape) #u))
                 (x (if (syn-symbol? (nth parts 1))
                        (syn-symbol (nth parts 1))
                        (pfail "a name" (nth parts 1))))
                 (body (parse-exp (nth parts 2)))
                 (rest (parse-typecase-arms (cdr arms) tmp a b)))
            (e-if (call-tmp pred tmp nil a b) (e-let (one-let x (e-var tmp a b 0)) body a b 0) rest
                  a b 0)))))
  ;; `(case key ((datum …) e …) … (else e …))` on atoms (`TODO.md` §46):
  ;; `(let ((%case-key key)) …)` and nested `if`s, each datum compared by
  ;; its kind's equality. The data are of one kind and distinct, and the
  ;; `else` is required, as `cond`'s is.
  (parse-case (->* (syns-a int int) exp)
    (lambda (xs a b)
      (cond ((null? xs)
             (pfail-at "`(case key ((datum …) expression …) … (else expression …))`" a b))
            ((null? (cdr xs)) (pfail-at "a `case` needs at least an `else` clause" a b))
            (else
             (begin (case-else (case-last (cdr xs)))
                    (let* ((kx (car xs)) (ka (syn-start kx)) (kb (syn-end kx)))
                      (if (case-direct? xs)
                          ;; A variable, which nothing assigns: compared as it is.
                          (begin (case-clauses (cdr xs) nil)
                                 (parse-case-body (e-var (syn-head kx) ka kb 0) xs a b))
                          (let ((key (parse-exp kx)) (k (fresh-name "%case-key" xs)))
                            (case-clauses (cdr xs) nil)
                            (e-let (one-let k key) (parse-case-body (e-var k ka kb 0) xs a b)
                                   a b 0)))))))))
  ;; A chain of tests, or, for many data of a kind that pays (`case-tree-from`)
  ;; all with a sort value, two searches (`case-tree`): as the Rust parser's.
  (parse-case-body (->* (exp syns-a int int) exp)
    (lambda (kv xs a b)
      (let* ((clauses (cdr xs)) (k (case-clauses-kind clauses)) (n (case-data-count clauses))
             (direct (and (not (null? (case-atom-else (case-last clauses))))
                          (= n (- (len clauses) 1)))))
        (if (and (>= n (case-tree-from k direct)) (case-all-keyed? k clauses))
            (case-tree kv xs (case-entries kv k clauses 0) k a b)
            (parse-case-arms kv clauses)))))
  ;; Each datum of the clauses before the `else`: its test, sort value, clause.
  (case-entries (->* (exp int syns-a int) case-entries)
    (lambda (kv k clauses c)
      (if (null? (cdr clauses))
          nil
          (case-entries-of kv k (syn-items (car (syn-items (car clauses) "c")) "data") c
                           (case-entries kv k (cdr clauses) (+ c 1))))))
  (case-entries-of (->* (exp int syns-a int case-entries) case-entries)
    (lambda (kv k data c rest)
      (if (null? data)
          rest
          (let ((d (car data)))
            (the case-entries
              (cons (product (1 (case-test kv d)) (2 (case-sort-key k d)) (3 c))
                    (case-entries-of kv k (cdr data) c rest)))))))
  ;; The clause's index by halving the sorted data, then its body by halving
  ;; the indices (`case_tree` in the Rust parser).
  (case-tree (->* (exp syns-a case-entries int int int) exp)
    (lambda (kv xs es k a b)
      (let* ((sorted (case-sort es nil))
             (bodies (case-bodies (cdr xs)))
             (m (- (case-exps-length bodies) 1))
             (hash (fresh-name "%case-hash" xs))
             (index (fresh-name "%case-index" xs))
             (by (if (= k 0) kv (e-var hash a b 0)))
             (n (case-entries-length sorted))
             (els (case-atom-else (case-last (cdr xs))))
             (tree (if (and (not (null? els)) (= n m))
                       ;; A clause per datum, an `else` of one atom: bodies at the leaves.
                       (case-index by sorted n m bodies (case-body-at bodies m) a b)
                       (let ((found (case-index by sorted n m nil (e-unit a b 0) a b)))
                         (e-let (one-let index found) (case-pick (e-var index a b 0) bodies 0 m a b)
                                a b 0)))))
        (if (= k 0)
            tree
            (let ((op (if (= k 2) 'string-hash 'symbol-name-hash)))
              (e-let (one-let hash (e-app (standard-ref op a b) (list kv) a b 0)) tree a b 0))))))
  ;; Each clause's body, first to last, the `else`'s last.
  (case-bodies (->* (syns-a) exp-list)
    (lambda (clauses)
      (if (null? clauses)
          nil
          (let* ((c (car clauses)) (parts (syn-items c "a case clause"))
                 (body (parse-body (cdr parts) (syn-start c) (syn-end c))))
            (the exp-list (cons body (case-bodies (cdr clauses))))))))
  (parse-case-arms (->* (exp syns-a) exp)
    (lambda (k clauses)
      (let* ((c (car clauses)) (parts (syn-items c "a case clause"))
             (ca (syn-start c)) (cb (syn-end c)))
        (if (null? (cdr clauses))
            (parse-body (cdr parts) ca cb)
            (let* ((test (case-tests k (syn-items (car parts) "data") ca cb))
                   (then (parse-body (cdr parts) ca cb)))
              (e-if test then (parse-case-arms k (cdr clauses)) ca cb 0))))))
  ;; `(if d1 #t (if d2 #t … dn))`, each `di` the key compared with a datum.
  (case-tests (->* (exp syns-a int int) exp)
    (lambda (key data ca cb)
      (let ((t (case-test key (car data))))
        (if (null? (cdr data)) t (case-or t (case-tests key (cdr data) ca cb) ca cb)))))
  (case-test (->* (exp syn) exp)
    (lambda (key d)
      (let* ((da (syn-start d)) (db (syn-end d)) (k (case-kind d))
             (eq (case k ((0) '=) ((1) 'char=?) ((2) 'string=?)
                         ((3) 'symbol=?) (else 'bool=?)))
             (lit (if (= k 3) (e-sym (syn-head d) da db 0) (parse-exp d))))
        (e-app (standard-ref eq da db) (list key lit) da db 0))))
  (parse-bloblet (->* (symbol syns-a int int) exp)
    (lambda (op args a b)
      (let ((n (len args)))
        (cond ((and (symbol=? op 'make-bloblet) (>= n 1))
               (e-bloblet op -1 (parse-exps args) nil a b 0))
              ((and (symbol=? op 'rmake-bloblet) (>= n 2))
               (e-bloblet op -1 (parse-exps args) nil a b 0))
              ((and (symbol=? op 'bloblet-ref) (= n 2))
               (let* ((i (field-index (nth args 1))) (x (parse-exp (car args))))
                 (e-bloblet op i (the exp-list (cons x nil)) nil a b 0)))
              ((and (symbol=? op 'bloblet-set!) (= n 3))
               (let* ((i (field-index (nth args 1)))
                      (x (parse-exp (car args)))
                      (v (parse-exp (nth args 2))))
                 (e-bloblet op i (list x v) nil a b 0)))
              ((bloblet-untagged? op n) (e-bloblet op -1 (parse-exps args) nil a b 0))
              (else (pfail-at (string-append "`(" (symbol->string op) " …)`") a b))))))
  (parse-fields (->* (syns-a) let-list)
    (lambda (ps)
      (if (null? ps)
          nil
          (let ((pair (syn-items (car ps) "`(label expression)`")))
            (if (= (len pair) 2)
                (let* ((l (label (car pair))) (e (parse-exp (nth pair 1))))
                  (cons (product (1 l) (2 e)) (parse-fields (cdr ps))))
                (pfail "`(product (label expression) …)`" (car ps)))))))
  ;; The arms of a `tagcase` other than `else`.
  (parse-arms (->* (syns-a) arm-list)
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
  (parse-arm-body (->* (syns-a syn) exp)
    (lambda (parts c) (parse-body (drop parts 2) (syn-start c) (syn-end c))))
  ;; The `else` arm, as a list of none or one.
  (parse-else (->* (syns-a) let-list)
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
  (parse-module-items (->* (syns-a) mod-items)
    (lambda (fs) (with-includes (parse-module-items-in fs (any-include? fs) #f))))
  ;; The same, each item's values in `(with %include …)` if `inc?`, each
  ;; hidden if `hid?` (`hidden-marks`).
  (parse-module-items-in (->* (syns-a bool bool) mod-items)
    (lambda (fs inc? hid?)
      (cond ((null? fs) nil)
            ;; A string: a comment, read past.
            ((syn-string? (car fs)) (parse-module-items-in (cdr fs) inc? hid?))
            ((hide-form? (car fs))
             (append (parse-module-items-in (hide-forms (car fs)) inc? #t)
                     (parse-module-items-in (cdr fs) inc? hid?)))
            ((datatype? (car fs))
             (parse-module-items-in (append (expand-datatype (car fs)) (cdr fs)) inc? hid?))
            ((import? (car fs))
             (parse-module-items-in (append (expand-import (car fs)) (cdr fs)) inc? hid?))
            (else (let* ((item (parse-module-item (car fs)))
                         (item (if inc? (item-in-includes item (car fs)) item))
                         (rest (parse-module-items-in (cdr fs) inc? hid?)))
                    (if hid? (hidden-marks item (car fs) rest) (cons item rest)))))))
  ;; `(define-generative t T)`, `(define-type d T)`, `(define x e)`, `(define
  ;; x T e)` or `(define-rec (f T e) …)`.
  (parse-module-item (->* (syn) mod-item)
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
              ;; `(include m)` (`TODO.md` §69): kind 9, its form kept.
              ((and (symbol=? head 'include) (= n 2))
               (mod-item-of 9 '%include (one-syn f) (list (parse-exp (nth parts 1)))))
              ((symbol=? head 'define-rec)
               (let ((bs (parse-typed-bindings (cdr parts) "`(name type expression)`"
                                               "`(define-rec (name type expression) …)`")))
                 (product (1 3) (2 (rec-names bs)) (3 (rec-types bs)) (4 (rec-inits bs)))))
              (else (pfail module-usage f))))))
  ;; `(load-module "path")` or, `input?`, `(load-input "path")`, at `a`..`b`:
  ;; the hidden global every load of its path is (`TODO.md` §68), the
  ;; first defining it, as the file loaded (`parse-load-file`), before the
  ;; form that loads it (`shared-pending`); a `load-input`'s, its one item.
  ;; What it makes is the form's, at `a`..`b`; the file's module, the whole
  ;; file's.
  (parse-loaded (->* (string bool bool int int) exp)
    (lambda (path input? here? a b)
      (let ((f (loaded-next-at a)))
        (if (null? f)
            (e-module (loaded-error (string-append "cannot read `" path "`: it was not read"))
                      a b 0)
            (let* ((key (string-append (if input? "input:" "") (extract (car f) 7)))
                   (name (string->symbol (string-append "%shared:" key)))
                   (cycle (load-cycle key path)))
              (if here?
                  ;; The hidden global's own definition: the file's module.
                  (begin (set shared-keys (cons key (get shared-keys)))
                         (parse-load-file (car f) path input? a b))
              (begin
                (cond ((not (string=? cycle "")) (pfail-at cycle a b))
                      ((< (extract (car f) 2) 0) #u)
                      ((shared-key? key (get shared-keys)) #u)
                      (else
                       (let* ((pushed (set loading-keys (cons (cons key path) (get loading-keys))))
                              (x (parse-load-file (car f) path input? a b)))
                         (begin (set loading-keys (cdr (get loading-keys)))
                                (set shared-keys (cons key (get shared-keys)))
                                (set shared-pending
                                     (cons (t-define name (the syns-a nil) x a b)
                                           (get shared-pending)))))))
                (if input?
                    (e-with name (e-var 'input a b 0) a b 0)
                    (e-var name a b 0)))))))))
  ;; File `f`, loaded at `a`..`b` as `path`: the module, its items after its
  ;; mark (`loaded-made` of it, for a file of parameters; for a
  ;; `load-input`, `input?`, its one form, the item `input`); or why it
  ;; could not be read. An error in the file, said with where in it, is at
  ;; the load's start, as Rust's `said_in` places it; one about reading it,
  ;; its text none, at the whole load.
  (parse-load-file (->* (loaded-file string bool int int) exp)
    (lambda (f path input? a b)
      (if (= (extract f 2) 0)
          (e-module (loaded-error (extract f 3)) a (if (string=? (extract f 6) "") b a) 0)
          (let* ((base (extract f 2))
                 (forms (extract f 5))
                 ;; The whole file, where no other expression is.
                 (end (+ base (string-length (extract f 6))))
                 ;; Its parameters and items, as a form's, out of the
                 ;; prompt that catches what is wrong in them.
                 (made (lambda ()
                         (if input?
                             (t-exp (e-module (cons (loaded-mark base path nil)
                                                    (parse-module-items (input-items forms a b)))
                                              base end 0))
                             (let* ((ps (loaded-params forms))
                                    (items (parse-module-items (if (null? ps) forms (cdr forms))))
                                    (m (e-module (cons (loaded-mark base path ps) items)
                                                 base end 0)))
                               (t-exp (if (null? ps)
                                          m
                                          (loaded-made ps m (syn-start (car forms))
                                                       (syn-end (car forms)))))))))
                 (r (prompt parse-tag (p-ok (cons (made) nil)) (lambda (r) r))))
            (tagcase r
              (p-err (m x y)
                (if (>= x base)
                    (e-module (loaded-error (in-loaded-as (get loaded) base path m x)) a a 0)
                    (pfail-at m x y)))
              (p-ok (ts) (tagcase (car ts) (t-exp (x) x) (else y (e-module nil a b 0))))))))))
;; A `define-rec`'s bindings, as a `letrec`'s are.
(define parse-rec-bindings (->* (syns-a) letrec-list)
  (lambda (bs)
    (let ((usage "a define-rec binding is `(name type lambda)`"))
      (parse-typed-bindings bs "a define-rec binding" usage))))
