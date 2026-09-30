;;; DYNAMIC -- Obtained from Andrew Wright.
;;;
;;; Fritz's dynamic type inferencer, set up to run on itself.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/dynamic.scm),
;;; ported to FX-26. Larceny's input: 500 iterations of (doit
;;; "inputs/dynamic.data"), each reading that file (the inferencer's own
;;; source, 84 KB), parsing it into typed syntax trees while generating type
;;; constraints, normalizing them by union/find, and showing the program with
;;; its tagging and untagging operations, counted.
;;; Answer: ((218 . 455) (6 . 1892) (2204 . 446)).
;;;
;;; What the port changed, and why:
;;; - The inferencer is dynamically typed Scheme through and through: type
;;;   variables are cons cells (a union/find element: parent, rank, id and
;;;   definition), syntax trees are lists headed by integers, and a
;;;   polymorphic type holds a procedure. So every Scheme value here is one
;;;   datatype, `val`: the empty list, booleans, characters, integers,
;;;   strings, symbols, mutable pairs (`(pairof val val @heap)`), vectors
;;;   (arrays), the procedures stored in polymorphic types, and the
;;;   end-of-file object. A pair is a sum around an FX-26 pair: two objects
;;;   where Scheme has one. `vcar`, `vcdr`, `vset-car!`, the c...r
;;;   compositions, the type predicates, `vmemq`, `vassv`, `vlength`,
;;;   `vlist?`, `vreverse`, `vappend`, `map1`, `map2`, `for-each1`,
;;;   `for-each2` and `list->vector` are Scheme's (Larceny's `map` and
;;;   `for-each`, left to right), written over `val`; Scheme's truth is
;;;   `truthy?`, anything but #f.
;;; - Identity: `eqv?` of two type variables is `eq?` of their pairs, exact
;;;   on mutable pairs; of symbols, `eq?`; of integers, `=`.
;;; - The input file becomes the string `input-text`, the file verbatim (its
;;;   `"` escaped), and `open-input-file` and `read` become
;;;   `open-input-string` and `read-datum`, a small reader here for what the
;;;   file holds (lists, dotted pairs, quote, strings, integers, booleans,
;;;   symbols, comments). As in Larceny, each iteration reads it again, one
;;;   datum at a time, into fresh pairs.
;;; - Procedures of more than one argument that the original passes to
;;;   `forall2` ... `forall5` and `fix` are FX-26 procedures; only those a
;;;   polymorphic type keeps (`forall`'s) are `val`s.
;;; - `set!`-ed globals (`counter`, `global-constraints`,
;;;   `dynamic-top-level-env` and the tag counters) are refs. The syntax
;;;   operators (`null-const` ... `begin-command`) are integers, and `case`
;;;   on them a `cond` of `=`; `case` on symbols a `cond` of `is-sym?`. The
;;;   symbols the display code builds with are made once (`q-...`), as
;;;   Scheme's are constants.
;;; - `dynamic-top-level-env` starts empty rather than as `(global-env)`: it
;;;   is set again by every `doit` before use.
;;; - Definitions come before their uses (FX-26 has no forward references):
;;;   the parse actions and `ast-gen` come before the parser; the parser's
;;;   mutually recursive procedures are one `define-rec`.
;;; - Code that `doit` never reaches is left out: `ast-show`, `tast-show`
;;;   and their `*` forms, `tvar-show`, `type-show`, `tvar->string`,
;;;   `constr-show`, `glob-constr-show`, the environment show procedures,
;;;   `write-to-port`, `write-to-file`, `forall?`, `set-info!`,
;;;   `reset-def!`, and the REPL shorthands `pc`, `lc`, `n!`, `pt`.
;;;   `fix`'s error message does not show the types.
;;; - `error` takes a single message string, and the run stops there;
;;;   no error is reached.

(define-effect hs (maxeff (read @heap) (write @heap) (alloc @heap) spin))
(define-effect tvfun
  (maxeff hs
          (read (globals forall vproc counter gen-element gen-id gen-type ptype-con v-null
                         vcons vint vpair forall2 forall3 forall4 boolean boolean-con
                         convert-tvars gen-tvar null pair pair-con procedure procedure-con vcar
                         vcdr vlist2 vnull? vpair? dynamic vlist1 fix info list-type number
                         number-con set-def! tvar-def type-args type-con vcddr vset-cdr! array
                         vector-con vlist3))))

(define-datatype val
  (vnull)
  (vbool bool)
  (vchar char)
  (vint int)
  (vstr string)
  (vsym symbol)
  (vpair (pairof val val @heap))
  (vvec (arrayof val @heap))
  (vproc (subr tvfun (val) val))
  (veof))

(define v-null val (vnull))
(define v-false val (vbool #f))
(define v-true val (vbool #t))
(define v-eof val (veof))

;;;----------------------------------------------------------------------------
;;; Scheme's primitives, over `val`
;;;----------------------------------------------------------------------------

(define truthy? (subr pure (val) bool) (lambda (x) (tagcase x (vbool (b) b) (else z #t))))

(define vnull? (subr pure (val) bool) (lambda (x) (tagcase x (vnull () #t) (else z #f))))
(define vpair? (subr pure (val) bool) (lambda (x) (tagcase x (vpair (p) #t) (else z #f))))
(define vboolean? (subr pure (val) bool) (lambda (x) (tagcase x (vbool (b) #t) (else z #f))))
(define vchar? (subr pure (val) bool) (lambda (x) (tagcase x (vchar (c) #t) (else z #f))))
(define vnumber? (subr pure (val) bool) (lambda (x) (tagcase x (vint (n) #t) (else z #f))))
(define vstring? (subr pure (val) bool) (lambda (x) (tagcase x (vstr (s) #t) (else z #f))))
(define vsymbol? (subr pure (val) bool) (lambda (x) (tagcase x (vsym (s) #t) (else z #f))))
(define vvector? (subr pure (val) bool) (lambda (x) (tagcase x (vvec (v) #t) (else z #f))))
(define veof-object? (subr pure (val) bool) (lambda (x) (tagcase x (veof () #t) (else z #f))))

;; Whether `x` is the symbol `s`: `(eqv? x 's)`, as `case` compares.
(define is-sym? (subr pure (val symbol) bool)
  (lambda (x s) (tagcase x (vsym (t) (eq? t s)) (else z #f))))

(define eqv? (subr pure (val val) bool)
  (lambda (x y)
    (tagcase x
      (vnull () (tagcase y (vnull () #t) (else z #f)))
      (vbool (a) (tagcase y (vbool (b) (bool=? a b)) (else z #f)))
      (vchar (a) (tagcase y (vchar (b) (char=? a b)) (else z #f)))
      (vint (a) (tagcase y (vint (b) (= a b)) (else z #f)))
      (vstr (a) (tagcase y (vstr (b) (eq? a b)) (else z #f)))
      (vsym (a) (tagcase y (vsym (b) (eq? a b)) (else z #f)))
      (vpair (a) (tagcase y (vpair (b) (eq? a b)) (else z #f)))
      (vvec (a) (tagcase y (vvec (b) (eq? a b)) (else z #f)))
      (vproc (a) (tagcase y (vproc (b) (eq? a b)) (else z #f)))
      (veof () (tagcase y (veof () #t) (else z #f))))))

(define vint-of (subr pure (val) int)
  (lambda (x) (tagcase x (vint (n) n) (else z (error "not a number")))))

(define* vcons (subr (alloc @heap) (val val) val) (lambda (a b) (vpair (cons a b))))
(define vcar (subr (read @heap) (val) val)
  (lambda (x) (tagcase x (vpair (p) (car p)) (else z (error "car: not a pair")))))
(define vcdr (subr (read @heap) (val) val)
  (lambda (x) (tagcase x (vpair (p) (cdr p)) (else z (error "cdr: not a pair")))))
(define vset-car! (subr (write @heap) (val val) unit)
  (lambda (x y) (tagcase x (vpair (p) (set-car! p y)) (else z (error "set-car!: not a pair")))))
(define vset-cdr! (subr (write @heap) (val val) unit)
  (lambda (x y) (tagcase x (vpair (p) (set-cdr! p y)) (else z (error "set-cdr!: not a pair")))))
(define* vcaar (subr (read @heap) (val) val) (lambda (x) (vcar (vcar x))))
(define* vcadr (subr (read @heap) (val) val) (lambda (x) (vcar (vcdr x))))
(define* vcdar (subr (read @heap) (val) val) (lambda (x) (vcdr (vcar x))))
(define* vcddr (subr (read @heap) (val) val) (lambda (x) (vcdr (vcdr x))))
(define* vcaadr (subr (read @heap) (val) val) (lambda (x) (vcar (vcar (vcdr x)))))
(define* vcdadr (subr (read @heap) (val) val) (lambda (x) (vcdr (vcar (vcdr x)))))
(define* vcaddr (subr (read @heap) (val) val) (lambda (x) (vcar (vcdr (vcdr x)))))
(define* vcdddr (subr (read @heap) (val) val) (lambda (x) (vcdr (vcdr (vcdr x)))))

(define* vlist1 (subr (alloc @heap) (val) val) (lambda (a) (vcons a v-null)))
(define* vlist2 (subr (alloc @heap) (val val) val) (lambda (a b) (vcons a (vcons b v-null))))
(define* vlist3 (subr (alloc @heap) (val val val) val)
  (lambda (a b c) (vcons a (vcons b (vcons c v-null)))))
;; Scheme's `(list e ...)` of more elements, from an FX-26 list.
(define* vlist-of (subr (maxeff (alloc @heap) spin) ((listof val acyclic)) val)
  (lambda (l) (if (null? l) v-null (vcons (car l) (vlist-of (cdr l))))))

(define* vmemq (subr (maxeff (read @heap) spin) (val val) bool)
  (lambda (x l) (tagcase l (vpair (p) (if (eqv? x (car p)) #t (vmemq x (cdr p)))) (else z #f))))

(define* vassv (subr (maxeff (read @heap) spin) (val val) val)
  (lambda (x l)
    (tagcase l
      (vpair (p) (let ((b (car p))) (if (eqv? x (vcar b)) b (vassv x (cdr p)))))
      (else z v-false))))

(define* vlength (subr (maxeff (read @heap) spin) (val) int)
  (lambda (l)
    (letrec ((loop (subr (maxeff (read @heap) spin) (val int) int)
               (lambda (l n) (tagcase l (vpair (p) (loop (cdr p) (+ n 1))) (else z n)))))
      (loop l 0))))

(define* vlist? (subr (maxeff (read @heap) spin) (val) bool)
  (lambda (l) (tagcase l (vpair (p) (vlist? (cdr p))) (vnull () #t) (else z #f))))

(define* vreverse (subr hs (val) val)
  (lambda (l)
    (letrec ((loop (subr hs (val val) val)
               (lambda (l acc)
                 (tagcase l (vpair (p) (loop (cdr p) (vcons (car p) acc))) (else z acc)))))
      (loop l v-null))))

(define* vappend (subr hs (val val) val)
  (lambda (a b) (tagcase a (vpair (p) (vcons (car p) (vappend (cdr p) b))) (else z b))))

(define* map1 (poly ((e effect)) (subr (maxeff e hs) ((subr e (val) val) val) val))
  (plambda ((e effect))
    (lambda (f x)
      (tagcase x
        (vpair (p) (let* ((a (f (car p))) (b (map1 f (cdr p)))) (vcons a b)))
        (vnull () v-null)
        (else z (error "map: not a list"))))))

(define* map2
  (poly ((e effect)) (subr (maxeff e hs) ((subr e (val val) val) val val) val))
  (plambda ((e effect))
    (lambda (f x y)
      (if (and (vpair? x) (vpair? y))
          (let* ((a (f (vcar x) (vcar y))) (b (map2 f (vcdr x) (vcdr y)))) (vcons a b))
          (if (and (or (vnull? x) (vpair? x)) (or (vnull? y) (vpair? y)))
              v-null
              (error "map: not a list"))))))

(define* for-each1 (poly ((e effect)) (subr (maxeff e hs) ((subr e (val) val) val) unit))
  (plambda ((e effect))
    (lambda (f x)
      (tagcase x
        (vpair (p) (begin (f (car p)) (for-each1 f (cdr p))))
        (else z #u)))))

(define* for-each2 (poly ((e effect)) (subr (maxeff e hs) ((subr e (val val) val) val val) unit))
  (plambda ((e effect))
    (lambda (f x y)
      (if (and (vpair? x) (vpair? y))
          (begin (f (vcar x) (vcar y)) (for-each2 f (vcdr x) (vcdr y)))
          #u))))

(define* list->vector (subr hs (val) val)
  (lambda (l)
    (let ((v (the (arrayof val @heap) (make-array (vlength l) v-null))))
      (letrec ((fill (subr hs (val int) val)
                 (lambda (l i)
                   (tagcase l
                     (vpair (p) (begin (array-set! v i (car p)) (fill (cdr p) (+ i 1))))
                     (else z (vvec v))))))
        (fill l 0)))))

(define* vector->list (subr hs (val) val)
  (lambda (x)
    (tagcase x
      (vvec (v)
        (letrec ((loop (subr hs (int val) val)
                   (lambda (i acc) (if (< i 0) acc (loop (- i 1) (vcons (array-ref v i) acc))))))
          (loop (- (array-length v) 1) v-null)))
      (else z (error "vector->list: not a vector")))))

;;; `read`, from a string: a port is the text and a position in it.

(define-type port (productof (text string) (pos (ref int @heap))))

(define* open-input-string (subr (alloc @heap) (string) port)
  (lambda (s) (product (text s) (pos (new 0)))))

(define* read-datum (subr hs (port) val)
  (lambda (port)
    (let* ((s (extract port text))
           (pos (extract port pos))
           (n (string-length s)))
      (letrec ((peek (subr (read @heap) () char)
                 (lambda () (if (< (get pos) n) (string-ref s (get pos)) #\nul)))
               (advance (subr (maxeff (read @heap) (write @heap)) () unit)
                 (lambda () (set pos (+ (get pos) 1))))
               (skip (subr hs () unit)
                 (lambda ()
                   (let ((c (peek)))
                     (cond ((and (< (get pos) n) (char-whitespace? c)) (begin (advance) (skip)))
                           ((char=? c #\;) (begin (skip-line) (skip)))
                           (else #u)))))
               (skip-line (subr hs () unit)
                 (lambda ()
                   (if (or (>= (get pos) n) (char=? (peek) #\newline))
                       #u
                       (begin (advance) (skip-line)))))
               (delimiter? (subr (read @heap) (char) bool)
                 (lambda (c)
                   (or (>= (get pos) n) (char-whitespace? c) (char-in? c "()\";'"))))
               (token (subr hs ((listof char @heap)) (listof char @heap))
                 (lambda (acc)
                   (if (delimiter? (peek))
                       (reverse acc)
                       (let ((c (peek))) (begin (advance) (token (cons c acc)))))))
               (string-body (subr hs ((listof char @heap)) string)
                 (lambda (acc)
                   (let ((c (peek)))
                     (begin
                       (advance)
                       (cond ((char=? c #\") (list->string (reverse acc)))
                             ((char=? c #\\)
                              (let ((e (peek))) (begin (advance) (string-body (cons e acc)))))
                             (else (string-body (cons c acc))))))))
               (digits? (subr hs ((listof char @heap)) bool)
                 (lambda (l) (if (null? l) #t (and (char-numeric? (car l)) (digits? (cdr l))))))
               (atom (subr hs (string) val)
                 (lambda (t)
                   (let ((cs (the (listof char @heap) (string->list t))))
                     (cond ((string=? t "#t") v-true)
                           ((string=? t "#f") v-false)
                           ((and (not (null? cs)) (digits? cs)) (vint (parse-nat t 10)))
                           ((and (char=? (car cs) #\-) (not (null? (cdr cs))) (digits? (cdr cs)))
                            (vint (- 0 (parse-nat (substring t 1 (string-length t)) 10))))
                           (else (vsym (string->symbol t)))))))
               (datum (subr hs () val)
                 (lambda ()
                   (begin
                     (skip)
                     (let ((c (peek)))
                       (cond ((>= (get pos) n) v-eof)
                             ((char=? c #\() (begin (advance) (rest-of-list)))
                             ((char=? c #\')
                              (begin (advance) (vlist2 (vsym 'quote) (datum))))
                             ((char=? c #\") (begin (advance) (vstr (string-body nil))))
                             (else (atom (list->string (token nil)))))))))
               (rest-of-list (subr hs () val)
                 (lambda ()
                   (begin
                     (skip)
                     (let ((c (peek)))
                       (cond ((char=? c #\)) (begin (advance) v-null))
                             ((and (char=? c #\.)
                                   (< (+ (get pos) 1) n)
                                   (let ((d (string-ref s (+ (get pos) 1))))
                                     (or (char-whitespace? d) (char-in? d "()\";'"))))
                              (begin (advance)
                                     (let ((x (datum))) (begin (skip) (advance) x))))
                             (else (let ((x (datum))) (vcons x (rest-of-list))))))))))
        (datum)))))

;;;----------------------------------------------------------------------------
;;; Environment management
;;;----------------------------------------------------------------------------

;; environments are lists of pairs, the first component being the key

; bindings

;; generates a type binding, binding a symbol to a type variable
(define* gen-binding (subr (alloc @heap) (val val) val) (lambda (k v) (vcons k v)))

;; returns the key of a type binding
(define* binding-key (subr (read @heap) (val) val) (lambda (b) (vcar b)))

;; returns the tvariable of a type binding
(define* binding-value (subr (read @heap) (val) val) (lambda (b) (vcdr b)))

; environments

;; returns the empty environment
(define dynamic-empty-env val v-null)

;; extends env with a binding, which hides any other binding in env
;; for the same key (see dynamic-lookup)
;; returns the extended environment
(define* extend-env-with-binding (subr (alloc @heap) (val val) val)
  (lambda (env binding) (vcons binding env)))

;; extends environment env with environment ext-env
;; a binding for a key in ext-env hides any binding in env for
;; the same key (see dynamic-lookup)
;; returns the extended environment
(define* extend-env-with-env (subr hs (val val) val)
  (lambda (env ext-env) (vappend ext-env env)))

;; returns the first pair in env that matches the key; returns #f
;; if no such pair exists
(define* dynamic-lookup (subr (maxeff (read @heap) spin) (val val) val)
  (lambda (x l) (vassv x l)))

;;;----------------------------------------------------------------------------
;;; Implementation of Union/find data structure in Scheme
;;;----------------------------------------------------------------------------

;; for union/find the following attributes are necessary: rank, parent
;; (see Tarjan, "Data structures and network algorithms", 1983)
;; In the Scheme realization an element is represented as a single
;; cons cell; its address is the element itself; the car field contains
;; the parent, the cdr field is an address for a cons
;; cell containing the rank (car field) and the information (cdr field)

;; generates a new element: the parent field is initialized to '(),
;; the rank field to 0
(define* gen-element (subr (alloc @heap) (val) val)
  (lambda (info) (vcons v-null (vcons (vint 0) info))))

;; returns the information stored in an element
(define* info (subr (read @heap) (val) val) (lambda (l) (vcddr l)))

;; finds the class representative of elem and sets the parent field
;; directly to the class representative (a class representative has
;; '() as its parent)
(define* find! (subr (maxeff (read @heap) (write @heap) spin) (val) val)
  (lambda (elem)
    (let ((p-elem (vcar elem)))
      (if (vnull? p-elem)
          elem
          (let ((rep-elem (find! p-elem)))
            (begin (vset-car! elem rep-elem)
                   rep-elem))))))

;; links class elements by rank
;; they must be distinct class representatives
;; returns the class representative of the merged equivalence classes
(define* link! (subr (maxeff (read @heap) (write @heap)) (val val) val)
  (lambda (elem-1 elem-2)
    (let ((rank-1 (vint-of (vcadr elem-1)))
          (rank-2 (vint-of (vcadr elem-2))))
      (cond
       ((= rank-1 rank-2)
        (begin (vset-car! (vcdr elem-2) (vint (+ rank-2 1)))
               (vset-car! elem-1 elem-2)
               elem-2))
       ((> rank-1 rank-2)
        (begin (vset-car! elem-2 elem-1)
               elem-1))
       (else
        (begin (vset-car! elem-1 elem-2)
               elem-2))))))

(define* asymm-link! (subr (maxeff (write @heap)) (val val) val)
  (lambda (l x) (begin (vset-car! l x) v-null)))

;;;----------------------------------------------------------------------------
;;; Type management
;;;----------------------------------------------------------------------------

;; counter for generating tvar id's
(define counter (ref int @heap) (new 0))

;; generates a new id (for printing purposes)
(define* gen-id (subr (maxeff (read @heap) (write @heap)) () val)
  (lambda () (begin (set counter (+ (get counter) 1)) (vint (get counter)))))

;; generates a new type variable from a new symbol
;; uses union/find elements with two info fields
;; a type variable has exactly four fields:
;; car:     TVar (the parent field; initially null)
;; cadr:    Number (the rank field; is always nonnegative)
;; caddr:   Symbol (the type variable identifier; used only for printing)
;; cdddr:   Type (the leq field; initially null)
(define* gen-tvar (subr (maxeff (read @heap) (write @heap) (alloc @heap)) () val)
  (lambda () (gen-element (vcons (gen-id) v-null))))

;; generates a new type variable with an associated type definition
(define* gen-type (subr (maxeff (read @heap) (write @heap) (alloc @heap)) (val val) val)
  (lambda (tcon targs) (gen-element (vcons (gen-id) (vcons tcon targs)))))

;; the special type variable dynamic
(define dynamic val (gen-element (vcons (vint 0) v-null)))

;; returns the (printable) symbol representing the type variable
(define* tvar-id (subr (read @heap) (val) val) (lambda (tvar) (vcar (info tvar))))

;; returns the type definition (if any) of the type variable
(define* tvar-def (subr (read @heap) (val) val) (lambda (tvar) (vcdr (info tvar))))

;; sets the type definition part of tvar to type
(define* set-def! (subr (maxeff (read @heap) (write @heap) (alloc @heap)) (val val val) val)
  (lambda (tvar tcon targs) (begin (vset-cdr! (info tvar) (vcons tcon targs)) v-null)))

;; returns the type constructor of a type definition
(define* type-con (subr (read @heap) (val) val) (lambda (l) (vcar l)))

;; returns the type variables of a type definition
(define* type-args (subr (read @heap) (val) val) (lambda (l) (vcdr l)))

; type constructor literals

(define boolean-con val (vsym 'boolean))
(define char-con val (vsym 'char))
(define null-con val (vsym 'null))
(define number-con val (vsym 'number))
(define pair-con val (vsym 'pair))
(define procedure-con val (vsym 'procedure))
(define string-con val (vsym 'string))
(define symbol-con val (vsym 'symbol))
(define vector-con val (vsym 'vector))

; type constants and type constructors

(define-effect makes-types (maxeff (read @heap) (write @heap) (alloc @heap)))

(define* pair (subr makes-types (val val) val)
  (lambda (tvar-1 tvar-2) (gen-type pair-con (vlist2 tvar-1 tvar-2))))
;; ***Note***: Temporarily changed to be a pair!
;; (gen-type null-con '())
(define* null (subr makes-types () val) (lambda () (pair (gen-tvar) (gen-tvar))))
(define* boolean (subr makes-types () val) (lambda () (gen-type boolean-con v-null)))
(define* character (subr makes-types () val) (lambda () (gen-type char-con v-null)))
(define* number (subr makes-types () val) (lambda () (gen-type number-con v-null)))
(define* charseq (subr makes-types () val) (lambda () (gen-type string-con v-null)))
(define* symbol (subr makes-types () val) (lambda () (gen-type symbol-con v-null)))
(define* array (subr makes-types (val) val)
  (lambda (tvar) (gen-type vector-con (vlist1 tvar))))
(define* procedure (subr makes-types (val val) val)
  (lambda (arg-tvar res-tvar) (gen-type procedure-con (vlist2 arg-tvar res-tvar))))

; equivalencing of type variables

(define* equiv-with-dynamic! (subr hs (val) val)
  (lambda (tv)
    (let ((tv-rep (find! tv)))
      (begin
        (if (not (eqv? tv-rep dynamic))
            (let ((tv-def (tvar-def tv-rep)))
              (begin
                (asymm-link! tv-rep dynamic)
                (if (not (vnull? tv-def))
                    (begin (map1 equiv-with-dynamic! (type-args tv-def)) #u)
                    #u)))
            #u)
        v-null))))

(define* equiv! (subr hs (val val) val)
  (lambda (tv1 tv2)
    (let* ((tv1-rep (find! tv1))
           (tv2-rep (find! tv2))
           (tv1-def (tvar-def tv1-rep))
           (tv2-def (tvar-def tv2-rep)))
      (begin
        (cond
         ((eqv? tv1-rep tv2-rep)
          v-null)
         ((eqv? tv2-rep dynamic)
          (equiv-with-dynamic! tv1-rep))
         ((eqv? tv1-rep dynamic)
          (equiv-with-dynamic! tv2-rep))
         ((vnull? tv1-def)
          (if (vnull? tv2-def)
              ;; both tv1 and tv2 are distinct type variables
              (link! tv1-rep tv2-rep)
              ;; tv1 is a type variable, tv2 is a (nondynamic) type
              (asymm-link! tv1-rep tv2-rep)))
         ((vnull? tv2-def)
          ;; tv1 is a (nondynamic) type, tv2 is a type variable
          (asymm-link! tv2-rep tv1-rep))
         ((eqv? (type-con tv1-def) (type-con tv2-def))
          ;; both tv1 and tv2 are (nondynamic) types with equal numbers of
          ;; arguments
          (begin (link! tv1-rep tv2-rep)
                 (map2 equiv! (type-args tv1-def) (type-args tv2-def))))
         (else
          ;; tv1 and tv2 are types with distinct type constructors or different
          ;; numbers of arguments
          (begin (equiv-with-dynamic! tv1-rep)
                 (equiv-with-dynamic! tv2-rep))))
        v-null))))

;;;----------------------------------------------------------------------------
;;; Polymorphic type management
;;;----------------------------------------------------------------------------

;; type constructor literal for polymorphic types
(define ptype-con val (vsym 'forall))

(define* forall (subr makes-types ((subr tvfun (val) val)) val)
  (lambda (tv-func) (gen-type ptype-con (vproc tv-func))))

(define* forall2 (subr makes-types ((subr tvfun (val val) val)) val)
  (lambda (tv-func2)
    (forall (lambda ((tv1 val))
              (forall (lambda ((tv2 val))
                        (tv-func2 tv1 tv2)))))))

(define* forall3 (subr makes-types ((subr tvfun (val val val) val)) val)
  (lambda (tv-func3)
    (forall (lambda ((tv1 val))
              (forall2 (lambda ((tv2 val) (tv3 val))
                         (tv-func3 tv1 tv2 tv3)))))))

(define* forall4 (subr makes-types ((subr tvfun (val val val val) val)) val)
  (lambda (tv-func4)
    (forall (lambda ((tv1 val))
              (forall3 (lambda ((tv2 val) (tv3 val) (tv4 val))
                         (tv-func4 tv1 tv2 tv3 tv4)))))))

(define* forall5 (subr makes-types ((subr tvfun (val val val val val) val)) val)
  (lambda (tv-func5)
    (forall (lambda ((tv1 val))
              (forall4 (lambda ((tv2 val) (tv3 val) (tv4 val) (tv5 val))
                         (tv-func5 tv1 tv2 tv3 tv4 tv5)))))))

;; (polymorphic) instantiation

;; instantiates type tv and returns a generic instance
(define* instantiate-type (subr (maxeff hs tvfun) (val) val)
  (lambda (tv)
    (let* ((tv-rep (find! tv))
           (tv-def (tvar-def tv-rep)))
      (cond
       ((vnull? tv-def)
        tv-rep)
       ((eqv? (type-con tv-def) ptype-con)
        (instantiate-type
         (tagcase (type-args tv-def)
           (vproc (f) (f (gen-tvar)))
           (else z (error "instantiate-type: not a procedure")))))
       (else
        tv-rep)))))

;; forms a recursive type: the fixed point of type mapping tv-func
(define* fix (subr (maxeff hs tvfun) ((subr tvfun (val) val)) val)
  (lambda (tv-func)
    (let* ((new-tvar (gen-tvar))
           (inst-tvar (tv-func new-tvar))
           (inst-def (tvar-def inst-tvar)))
      (if (vnull? inst-def)
          (error "fix: Illegal recursive type")
          (begin
            (set-def! new-tvar
                      (type-con inst-def)
                      (type-args inst-def))
            new-tvar)))))

;;;----------------------------------------------------------------------------
;;;       Constraint management
;;;----------------------------------------------------------------------------

; constraints

;; generates an equality between tvar1 and tvar2
(define* gen-constr (subr (alloc @heap) (val val) val) (lambda (a b) (vcons a b)))

;; returns the left-hand side of a constraint
(define* constr-lhs (subr (read @heap) (val) val) (lambda (c) (vcar c)))

;; returns the right-hand side of a constraint
(define* constr-rhs (subr (read @heap) (val) val) (lambda (c) (vcdr c)))

; constraint set management

(define global-constraints (ref val @heap) (new v-null))

(define* init-global-constraints! (subr (write @heap) () unit)
  (lambda () (set global-constraints v-null)))

(define* add-constr! (subr (maxeff (read @heap) (write @heap) (alloc @heap)) (val val) val)
  (lambda (lhs rhs)
    (begin
      (set global-constraints
           (vcons (gen-constr lhs rhs) (get global-constraints)))
      v-null)))

; constraint normalization

(define* normalize! (subr hs (val) val)
  (lambda (constraints)
    (map1 (lambda ((c val))
            (equiv! (constr-lhs c) (constr-rhs c))) constraints)))

(define* normalize-global-constraints! (subr hs () unit)
  (lambda ()
    (begin (normalize! (get global-constraints))
           (init-global-constraints!))))

;;;----------------------------------------------------------------------------
;;; Abstract syntax definition and parse actions
;;;----------------------------------------------------------------------------

;; Abstract syntax operators

; Datum

(define null-const int 0)
(define boolean-const int 1)
(define char-const int 2)
(define number-const int 3)
(define string-const int 4)
(define symbol-const int 5)
(define vector-const int 6)
(define pair-const int 7)

; Bindings

(define var-def int 8)
(define null-def int 29)
(define pair-def int 30)

; Expr

(define variable int 9)
(define identifier int 10)
(define procedure-call int 11)
(define lambda-expression int 12)
(define conditional int 13)
(define assignment int 14)
(define cond-expression int 15)
(define case-expression int 16)
(define and-expression int 17)
(define or-expression int 18)
(define let-expression int 19)
(define named-let-expression int 20)
(define let*-expression int 21)
(define letrec-expression int 22)
(define begin-expression int 23)
(define do-expression int 24)
(define empty int 25)
(define null-arg int 31)
(define pair-arg int 32)

; Command

(define definition int 26)
(define function-definition int 27)
(define begin-command int 28)

;;;----------------------------------------------------------------------------
;;; Typed abstract syntax tree management: constraint generation, display, etc.
;;;----------------------------------------------------------------------------

;; extracts the ast-constructor from an abstract syntax tree
(define* ast-con (subr (read @heap) (val) val) (lambda (a) (vcar a)))

;; extracts the ast-argument from an abstract syntax tree
(define* ast-arg (subr (read @heap) (val) val) (lambda (a) (vcddr a)))

;; extracts the tvar from an abstract syntax tree
(define* ast-tvar (subr (read @heap) (val) val) (lambda (a) (vcadr a)))

;; returns the tail of a nonempty list
(define* tail (subr (maxeff (read @heap) spin) (val) val)
  (lambda (l)
    (if (vnull? (vcdr l))
        (vcar l)
        (tail (vcdr l)))))

;; converts a list of tvars to a single tvar
(define* convert-tvars (subr hs (val) val)
  (lambda (tvar-list)
    (cond
     ((vnull? tvar-list) (null))
     ((vpair? tvar-list) (pair (vcar tvar-list)
                               (convert-tvars (vcdr tvar-list))))
     (else (error "convert-tvars: Not a list of tvars")))))

(define dynamic-top-level-env (ref val @heap) (new v-null))

;; Abstract syntax operations, incl. constraint generation

;; generates all attributes and performs semantic side effects
(define* ast-gen (subr (maxeff hs tvfun) (int val) val)
  (lambda (syntax-op arg)
    (let ((ntvar
           (cond
            ((or (= syntax-op 0) (= syntax-op 29) (= syntax-op 31)) (null))
            ((= syntax-op 1) (boolean))
            ((= syntax-op 2) (character))
            ((= syntax-op 3) (number))
            ((= syntax-op 4) (charseq))
            ((= syntax-op 5) (symbol))
            ((= syntax-op 6)
             (let ((aux-tvar (gen-tvar)))
               (begin
                 (for-each1 (lambda ((t val))
                              (add-constr! t aux-tvar))
                            (map1 ast-tvar arg))
                 (array aux-tvar))))
            ((or (= syntax-op 7) (= syntax-op 30) (= syntax-op 32))
             (let ((t1 (ast-tvar (vcar arg)))
                   (t2 (ast-tvar (vcdr arg))))
               (pair t1 t2)))
            ((= syntax-op 8) (gen-tvar))
            ((= syntax-op 9) (ast-tvar arg))
            ((= syntax-op 10)
             (let ((in-env (dynamic-lookup arg (get dynamic-top-level-env))))
               (if (truthy? in-env)
                   (instantiate-type (binding-value in-env))
                   (let ((new-tvar (gen-tvar)))
                     (begin
                       (set dynamic-top-level-env (extend-env-with-binding
                                                   (get dynamic-top-level-env)
                                                   (gen-binding arg new-tvar)))
                       new-tvar)))))
            ((= syntax-op 11)
             (let ((new-tvar (gen-tvar)))
               (begin
                 (add-constr! (procedure (ast-tvar (vcdr arg)) new-tvar)
                              (ast-tvar (vcar arg)))
                 new-tvar)))
            ((= syntax-op 12)
             (procedure (ast-tvar (vcar arg))
                        (ast-tvar (tail (vcdr arg)))))
            ((= syntax-op 13)
             (let ((t-test (ast-tvar (vcar arg)))
                   (t-consequent (ast-tvar (vcadr arg)))
                   (t-alternate (ast-tvar (vcddr arg))))
               (begin
                 (add-constr! (boolean) t-test)
                 (add-constr! t-consequent t-alternate)
                 t-consequent)))
            ((= syntax-op 14)
             (let ((var-tvar (ast-tvar (vcar arg)))
                   (exp-tvar (ast-tvar (vcdr arg))))
               (begin
                 (add-constr! var-tvar exp-tvar)
                 var-tvar)))
            ((= syntax-op 15)
             (let ((new-tvar (gen-tvar)))
               (begin
                 (for-each1 (lambda ((body val))
                              (add-constr! (ast-tvar (tail body)) new-tvar))
                            (map1 vcdr arg))
                 (for-each1 (lambda ((e val))
                              (add-constr! (boolean) (ast-tvar e)))
                            (map1 vcar arg))
                 new-tvar)))
            ((= syntax-op 16)
             (let* ((new-tvar (gen-tvar))
                    (t-key (ast-tvar (vcar arg)))
                    (case-clauses (vcdr arg)))
               (begin
                 (for-each1 (lambda ((exprs val))
                              (begin
                                (for-each1 (lambda ((e val))
                                             (add-constr! (ast-tvar e) t-key))
                                           exprs)
                                v-null))
                            (map1 vcar case-clauses))
                 (for-each1 (lambda ((body val))
                              (add-constr! (ast-tvar (tail body)) new-tvar))
                            (map1 vcdr case-clauses))
                 new-tvar)))
            ((or (= syntax-op 17) (= syntax-op 18))
             (begin
               (for-each1 (lambda ((e val))
                            (add-constr! (boolean) (ast-tvar e)))
                          arg)
               (boolean)))
            ((or (= syntax-op 19) (= syntax-op 21) (= syntax-op 22))
             (let ((var-def-tvars (map1 ast-tvar (vcaar arg)))
                   (def-expr-types (map1 ast-tvar (vcdar arg)))
                   (body-type (ast-tvar (tail (vcdr arg)))))
               (begin
                 (for-each2 add-constr! var-def-tvars def-expr-types)
                 body-type)))
            ((= syntax-op 20)
             (let ((var-def-tvars (map1 ast-tvar (vcaadr arg)))
                   (def-expr-types (map1 ast-tvar (vcdadr arg)))
                   (body-type (ast-tvar (tail (vcddr arg))))
                   (named-var-type (ast-tvar (vcar arg))))
               (begin
                 (for-each2 add-constr! var-def-tvars def-expr-types)
                 (add-constr! (procedure (convert-tvars var-def-tvars) body-type)
                              named-var-type)
                 body-type)))
            ((= syntax-op 23) (ast-tvar (tail arg)))
            ((= syntax-op 24)
             (error "ast-gen: Do-expressions not handled!"))
            ((= syntax-op 25) (gen-tvar))
            ((= syntax-op 26)
             (let ((t-var (ast-tvar (vcar arg)))
                   (t-exp (ast-tvar (vcdr arg))))
               (begin
                 (add-constr! t-var t-exp)
                 t-var)))
            ((= syntax-op 27)
             (let ((t-var (ast-tvar (vcar arg)))
                   (t-formals (ast-tvar (vcadr arg)))
                   (t-body (ast-tvar (tail (vcddr arg)))))
               (begin
                 (add-constr! (procedure t-formals t-body) t-var)
                 t-var)))
            ((= syntax-op 28) (gen-tvar))
            (else (error "ast-gen: Can't handle syntax operator")))))
      (vcons (vint syntax-op) (vcons ntvar arg)))))

;; Parse actions for abstract syntax construction

(define-effect acts (maxeff hs tvfun))

;; dynamic-parse-action for '()
(define* dynamic-parse-action-null-const (subr acts () val)
  (lambda () (ast-gen null-const v-null)))

;; dynamic-parse-action for #f and #t
(define* dynamic-parse-action-boolean-const (subr acts (val) val)
  (lambda (e) (ast-gen boolean-const e)))

;; dynamic-parse-action for character constants
(define* dynamic-parse-action-char-const (subr acts (val) val)
  (lambda (e) (ast-gen char-const e)))

;; dynamic-parse-action for number constants
(define* dynamic-parse-action-number-const (subr acts (val) val)
  (lambda (e) (ast-gen number-const e)))

;; dynamic-parse-action for string literals
(define* dynamic-parse-action-string-const (subr acts (val) val)
  (lambda (e) (ast-gen string-const e)))

;; dynamic-parse-action for symbol constants
(define* dynamic-parse-action-symbol-const (subr acts (val) val)
  (lambda (e) (ast-gen symbol-const e)))

;; dynamic-parse-action for vector literals
(define* dynamic-parse-action-vector-const (subr acts (val) val)
  (lambda (e) (ast-gen vector-const e)))

;; dynamic-parse-action for pairs
(define* dynamic-parse-action-pair-const (subr acts (val val) val)
  (lambda (e1 e2) (ast-gen pair-const (vcons e1 e2))))

;; dynamic-parse-action for defining occurrences of variables;
;; e is a symbol
(define* dynamic-parse-action-var-def (subr acts (val) val)
  (lambda (e) (ast-gen var-def e)))

;; dynamic-parse-action for null-list of formals
(define* dynamic-parse-action-null-formal (subr acts () val)
  (lambda () (ast-gen null-def v-null)))

;; dynamic-parse-action for non-null list of formals;
;; d1 is the result of parsing the first formal,
;; d2 the result of parsing the remaining formals
(define* dynamic-parse-action-pair-formal (subr acts (val val) val)
  (lambda (d1 d2) (ast-gen pair-def (vcons d1 d2))))

;; dynamic-parse-action for applied occurrences of variables
;; ***Note***: e is the result of a dynamic-parse-action on the
;; corresponding variable definition!
(define* dynamic-parse-action-variable (subr acts (val) val)
  (lambda (e) (ast-gen variable e)))

;; dynamic-parse-action for undeclared identifiers (free variable
;; occurrences)
;; ***Note***: e is a symbol (legal identifier)
(define* dynamic-parse-action-identifier (subr acts (val) val)
  (lambda (e) (ast-gen identifier e)))

;; dynamic-parse-action for a null list of arguments in a procedure call
(define* dynamic-parse-action-null-arg (subr acts () val)
  (lambda () (ast-gen null-arg v-null)))

;; dynamic-parse-action for a non-null list of arguments in a procedure call
;; a1 is the result of parsing the first argument,
;; a2 the result of parsing the remaining arguments
(define* dynamic-parse-action-pair-arg (subr acts (val val) val)
  (lambda (a1 a2) (ast-gen pair-arg (vcons a1 a2))))

;; dynamic-parse-action for procedure calls: op function, args list of arguments
(define* dynamic-parse-action-procedure-call (subr acts (val val) val)
  (lambda (op args) (ast-gen procedure-call (vcons op args))))

;; dynamic-parse-action for lambda-abstractions
(define* dynamic-parse-action-lambda-expression (subr acts (val val) val)
  (lambda (formals body) (ast-gen lambda-expression (vcons formals body))))

;; dynamic-parse-action for conditionals (if-then-else expressions)
(define* dynamic-parse-action-conditional (subr acts (val val val) val)
  (lambda (test then-branch else-branch)
    (ast-gen conditional (vcons test (vcons then-branch else-branch)))))

;; dynamic-parse-action for missing or empty field
(define* dynamic-parse-action-empty (subr acts () val)
  (lambda () (ast-gen empty v-null)))

;; dynamic-parse-action for assignment
(define* dynamic-parse-action-assignment (subr acts (val val) val)
  (lambda (lhs rhs) (ast-gen assignment (vcons lhs rhs))))

;; dynamic-parse-action for begin-expression
(define* dynamic-parse-action-begin-expression (subr acts (val) val)
  (lambda (body) (ast-gen begin-expression body)))

;; dynamic-parse-action for cond-expressions
(define* dynamic-parse-action-cond-expression (subr acts (val) val)
  (lambda (clauses) (ast-gen cond-expression clauses)))

;; dynamic-parse-action for and-expressions
(define* dynamic-parse-action-and-expression (subr acts (val) val)
  (lambda (args) (ast-gen and-expression args)))

;; dynamic-parse-action for or-expressions
(define* dynamic-parse-action-or-expression (subr acts (val) val)
  (lambda (args) (ast-gen or-expression args)))

;; dynamic-parse-action for case-expressions
(define* dynamic-parse-action-case-expression (subr acts (val val) val)
  (lambda (key clauses) (ast-gen case-expression (vcons key clauses))))

;; dynamic-parse-action for let-expressions
(define* dynamic-parse-action-let-expression (subr acts (val val) val)
  (lambda (bindings body) (ast-gen let-expression (vcons bindings body))))

;; dynamic-parse-action for named-let expressions
(define* dynamic-parse-action-named-let-expression (subr acts (val val val) val)
  (lambda (variable bindings body)
    (ast-gen named-let-expression (vcons variable (vcons bindings body)))))

;; dynamic-parse-action for let-expressions
(define* dynamic-parse-action-let*-expression (subr acts (val val) val)
  (lambda (bindings body) (ast-gen let*-expression (vcons bindings body))))

;; dynamic-parse-action for let-expressions
(define* dynamic-parse-action-letrec-expression (subr acts (val val) val)
  (lambda (bindings body) (ast-gen letrec-expression (vcons bindings body))))

;; dynamic-parse-action for simple definitions
(define* dynamic-parse-action-definition (subr acts (val val) val)
  (lambda (variable expr) (ast-gen definition (vcons variable expr))))

;; dynamic-parse-action for function definitions
(define* dynamic-parse-action-function-definition (subr acts (val val val) val)
  (lambda (variable formals body)
    (ast-gen function-definition (vcons variable (vcons formals body)))))

;; dynamic-parse-action for processing a command result followed by a the
;; result of processing the remaining commands
(define* dynamic-parse-action-commands (subr (alloc @heap) (val val) val)
  (lambda (a b) (vcons a b)))

;;;----------------------------------------------------------------------------
;;;       Parsing for Scheme
;;;----------------------------------------------------------------------------

;; Lexical notions

;; source: IEEE Scheme, 7.1, <expression keyword>, <syntactic keyword>
(define syntactic-keywords val
  (vlist-of
   (list (vsym 'lambda) (vsym 'if) (vsym 'set!) (vsym 'begin) (vsym 'cond) (vsym 'and)
         (vsym 'or) (vsym 'case) (vsym 'let) (vsym 'let*) (vsym 'letrec) (vsym 'do)
         (vsym 'quasiquote) (vsym 'else) (vsym '=>) (vsym 'define) (vsym 'unquote)
         (vsym 'unquote-splicing))))

;; Parse routines

; Datum

;; dynamic-parse-datum: parses nonterminal <datum>
(define* dynamic-parse-datum (subr acts (val) val)
  ;; Source: IEEE Scheme, sect. 7.2, <datum>
  ;; Note: "'" is parsed as 'quote, "`" as 'quasiquote, "," as
  ;; 'unquote, ",@" as 'unquote-splicing (see sect. 4.2.5, p. 18)
  ;; ***Note***: quasi-quotations are not permitted! (It would be
  ;; necessary to pass the environment to dynamic-parse-datum.)
  (lambda (e)
    (cond
     ((vnull? e)
      (dynamic-parse-action-null-const))
     ((vboolean? e)
      (dynamic-parse-action-boolean-const e))
     ((vchar? e)
      (dynamic-parse-action-char-const e))
     ((vnumber? e)
      (dynamic-parse-action-number-const e))
     ((vstring? e)
      (dynamic-parse-action-string-const e))
     ((vsymbol? e)
      (dynamic-parse-action-symbol-const e))
     ((vvector? e)
      (dynamic-parse-action-vector-const (map1 dynamic-parse-datum (vector->list e))))
     ((vpair? e)
      (dynamic-parse-action-pair-const (dynamic-parse-datum (vcar e))
                                       (dynamic-parse-datum (vcdr e))))
     (else (error "dynamic-parse-datum: Unknown datum")))))

; VarDef

;; dynamic-parse-formal: parses nonterminal <variable> in defining occurrence position
(define* dynamic-parse-formal (subr acts (val val) val)
  ;; e is an arbitrary object, f-env is a forbidden environment;
  ;; returns: a variable definition (a binding for the symbol), plus
  ;; the value of the binding as a result
  (lambda (f-env e)
    (if (vsymbol? e)
        (cond
         ((vmemq e syntactic-keywords)
          (error "dynamic-parse-formal: Illegal identifier (keyword)"))
         ((truthy? (dynamic-lookup e f-env))
          (error "dynamic-parse-formal: Duplicate variable definition"))
         (else (let ((dynamic-parse-action-result (dynamic-parse-action-var-def e)))
                 (vcons (gen-binding e dynamic-parse-action-result)
                        dynamic-parse-action-result))))
        (error "dynamic-parse-formal: Not an identifier"))))

;; dynamic-parse-formal*
(define* dynamic-parse-formal* (subr acts (val) val)
  ;; parses a list of formals and returns a pair consisting of generated
  ;; environment and list of parsing action results
  (lambda (formals)
    (letrec
        ((pf*
          (subr acts (val val val) val)
          (lambda (f-env results formals)
            ;; f-env: "forbidden" environment (to avoid duplicate defs)
            ;; results: the results of the parsing actions
            ;; formals: the unprocessed formals
            ;; Note: generates the results of formals in reverse order!
            (cond
             ((vnull? formals)
              (vcons f-env results))
             ((vpair? formals)
              (let* ((fst-formal (vcar formals))
                     (binding-result (dynamic-parse-formal f-env fst-formal))
                     (binding (vcar binding-result))
                     (var-result (vcdr binding-result)))
                (pf*
                 (extend-env-with-binding f-env binding)
                 (vcons var-result results)
                 (vcdr formals))))
             (else (error "dynamic-parse-formal*: Illegal formals"))))))
      (let ((renv-rres (pf* dynamic-empty-env v-null formals)))
        (vcons (vcar renv-rres) (vreverse (vcdr renv-rres)))))))

;; dynamic-parse-formals: parses <formals>
(define* dynamic-parse-formals (subr acts (val) val)
  ;; parses <formals>; see IEEE Scheme, sect. 7.3
  ;; returns a pair: env and result
  (lambda (formals)
    (letrec ((pfs (subr acts (val val) val)
               (lambda (f-env formals)
                 (cond
                  ((vnull? formals)
                   (vcons dynamic-empty-env (dynamic-parse-action-null-formal)))
                  ((vpair? formals)
                   (let* ((fst-formal (vcar formals))
                          (rem-formals (vcdr formals))
                          (bind-res (dynamic-parse-formal f-env fst-formal))
                          (bind (vcar bind-res))
                          (res (vcdr bind-res))
                          (nf-env (extend-env-with-binding f-env bind))
                          (renv-res* (pfs nf-env rem-formals))
                          (renv (vcar renv-res*))
                          (res* (vcdr renv-res*)))
                     (vcons
                      (extend-env-with-binding renv bind)
                      (dynamic-parse-action-pair-formal res res*))))
                  (else
                   (let* ((bind-res (dynamic-parse-formal f-env formals))
                          (bind (vcar bind-res))
                          (res (vcdr bind-res)))
                     (vcons
                      (extend-env-with-binding dynamic-empty-env bind)
                      res)))))))
      (pfs dynamic-empty-env formals))))

;; Auxiliary routines

(define* list-of-1? (subr (read @heap) (val) bool)
  (lambda (l) (and (vpair? l) (vnull? (vcdr l)))))

(define* list-of-2? (subr (read @heap) (val) bool)
  (lambda (l) (and (vpair? l) (vpair? (vcdr l)) (vnull? (vcddr l)))))

(define* list-of-3? (subr (read @heap) (val) bool)
  (lambda (l) (and (vpair? l) (vpair? (vcdr l)) (vpair? (vcddr l)) (vnull? (vcdddr l)))))

(define* list-of-list-of-2s? (subr (maxeff (read @heap) spin) (val) bool)
  (lambda (e)
    (cond
     ((vnull? e)
      #t)
     ((vpair? e)
      (and (list-of-2? (vcar e)) (list-of-list-of-2s? (vcdr e))))
     (else #f))))

;; dynamic-parse-variable: parses variables (applied occurrences)
(define* dynamic-parse-variable (subr acts (val val) val)
  (lambda (env e)
    (if (vsymbol? e)
        (if (vmemq e syntactic-keywords)
            (error "dynamic-parse-variable: Illegal identifier (keyword)")
            (let ((assoc-var-def (dynamic-lookup e env)))
              (if (truthy? assoc-var-def)
                  (dynamic-parse-action-variable (binding-value assoc-var-def))
                  (dynamic-parse-action-identifier e))))
        (error "dynamic-parse-variable: Not an identifier"))))

;; dynamic-parse-quote
(define* dynamic-parse-quote (subr acts (val val) val)
  (lambda (env args)
    (if (list-of-1? args)
        (dynamic-parse-datum (vcar args))
        (error "dynamic-parse-quote: Not a datum (multiple arguments)"))))

;; dynamic-parse-do
(define* dynamic-parse-do (subr acts (val val) val)
  ;; parses do-expressions
  ;; ***Note***: Not implemented!
  (lambda (env args) (error "dynamic-parse-do: Nothing yet...")))

;; dynamic-parse-quasiquote
(define* dynamic-parse-quasiquote (subr acts (val val) val)
  ;; ***Note***: Not implemented!
  (lambda (env args) (error "dynamic-parse-quasiquote: Nothing yet...")))

(define-effect parses
  (maxeff acts
          (read (globals dynamic-parse-expression dynamic-parse-expression*
                         dynamic-parse-expressions dynamic-parse-procedure-call
                         dynamic-parse-lambda dynamic-parse-body dynamic-parse-if
                         dynamic-parse-set dynamic-parse-begin dynamic-parse-cond
                         dynamic-parse-cond-clause dynamic-parse-and dynamic-parse-or
                         dynamic-parse-case dynamic-parse-case-clause dynamic-parse-let
                         dynamic-parse-normal-let dynamic-parse-named-let
                         dynamic-parse-parallel-bindings dynamic-parse-let*
                         dynamic-parse-sequential-bindings dynamic-parse-letrec
                         dynamic-parse-recursive-bindings dynamic-parse-command
                         dynamic-parse-command* dynamic-parse-define add-constr! ast-gen
                         ast-tvar binding-value boolean-const char-con char-const character
                         charseq dynamic-lookup dynamic-parse-action-boolean-const
                         dynamic-parse-action-char-const dynamic-parse-action-identifier
                         dynamic-parse-action-null-const dynamic-parse-action-number-const
                         dynamic-parse-action-pair-const dynamic-parse-action-string-const
                         dynamic-parse-action-symbol-const dynamic-parse-action-variable
                         dynamic-parse-action-vector-const dynamic-parse-datum dynamic-parse-do
                         dynamic-parse-quasiquote dynamic-parse-quote dynamic-parse-variable
                         dynamic-top-level-env eqv? extend-env-with-binding find! for-each1
                         for-each2 gen-binding gen-constr global-constraints identifier
                         instantiate-type is-sym? list-of-1? map1 null-const number-const
                         pair-const string-con string-const symbol symbol-con symbol-const
                         syntactic-keywords tail truthy? v-false variable vassv vboolean?
                         vcaadr vcaar vcadr vcdadr vcdar vchar? vector->list vector-const vmemq
                         vnumber? vset-car! vstring? vsymbol? vvector? vreverse
                         dynamic-parse-action-null-arg dynamic-parse-action-pair-arg null-arg
                         pair-arg dynamic-parse-action-procedure-call procedure-call
                         dynamic-empty-env dynamic-parse-action-lambda-expression
                         dynamic-parse-action-null-formal dynamic-parse-action-pair-formal
                         dynamic-parse-action-var-def dynamic-parse-formal
                         dynamic-parse-formals extend-env-with-env lambda-expression null-def
                         pair-def vappend var-def conditional dynamic-parse-action-conditional
                         dynamic-parse-action-empty empty list-of-2? list-of-3? vcaddr vcdddr
                         assignment dynamic-parse-action-assignment begin-expression
                         dynamic-parse-action-begin-expression cond-expression
                         dynamic-parse-action-cond-expression vlist? and-expression
                         dynamic-parse-action-and-expression dynamic-parse-action-or-expression
                         or-expression case-expression dynamic-parse-action-case-expression
                         vlength dynamic-parse-action-let-expression let-expression
                         dynamic-parse-action-named-let-expression named-let-expression
                         dynamic-parse-formal* list-of-list-of-2s?
                         dynamic-parse-action-let*-expression let*-expression
                         dynamic-parse-action-letrec-expression letrec-expression definition
                         dynamic-parse-action-definition
                         dynamic-parse-action-function-definition function-definition))))

(define-rec
  ;; Expr

  ;; dynamic-parse-expression: parses nonterminal <expression>
  (dynamic-parse-expression (subr parses (val val) val)
    (lambda (env e)
      (cond
       ((vsymbol? e)
        (dynamic-parse-variable env e))
       ((vpair? e)
        (let ((op (vcar e)) (args (vcdr e)))
          (cond
           ((is-sym? op 'quote) (dynamic-parse-quote env args))
           ((is-sym? op 'lambda) (dynamic-parse-lambda env args))
           ((is-sym? op 'if) (dynamic-parse-if env args))
           ((is-sym? op 'set!) (dynamic-parse-set env args))
           ((is-sym? op 'begin) (dynamic-parse-begin env args))
           ((is-sym? op 'cond) (dynamic-parse-cond env args))
           ((is-sym? op 'case) (dynamic-parse-case env args))
           ((is-sym? op 'and) (dynamic-parse-and env args))
           ((is-sym? op 'or) (dynamic-parse-or env args))
           ((is-sym? op 'let) (dynamic-parse-let env args))
           ((is-sym? op 'let*) (dynamic-parse-let* env args))
           ((is-sym? op 'letrec) (dynamic-parse-letrec env args))
           ((is-sym? op 'do) (dynamic-parse-do env args))
           ((is-sym? op 'quasiquote) (dynamic-parse-quasiquote env args))
           (else (dynamic-parse-procedure-call env op args)))))
       (else (dynamic-parse-datum e)))))

  ;; dynamic-parse-expression*
  (dynamic-parse-expression* (subr parses (val val) val)
    ;; Parses lists of expressions (returns them in the right order!)
    (lambda (env exprs)
      (letrec ((pe*
                (subr parses (val val) val)
                (lambda (results es)
                  (cond
                   ((vnull? es) results)
                   ((vpair? es)
                    (pe* (vcons (dynamic-parse-expression env (vcar es)) results) (vcdr es)))
                   (else (error "dynamic-parse-expression*: Not a list of expressions"))))))
        (vreverse (pe* v-null exprs)))))

  ;; dynamic-parse-expressions
  (dynamic-parse-expressions (subr parses (val val) val)
    ;; parses lists of arguments of a procedure call
    (lambda (env exprs)
      (cond
       ((vnull? exprs) (dynamic-parse-action-null-arg))
       ((vpair? exprs) (let* ((fst-expr (vcar exprs))
                              (rem-exprs (vcdr exprs))
                              (fst-res (dynamic-parse-expression env fst-expr))
                              (rem-res (dynamic-parse-expressions env rem-exprs)))
                         (dynamic-parse-action-pair-arg fst-res rem-res)))
       (else (error "dynamic-parse-expressions: Illegal expression list")))))

  ;; dynamic-parse-procedure-call
  (dynamic-parse-procedure-call (subr parses (val val val) val)
    (lambda (env op args)
      (dynamic-parse-action-procedure-call
       (dynamic-parse-expression env op)
       (dynamic-parse-expressions env args))))

  ;; dynamic-parse-lambda
  (dynamic-parse-lambda (subr parses (val val) val)
    (lambda (env args)
      (if (vpair? args)
          (let* ((formals (vcar args))
                 (body (vcdr args))
                 (nenv-fresults (dynamic-parse-formals formals))
                 (nenv (vcar nenv-fresults))
                 (fresults (vcdr nenv-fresults)))
            (dynamic-parse-action-lambda-expression
             fresults
             (dynamic-parse-body (extend-env-with-env env nenv) body)))
          (error "dynamic-parse-lambda: Illegal formals/body"))))

  ;; dynamic-parse-body
  (dynamic-parse-body (subr parses (val val) val)
    ;; <body> = <definition>* <expression>+
    (lambda (env body)
      (letrec ((def-var*
                (subr parses (val val) val)
                ;; finds the defined variables in a body and returns an
                ;; environment containing them
                (lambda (f-env body)
                  (if (vpair? body)
                      (let ((n-env (def-var f-env (vcar body))))
                        (if (truthy? n-env)
                            (def-var* n-env (vcdr body))
                            f-env))
                      f-env)))
               (def-var
                (subr parses (val val) val)
                ;; finds the defined variables in a single clause and extends
                ;; f-env accordingly; returns false if it's not a definition
                (lambda (f-env clause)
                  (if (vpair? clause)
                      (let ((key (vcar clause)))
                        (cond
                         ((is-sym? key 'define)
                          (if (vpair? (vcdr clause))
                              (let ((pattern (vcadr clause)))
                                (cond
                                 ((vsymbol? pattern)
                                  (extend-env-with-binding
                                   f-env
                                   (gen-binding pattern
                                                (dynamic-parse-action-var-def pattern))))
                                 ((and (vpair? pattern) (vsymbol? (vcar pattern)))
                                  (extend-env-with-binding
                                   f-env
                                   (gen-binding (vcar pattern)
                                                (dynamic-parse-action-var-def
                                                 (vcar pattern)))))
                                 (else f-env)))
                              f-env))
                         ((is-sym? key 'begin) (def-var* f-env (vcdr clause)))
                         (else v-false)))
                      v-false))))
        (if (vpair? body)
            (dynamic-parse-command* (def-var* env body) body)
            (error "dynamic-parse-body: Illegal body")))))

  ;; dynamic-parse-if
  (dynamic-parse-if (subr parses (val val) val)
    (lambda (env args)
      (cond
       ((list-of-3? args)
        (dynamic-parse-action-conditional
         (dynamic-parse-expression env (vcar args))
         (dynamic-parse-expression env (vcadr args))
         (dynamic-parse-expression env (vcaddr args))))
       ((list-of-2? args)
        (dynamic-parse-action-conditional
         (dynamic-parse-expression env (vcar args))
         (dynamic-parse-expression env (vcadr args))
         (dynamic-parse-action-empty)))
       (else (error "dynamic-parse-if: Not an if-expression")))))

  ;; dynamic-parse-set
  (dynamic-parse-set (subr parses (val val) val)
    (lambda (env args)
      (if (list-of-2? args)
          (dynamic-parse-action-assignment
           (dynamic-parse-variable env (vcar args))
           (dynamic-parse-expression env (vcadr args)))
          (error "dynamic-parse-set: Not a variable/expression pair"))))

  ;; dynamic-parse-begin
  (dynamic-parse-begin (subr parses (val val) val)
    (lambda (env args)
      (dynamic-parse-action-begin-expression
       (dynamic-parse-body env args))))

  ;; dynamic-parse-cond
  (dynamic-parse-cond (subr parses (val val) val)
    (lambda (env args)
      (if (and (vpair? args) (vlist? args))
          (dynamic-parse-action-cond-expression
           (map1 (lambda ((e val))
                   (dynamic-parse-cond-clause env e))
                 args))
          (error "dynamic-parse-cond: Not a list of cond-clauses"))))

  ;; dynamic-parse-cond-clause
  (dynamic-parse-cond-clause (subr parses (val val) val)
    ;; ***Note***: Only (<test> <sequence>) is permitted!
    (lambda (env e)
      (if (vpair? e)
          (vcons
           (if (is-sym? (vcar e) 'else)
               (dynamic-parse-action-empty)
               (dynamic-parse-expression env (vcar e)))
           (dynamic-parse-body env (vcdr e)))
          (error "dynamic-parse-cond-clause: Not a cond-clause"))))

  ;; dynamic-parse-and
  (dynamic-parse-and (subr parses (val val) val)
    (lambda (env args)
      (if (vlist? args)
          (dynamic-parse-action-and-expression
           (dynamic-parse-expression* env args))
          (error "dynamic-parse-and: Not a list of arguments"))))

  ;; dynamic-parse-or
  (dynamic-parse-or (subr parses (val val) val)
    (lambda (env args)
      (if (vlist? args)
          (dynamic-parse-action-or-expression
           (dynamic-parse-expression* env args))
          (error "dynamic-parse-or: Not a list of arguments"))))

  ;; dynamic-parse-case
  (dynamic-parse-case (subr parses (val val) val)
    (lambda (env args)
      (if (and (vlist? args) (> (vlength args) 1))
          (dynamic-parse-action-case-expression
           (dynamic-parse-expression env (vcar args))
           (map1 (lambda ((e val))
                   (dynamic-parse-case-clause env e))
                 (vcdr args)))
          (error "dynamic-parse-case: Not a list of clauses"))))

  ;; dynamic-parse-case-clause
  (dynamic-parse-case-clause (subr parses (val val) val)
    (lambda (env e)
      (if (vpair? e)
          (vcons
           (cond
            ((is-sym? (vcar e) 'else)
             (vlist1 (dynamic-parse-action-empty)))
            ((vlist? (vcar e))
             (map1 dynamic-parse-datum (vcar e)))
            (else (error "dynamic-parse-case-clause: Not a datum list")))
           (dynamic-parse-body env (vcdr e)))
          (error "dynamic-parse-case-clause: Not case clause"))))

  ;; dynamic-parse-let
  (dynamic-parse-let (subr parses (val val) val)
    (lambda (env args)
      (if (vpair? args)
          (if (vsymbol? (vcar args))
              (dynamic-parse-named-let env args)
              (dynamic-parse-normal-let env args))
          (error "dynamic-parse-let: Illegal bindings/body"))))

  ;; dynamic-parse-normal-let
  (dynamic-parse-normal-let (subr parses (val val) val)
    ;; parses "normal" let-expressions
    (lambda (env args)
      (let* ((bindings (vcar args))
             (body (vcdr args))
             (env-ast (dynamic-parse-parallel-bindings env bindings))
             (nenv (vcar env-ast))
             (bresults (vcdr env-ast)))
        (dynamic-parse-action-let-expression
         bresults
         (dynamic-parse-body (extend-env-with-env env nenv) body)))))

  ;; dynamic-parse-named-let
  (dynamic-parse-named-let (subr parses (val val) val)
    ;; parses a named let-expression
    (lambda (env args)
      (if (vpair? (vcdr args))
          (let* ((variable (vcar args))
                 (bindings (vcadr args))
                 (body (vcddr args))
                 (vbind-vres (dynamic-parse-formal dynamic-empty-env variable))
                 (vbind (vcar vbind-vres))
                 (vres (vcdr vbind-vres))
                 (env-ast (dynamic-parse-parallel-bindings env bindings))
                 (nenv (vcar env-ast))
                 (bresults (vcdr env-ast)))
            (dynamic-parse-action-named-let-expression
             vres bresults
             (dynamic-parse-body (extend-env-with-env
                                  (extend-env-with-binding env vbind)
                                  nenv) body)))
          (error "dynamic-parse-named-let: Illegal named let-expression"))))

  ;; dynamic-parse-parallel-bindings
  (dynamic-parse-parallel-bindings (subr parses (val val) val)
    ;; returns a pair consisting of an environment
    ;; and a list of pairs (variable . asg)
    ;; ***Note***: the list of pairs is returned in reverse unzipped form!
    (lambda (env bindings)
      (if (list-of-list-of-2s? bindings)
          (let* ((env-formals-asg
                  (dynamic-parse-formal* (map1 vcar bindings)))
                 (nenv (vcar env-formals-asg))
                 (bresults (vcdr env-formals-asg))
                 (exprs-asg
                  (dynamic-parse-expression* env (map1 vcadr bindings))))
            (vcons nenv (vcons bresults exprs-asg)))
          (error "dynamic-parse-parallel-bindings: Not a list of bindings"))))

  ;; dynamic-parse-let*
  (dynamic-parse-let* (subr parses (val val) val)
    (lambda (env args)
      (if (vpair? args)
          (let* ((bindings (vcar args))
                 (body (vcdr args))
                 (env-ast (dynamic-parse-sequential-bindings env bindings))
                 (nenv (vcar env-ast))
                 (bresults (vcdr env-ast)))
            (dynamic-parse-action-let*-expression
             bresults
             (dynamic-parse-body (extend-env-with-env env nenv) body)))
          (error "dynamic-parse-let*: Illegal bindings/body"))))

  ;; dynamic-parse-sequential-bindings
  (dynamic-parse-sequential-bindings (subr parses (val val) val)
    ;; returns a pair consisting of an environment
    ;; and a list of pairs (variable . asg)
    ;; ***Note***: the list of pairs is returned in reverse unzipped form!
    (lambda (env bindings)
      (letrec
          ((psb
            (subr parses (val val val val val) val)
            (lambda (f-env c-env var-defs expr-asgs binds)
              ;; f-env: forbidden environment
              ;; c-env: constructed environment
              ;; var-defs: results of formals
              ;; expr-asgs: results of corresponding expressions
              ;; binds: reminding bindings to process
              (cond
               ((vnull? binds)
                (vcons f-env (vcons var-defs expr-asgs)))
               ((vpair? binds)
                (let ((fst-bind (vcar binds)))
                  (if (list-of-2? fst-bind)
                      (let* ((fbinding-bres
                              (dynamic-parse-formal f-env (vcar fst-bind)))
                             (fbind (vcar fbinding-bres))
                             (bres (vcdr fbinding-bres))
                             (new-expr-asg
                              (dynamic-parse-expression c-env (vcadr fst-bind))))
                        (psb
                         (extend-env-with-binding f-env fbind)
                         (extend-env-with-binding c-env fbind)
                         (vcons bres var-defs)
                         (vcons new-expr-asg expr-asgs)
                         (vcdr binds)))
                      (error "dynamic-parse-sequential-bindings: Illegal binding"))))
               (else (error "dynamic-parse-sequential-bindings: Illegal bindings"))))))
        (let ((env-vdefs-easgs (psb dynamic-empty-env env v-null v-null bindings)))
          (vcons (vcar env-vdefs-easgs)
                 (vcons (vreverse (vcadr env-vdefs-easgs))
                        (vreverse (vcddr env-vdefs-easgs))))))))

  ;; dynamic-parse-letrec
  (dynamic-parse-letrec (subr parses (val val) val)
    (lambda (env args)
      (if (vpair? args)
          (let* ((bindings (vcar args))
                 (body (vcdr args))
                 (env-ast (dynamic-parse-recursive-bindings env bindings))
                 (nenv (vcar env-ast))
                 (bresults (vcdr env-ast)))
            (dynamic-parse-action-letrec-expression
             bresults
             (dynamic-parse-body (extend-env-with-env env nenv) body)))
          (error "dynamic-parse-letrec: Illegal bindings/body"))))

  ;; dynamic-parse-recursive-bindings
  (dynamic-parse-recursive-bindings (subr parses (val val) val)
    ;; ***Note***: the list of pairs is returned in reverse unzipped form!
    (lambda (env bindings)
      (if (list-of-list-of-2s? bindings)
          (let* ((env-formals-asg
                  (dynamic-parse-formal* (map1 vcar bindings)))
                 (formals-env
                  (vcar env-formals-asg))
                 (formals-res
                  (vcdr env-formals-asg))
                 (exprs-asg
                  (dynamic-parse-expression*
                   (extend-env-with-env env formals-env)
                   (map1 vcadr bindings))))
            (vcons
             formals-env
             (vcons formals-res exprs-asg)))
          (error "dynamic-parse-recursive-bindings: Illegal bindings"))))

  ;; Command

  ;; dynamic-parse-command
  (dynamic-parse-command (subr parses (val val) val)
    (lambda (env c)
      (if (vpair? c)
          (let ((op (vcar c))
                (args (vcdr c)))
            (cond
             ((is-sym? op 'define) (dynamic-parse-define env args))
             ;; ((begin) (dynamic-parse-command* env args))  ;; AKW
             ((is-sym? op 'begin)
              (dynamic-parse-action-begin-expression (dynamic-parse-command* env args)))
             (else (dynamic-parse-expression env c))))
          (dynamic-parse-expression env c))))

  ;; dynamic-parse-command*
  (dynamic-parse-command* (subr parses (val val) val)
    ;; parses a sequence of commands
    (lambda (env commands)
      (if (vlist? commands)
          (map1 (lambda ((command val)) (dynamic-parse-command env command)) commands)
          (error "dynamic-parse-command*: Invalid sequence of commands"))))

  ;; dynamic-parse-define
  (dynamic-parse-define (subr parses (val val) val)
    ;; three cases -- see IEEE Scheme, sect. 5.2
    ;; ***Note***: the parser admits forms (define (x . y) ...)
    ;; ***Note***: Variables are treated as applied occurrences!
    (lambda (env args)
      (if (vpair? args)
          (let ((pattern (vcar args))
                (exp-or-body (vcdr args)))
            (cond
             ((vsymbol? pattern)
              (if (list-of-1? exp-or-body)
                  (dynamic-parse-action-definition
                   (dynamic-parse-variable env pattern)
                   (dynamic-parse-expression env (vcar exp-or-body)))
                  (error "dynamic-parse-define: Not a single expression")))
             ((vpair? pattern)
              (let* ((function-name (vcar pattern))
                     (function-arg-names (vcdr pattern))
                     (env-ast (dynamic-parse-formals function-arg-names))
                     (formals-env (vcar env-ast))
                     (formals-ast (vcdr env-ast)))
                (dynamic-parse-action-function-definition
                 (dynamic-parse-variable env function-name)
                 formals-ast
                 (dynamic-parse-body (extend-env-with-env env formals-env) exp-or-body))))
             (else (error "dynamic-parse-define: Not a valid pattern"))))
          (error "dynamic-parse-define: Not a valid definition")))))

;; File processing

;; dynamic-parse-from-port
(define* dynamic-parse-from-port (subr parses (port) val)
  (lambda (port)
    (let ((next-input (read-datum port)))
      (if (veof-object? next-input)
          v-null
          (dynamic-parse-action-commands
           (dynamic-parse-command dynamic-empty-env next-input)
           (dynamic-parse-from-port port))))))

;; dynamic-parse-file
(define* dynamic-parse-file (subr parses (string) val)
  (lambda (file-name)
    (let ((input-port (open-input-string file-name)))
      (dynamic-parse-from-port input-port))))

;;;----------------------------------------------------------------------------
;;; Display: tagging and untagging
;;;----------------------------------------------------------------------------

;; The symbols the display builds with.
(define q-quote val (vsym 'quote))
(define q-cons val (vsym 'cons))
(define q-lambda val (vsym 'lambda))
(define q-if val (vsym 'if))
(define q-set! val (vsym 'set!))
(define q-cond val (vsym 'cond))
(define q-else val (vsym 'else))
(define q-case val (vsym 'case))
(define q-and val (vsym 'and))
(define q-or val (vsym 'or))
(define q-let val (vsym 'let))
(define q-let* val (vsym 'let*))
(define q-letrec val (vsym 'letrec))
(define q-begin val (vsym 'begin))
(define q-define val (vsym 'define))
(define q-tag val (vsym 'tag))
(define q-no-tag val (vsym 'no-tag))
(define q-untag val (vsym 'untag))
(define q-no-untag val (vsym 'no-untag))
(define q-may-untag val (vsym 'may-untag))
(define q-no-may-untag val (vsym 'no-may-untag))

;; datum-show

;; prints an abstract syntax tree as a datum
(define* datum-show (subr hs (val) val)
  (lambda (ast)
    (let ((op (vint-of (ast-con ast))))
      (cond
       ((and (>= op 0) (<= op 5)) (ast-arg ast))
       ((= op 6) (list->vector (map1 datum-show (ast-arg ast))))
       ((= op 7) (vcons (datum-show (vcar (ast-arg ast))) (datum-show (vcdr (ast-arg ast)))))
       (else (error "datum-show: This should not happen!"))))))

;; counters for tagging/untagging

(define untag-counter (ref int @heap) (new 0))
(define no-untag-counter (ref int @heap) (new 0))
(define tag-counter (ref int @heap) (new 0))
(define no-tag-counter (ref int @heap) (new 0))
(define may-untag-counter (ref int @heap) (new 0))
(define no-may-untag-counter (ref int @heap) (new 0))

(define* reset-counters! (subr (write @heap) () unit)
  (lambda ()
    (begin
      (set untag-counter 0)
      (set no-untag-counter 0)
      (set tag-counter 0)
      (set no-tag-counter 0)
      (set may-untag-counter 0)
      (set no-may-untag-counter 0))))

(define* counters-show (subr (maxeff (read @heap) (alloc @heap)) () val)
  (lambda ()
    (vlist3
     (vcons (vint (get tag-counter)) (vint (get no-tag-counter)))
     (vcons (vint (get untag-counter)) (vint (get no-untag-counter)))
     (vcons (vint (get may-untag-counter)) (vint (get no-may-untag-counter))))))

;; tag-show

;; display prog with tagging operation
(define* tag-show (subr (maxeff (read @heap) (write @heap) (alloc @heap)) (val val) val)
  (lambda (tvar-rep prog)
    (if (eqv? tvar-rep dynamic)
        (begin
          (set tag-counter (+ (get tag-counter) 1))
          (vlist2 q-tag prog))
        (begin
          (set no-tag-counter (+ (get no-tag-counter) 1))
          (vlist2 q-no-tag prog)))))

;; untag-show

;; display prog with untagging operation
(define* untag-show (subr (maxeff (read @heap) (write @heap) (alloc @heap)) (val val) val)
  (lambda (tvar-rep prog)
    (if (eqv? tvar-rep dynamic)
        (begin
          (set untag-counter (+ (get untag-counter) 1))
          (vlist2 q-untag prog))
        (begin
          (set no-untag-counter (+ (get no-untag-counter) 1))
          (vlist2 q-no-untag prog)))))

;; display possible untagging in actual arguments
(define* may-untag-show (subr (maxeff (read @heap) (write @heap) (alloc @heap)) (val val) val)
  (lambda (tvar-rep prog)
    (if (eqv? tvar-rep dynamic)
        (begin
          (set may-untag-counter (+ (get may-untag-counter) 1))
          (vlist2 q-may-untag prog))
        (begin
          (set no-may-untag-counter (+ (get no-may-untag-counter) 1))
          (vlist2 q-no-may-untag prog)))))

;; tag-ast-show

;; converts typed and normalized abstract syntax tree to
;; a Scheme program with explicit tagging and untagging operations
(define* tag-ast-show (subr hs (val) val)
  (lambda (ast)
    (let ((syntax-op (vint-of (ast-con ast)))
          (syntax-tvar (find! (ast-tvar ast)))
          (syntax-arg (ast-arg ast)))
      (cond
       ((and (>= syntax-op 0) (<= syntax-op 4))
        (tag-show syntax-tvar syntax-arg))
       ((or (= syntax-op 8) (= syntax-op 10)) syntax-arg)
       ((or (= syntax-op 29) (= syntax-op 31)) v-null)
       ((= syntax-op 30) (vcons (tag-ast-show (vcar syntax-arg))
                                (tag-ast-show (vcdr syntax-arg))))
       ((= syntax-op 32) (vcons (may-untag-show (find! (ast-tvar (vcar syntax-arg)))
                                                (tag-ast-show (vcar syntax-arg)))
                                (tag-ast-show (vcdr syntax-arg))))
       ((= syntax-op 5) (tag-show syntax-tvar (vlist2 q-quote syntax-arg)))
       ((= syntax-op 6) (tag-show syntax-tvar (list->vector (map1 tag-ast-show syntax-arg))))
       ((= syntax-op 7) (tag-show syntax-tvar (vlist3 q-cons (tag-ast-show (vcar syntax-arg))
                                                      (tag-ast-show (vcdr syntax-arg)))))
       ((= syntax-op 9) (ast-arg syntax-arg))
       ((= syntax-op 11) (let ((proc-tvar (find! (ast-tvar (vcar syntax-arg)))))
                           (vcons (untag-show proc-tvar
                                              (tag-ast-show (vcar syntax-arg)))
                                  (tag-ast-show (vcdr syntax-arg)))))
       ((= syntax-op 12) (tag-show syntax-tvar
                                   (vcons q-lambda (vcons (tag-ast-show (vcar syntax-arg))
                                                          (map1 tag-ast-show (vcdr syntax-arg))))))
       ((= syntax-op 13)
        (let ((test-tvar (find! (ast-tvar (vcar syntax-arg)))))
          (vcons q-if (vcons (untag-show test-tvar
                                         (tag-ast-show (vcar syntax-arg)))
                             (vcons (tag-ast-show (vcadr syntax-arg))
                                    (let ((alt (vcddr syntax-arg)))
                                      (if (= (vint-of (ast-con alt)) empty)
                                          v-null
                                          (vlist1 (tag-ast-show alt)))))))))
       ((= syntax-op 14) (vlist3 q-set! (tag-ast-show (vcar syntax-arg))
                                 (tag-ast-show (vcdr syntax-arg))))
       ((= syntax-op 15)
        (vcons q-cond
               (map1 (lambda ((cc val))
                       (let ((guard (vcar cc))
                             (body (vcdr cc)))
                         (vcons
                          (if (= (vint-of (ast-con guard)) empty)
                              q-else
                              (untag-show (find! (ast-tvar guard))
                                          (tag-ast-show guard)))
                          (map1 tag-ast-show body))))
                     syntax-arg)))
       ((= syntax-op 16)
        (vcons q-case
               (vcons (tag-ast-show (vcar syntax-arg))
                      (map1 (lambda ((cc val))
                              (let ((data (vcar cc)))
                                (if (and (vpair? data)
                                         (= (vint-of (ast-con (vcar data))) empty))
                                    (vcons q-else
                                           (map1 tag-ast-show (vcdr cc)))
                                    (vcons (map1 datum-show data)
                                           (map1 tag-ast-show (vcdr cc))))))
                            (vcdr syntax-arg)))))
       ((= syntax-op 17)
        (vcons q-and (map1
                      (lambda ((ast val))
                        (let ((bool-tvar (find! (ast-tvar ast))))
                          (untag-show bool-tvar (tag-ast-show ast))))
                      syntax-arg)))
       ((= syntax-op 18)
        (vcons q-or (map1
                     (lambda ((ast val))
                       (let ((bool-tvar (find! (ast-tvar ast))))
                         (untag-show bool-tvar (tag-ast-show ast))))
                     syntax-arg)))
       ((= syntax-op 19)
        (vcons q-let
               (vcons (map2
                       (lambda ((vd val) (e val))
                         (vlist2 (tag-ast-show vd) (tag-ast-show e)))
                       (vcaar syntax-arg)
                       (vcdar syntax-arg))
                      (map1 tag-ast-show (vcdr syntax-arg)))))
       ((= syntax-op 20)
        (vcons q-let
               (vcons (tag-ast-show (vcar syntax-arg))
                      (vcons (map2
                              (lambda ((vd val) (e val))
                                (vlist2 (tag-ast-show vd) (tag-ast-show e)))
                              (vcaadr syntax-arg)
                              (vcdadr syntax-arg))
                             (map1 tag-ast-show (vcddr syntax-arg))))))
       ((= syntax-op 21)
        (vcons q-let*
               (vcons (map2
                       (lambda ((vd val) (e val))
                         (vlist2 (tag-ast-show vd) (tag-ast-show e)))
                       (vcaar syntax-arg)
                       (vcdar syntax-arg))
                      (map1 tag-ast-show (vcdr syntax-arg)))))
       ((= syntax-op 22)
        (vcons q-letrec
               (vcons (map2
                       (lambda ((vd val) (e val))
                         (vlist2 (tag-ast-show vd) (tag-ast-show e)))
                       (vcaar syntax-arg)
                       (vcdar syntax-arg))
                      (map1 tag-ast-show (vcdr syntax-arg)))))
       ((= syntax-op 23)
        (vcons q-begin
               (map1 tag-ast-show syntax-arg)))
       ((= syntax-op 24) (error "tag-ast-show: Do expressions not handled!"))
       ((= syntax-op 25) (error "tag-ast-show: This can't happen: empty encountered!"))
       ((= syntax-op 26)
        (vlist3 q-define
                (tag-ast-show (vcar syntax-arg))
                (tag-ast-show (vcdr syntax-arg))))
       ((= syntax-op 27)
        (let ((func-tvar (find! (ast-tvar (vcar syntax-arg)))))
          (vlist3 q-define
                  (tag-ast-show (vcar syntax-arg))
                  (tag-show func-tvar
                            (vcons q-lambda
                                   (vcons (tag-ast-show (vcadr syntax-arg))
                                          (map1 tag-ast-show (vcddr syntax-arg))))))))
       ((= syntax-op 28)
        (vcons q-begin
               (map1 tag-ast-show syntax-arg)))
       (else (error "tag-ast-show: Unknown abstract syntax operator"))))))

;; tag-ast*-show

;; display list of commands/expressions with tagging/untagging
;; operations
(define* tag-ast*-show (subr hs (val) val)
  (lambda (p) (map1 tag-ast-show p)))

;;;----------------------------------------------------------------------------
;;; Top level type environment
;;;----------------------------------------------------------------------------

;; Scheme's `(cons 'name type)`, a binding of the environment.
(define* entry (subr (alloc @heap) (symbol val) val)
  (lambda (name type) (vcons (vsym name) type)))

; type environment for miscellaneous

(define misc-env val
  (vlist-of
   (list
    (entry 'quote (forall (lambda ((tv val)) tv)))
    (entry 'eqv? (forall (lambda ((tv val)) (procedure (convert-tvars (vlist2 tv tv))
                                                       (boolean)))))
    (entry 'eq? (forall (lambda ((tv val)) (procedure (convert-tvars (vlist2 tv tv))
                                                      (boolean)))))
    (entry 'equal? (forall (lambda ((tv val)) (procedure (convert-tvars (vlist2 tv tv))
                                                         (boolean))))))))

; type environment for input/output

(define io-env val
  (vlist-of
   (list
    (entry 'open-input-file (procedure (convert-tvars (vlist1 (charseq))) dynamic))
    (entry 'eof-object? (procedure (convert-tvars (vlist1 dynamic)) (boolean)))
    (entry 'read (forall (lambda ((tv val))
                           (procedure (convert-tvars (vlist1 tv)) dynamic))))
    (entry 'write (forall (lambda ((tv val))
                            (procedure (convert-tvars (vlist1 tv)) dynamic))))
    (entry 'display (forall (lambda ((tv val))
                              (procedure (convert-tvars (vlist1 tv)) dynamic))))
    (entry 'newline (procedure (null) dynamic))
    (entry 'pretty-print (forall (lambda ((tv val))
                                   (procedure (convert-tvars (vlist1 tv)) dynamic)))))))

; type environment for Booleans

(define boolean-env val
  (vlist-of
   (list
    (entry 'boolean? (forall (lambda ((tv val))
                               (procedure (convert-tvars (vlist1 tv)) (boolean)))))
    ;(cons #f (boolean))
    ; #f doesn't exist in Chez Scheme, but gets mapped to null!
    (vcons v-true (boolean))
    (entry 'not (procedure (convert-tvars (vlist1 (boolean))) (boolean))))))

; type environment for pairs and lists

(define* list-type (subr (maxeff hs tvfun) (val) val)
  (lambda (tv)
    (fix (lambda ((tv2 val)) (pair tv tv2)))))

(define list-env val
  (vlist-of
   (list
    (entry 'pair? (forall2 (lambda ((tv1 val) (tv2 val))
                             (procedure (convert-tvars (vlist1 (pair tv1 tv2)))
                                        (boolean)))))
    (entry 'null? (forall2 (lambda ((tv1 val) (tv2 val))
                             (procedure (convert-tvars (vlist1 (pair tv1 tv2)))
                                        (boolean)))))
    (entry 'list? (forall2 (lambda ((tv1 val) (tv2 val))
                             (procedure (convert-tvars (vlist1 (pair tv1 tv2)))
                                        (boolean)))))
    (entry 'cons (forall2 (lambda ((tv1 val) (tv2 val))
                            (procedure (convert-tvars (vlist2 tv1 tv2))
                                       (pair tv1 tv2)))))
    (entry 'car (forall2 (lambda ((tv1 val) (tv2 val))
                           (procedure (convert-tvars (vlist1 (pair tv1 tv2)))
                                      tv1))))
    (entry 'cdr (forall2 (lambda ((tv1 val) (tv2 val))
                           (procedure (convert-tvars (vlist1 (pair tv1 tv2)))
                                      tv2))))
    (entry 'set-car! (forall2 (lambda ((tv1 val) (tv2 val))
                                (procedure (convert-tvars (vlist2 (pair tv1 tv2)
                                                                  tv1))
                                           dynamic))))
    (entry 'set-cdr! (forall2 (lambda ((tv1 val) (tv2 val))
                                (procedure (convert-tvars (vlist2 (pair tv1 tv2)
                                                                  tv2))
                                           dynamic))))
    (entry 'caar (forall3 (lambda ((tv1 val) (tv2 val) (tv3 val))
                            (procedure (convert-tvars
                                        (vlist1 (pair (pair tv1 tv2) tv3)))
                                       tv1))))
    (entry 'cdar (forall3 (lambda ((tv1 val) (tv2 val) (tv3 val))
                            (procedure (convert-tvars
                                        (vlist1 (pair (pair tv1 tv2) tv3)))
                                       tv2))))

    (entry 'cadr (forall3 (lambda ((tv1 val) (tv2 val) (tv3 val))
                            (procedure (convert-tvars
                                        (vlist1 (pair tv1 (pair tv2 tv3))))
                                       tv2))))
    (entry 'cddr (forall3 (lambda ((tv1 val) (tv2 val) (tv3 val))
                            (procedure (convert-tvars
                                        (vlist1 (pair tv1 (pair tv2 tv3))))
                                       tv3))))
    (entry 'caaar (forall4
                   (lambda ((tv1 val) (tv2 val) (tv3 val) (tv4 val))
                     (procedure (convert-tvars
                                 (vlist1 (pair (pair (pair tv1 tv2) tv3) tv4)))
                                tv1))))
    (entry 'cdaar (forall4
                   (lambda ((tv1 val) (tv2 val) (tv3 val) (tv4 val))
                     (procedure (convert-tvars
                                 (vlist1 (pair (pair (pair tv1 tv2) tv3) tv4)))
                                tv2))))
    (entry 'cadar (forall4
                   (lambda ((tv1 val) (tv2 val) (tv3 val) (tv4 val))
                     (procedure (convert-tvars
                                 (vlist1 (pair (pair tv1 (pair tv2 tv3)) tv4)))
                                tv2))))
    (entry 'cddar (forall4
                   (lambda ((tv1 val) (tv2 val) (tv3 val) (tv4 val))
                     (procedure (convert-tvars
                                 (vlist1 (pair (pair tv1 (pair tv2 tv3)) tv4)))
                                tv3))))
    (entry 'caadr (forall4
                   (lambda ((tv1 val) (tv2 val) (tv3 val) (tv4 val))
                     (procedure (convert-tvars
                                 (vlist1 (pair tv1 (pair (pair tv2 tv3) tv4))))
                                tv2))))
    (entry 'cdadr (forall4
                   (lambda ((tv1 val) (tv2 val) (tv3 val) (tv4 val))
                     (procedure (convert-tvars
                                 (vlist1 (pair tv1 (pair (pair tv2 tv3) tv4))))
                                tv3))))
    (entry 'caddr (forall4
                   (lambda ((tv1 val) (tv2 val) (tv3 val) (tv4 val))
                     (procedure (convert-tvars
                                 (vlist1 (pair tv1 (pair tv2 (pair tv3 tv4)))))
                                tv3))))
    (entry 'cdddr (forall4
                   (lambda ((tv1 val) (tv2 val) (tv3 val) (tv4 val))
                     (procedure (convert-tvars
                                 (vlist1 (pair tv1 (pair tv2 (pair tv3 tv4)))))
                                tv4))))
    (entry 'cadddr
           (forall5 (lambda ((tv1 val) (tv2 val) (tv3 val) (tv4 val) (tv5 val))
                      (procedure (convert-tvars
                                  (vlist1 (pair tv1
                                                (pair tv2
                                                      (pair tv3
                                                            (pair tv4 tv5))))))
                                 tv4))))
    (entry 'cddddr
           (forall5 (lambda ((tv1 val) (tv2 val) (tv3 val) (tv4 val) (tv5 val))
                      (procedure (convert-tvars
                                  (vlist1 (pair tv1
                                                (pair tv2
                                                      (pair tv3
                                                            (pair tv4 tv5))))))
                                 tv5))))
    (entry 'list (forall (lambda ((tv val))
                           (procedure tv tv))))
    (entry 'length (forall (lambda ((tv val))
                             (procedure (convert-tvars (vlist1 (list-type tv)))
                                        (number)))))
    (entry 'append (forall (lambda ((tv val))
                             (procedure (convert-tvars (vlist2 (list-type tv)
                                                               (list-type tv)))
                                        (list-type tv)))))
    (entry 'reverse (forall (lambda ((tv val))
                              (procedure (convert-tvars (vlist1 (list-type tv)))
                                         (list-type tv)))))
    (entry 'list-ref (forall (lambda ((tv val))
                               (procedure (convert-tvars (vlist2 (list-type tv)
                                                                 (number)))
                                          tv))))
    (entry 'memq (forall (lambda ((tv val))
                           (procedure (convert-tvars (vlist2 tv
                                                             (list-type tv)))
                                      (boolean)))))
    (entry 'memv (forall (lambda ((tv val))
                           (procedure (convert-tvars (vlist2 tv
                                                             (list-type tv)))
                                      (boolean)))))
    (entry 'member (forall (lambda ((tv val))
                             (procedure (convert-tvars (vlist2 tv
                                                               (list-type tv)))
                                        (boolean)))))
    (entry 'assq (forall2 (lambda ((tv1 val) (tv2 val))
                            (procedure (convert-tvars
                                        (vlist2 tv1
                                                (list-type (pair tv1 tv2))))
                                       (pair tv1 tv2)))))
    (entry 'assv (forall2 (lambda ((tv1 val) (tv2 val))
                            (procedure (convert-tvars
                                        (vlist2 tv1
                                                (list-type (pair tv1 tv2))))
                                       (pair tv1 tv2)))))
    (entry 'assoc (forall2 (lambda ((tv1 val) (tv2 val))
                             (procedure (convert-tvars
                                         (vlist2 tv1
                                                 (list-type (pair tv1 tv2))))
                                        (pair tv1 tv2))))))))

(define symbol-env val
  (vlist-of
   (list
    (entry 'symbol? (forall (lambda ((tv val))
                              (procedure (convert-tvars (vlist1 tv)) (boolean)))))
    (entry 'symbol->string (procedure (convert-tvars (vlist1 (symbol))) (charseq)))
    (entry 'string->symbol (procedure (convert-tvars (vlist1 (charseq))) (symbol))))))

(define number-env val
  (vlist-of
   (list
    (entry 'number? (forall (lambda ((tv val))
                              (procedure (convert-tvars (vlist1 tv)) (boolean)))))
    (entry '+ (procedure (convert-tvars (vlist2 (number) (number))) (number)))
    (entry '- (procedure (convert-tvars (vlist2 (number) (number))) (number)))
    (entry '* (procedure (convert-tvars (vlist2 (number) (number))) (number)))
    (entry '/ (procedure (convert-tvars (vlist2 (number) (number))) (number)))
    (entry 'number->string (procedure (convert-tvars (vlist1 (number))) (charseq)))
    (entry 'string->number (procedure (convert-tvars (vlist1 (charseq))) (number))))))

(define char-env val
  (vlist-of
   (list
    (entry 'char? (forall (lambda ((tv val))
                            (procedure (convert-tvars (vlist1 tv)) (boolean)))))
    (entry 'char->integer (procedure (convert-tvars (vlist1 (character)))
                                     (number)))
    (entry 'integer->char (procedure (convert-tvars (vlist1 (number)))
                                     (character))))))

(define string-env val
  (vlist-of
   (list
    (entry 'string? (forall (lambda ((tv val))
                              (procedure (convert-tvars (vlist1 tv)) (boolean))))))))

(define vector-env val
  (vlist-of
   (list
    (entry 'vector? (forall (lambda ((tv val))
                              (procedure (convert-tvars (vlist1 tv)) (boolean)))))
    (entry 'make-vector (forall (lambda ((tv val))
                                  (procedure (convert-tvars (vlist1 (number)))
                                             (array tv)))))
    (entry 'vector-length (forall (lambda ((tv val))
                                    (procedure (convert-tvars (vlist1 (array tv)))
                                               (number)))))
    (entry 'vector-ref (forall (lambda ((tv val))
                                 (procedure (convert-tvars (vlist2 (array tv)
                                                                   (number)))
                                            tv))))
    (entry 'vector-set! (forall (lambda ((tv val))
                                  (procedure (convert-tvars (vlist3 (array tv)
                                                                    (number)
                                                                    tv))
                                             dynamic)))))))

(define procedure-env val
  (vlist-of
   (list
    (entry 'procedure? (forall (lambda ((tv val))
                                 (procedure (convert-tvars (vlist1 tv)) (boolean)))))
    (entry 'map (forall2 (lambda ((tv1 val) (tv2 val))
                           (procedure (convert-tvars
                                       (vlist2 (procedure (convert-tvars
                                                           (vlist1 tv1)) tv2)
                                               (list-type tv1)))
                                      (list-type tv2)))))
    (entry 'foreach (forall2 (lambda ((tv1 val) (tv2 val))
                               (procedure (convert-tvars
                                           (vlist2 (procedure (convert-tvars
                                                               (vlist1 tv1)) tv2)
                                                   (list-type tv1)))
                                          (list-type tv2)))))
    (entry 'call-with-current-continuation
           (forall2 (lambda ((tv1 val) (tv2 val))
                      (procedure (convert-tvars
                                  (vlist1 (procedure
                                           (convert-tvars
                                            (vlist1 (procedure (convert-tvars
                                                                (vlist1 tv1)) tv2)))
                                           tv2)))
                                 tv2)))))))

; global top level environment

(define* global-env (subr hs () val)
  (lambda ()
    (vappend misc-env
     (vappend io-env
      (vappend boolean-env
       (vappend symbol-env
        (vappend number-env
         (vappend char-env
          (vappend string-env
           (vappend vector-env
            (vappend procedure-env
                     list-env)))))))))))

(define* init-dynamic-top-level-env! (subr hs () val)
  (lambda ()
    (begin (set dynamic-top-level-env (global-env))
           v-null)))

;;;----------------------------------------------------------------------------
;;; Dynamic type inference for Scheme
;;;----------------------------------------------------------------------------

(define tag-ops (ref int @heap) (new 0))
(define no-ops (ref int @heap) (new 0))

(define* ic! (subr hs () unit) (lambda () (init-global-constraints!)))
(define* it! (subr hs () val) (lambda () (init-dynamic-top-level-env!)))
(define* io! (subr hs () unit) (lambda () (begin (set tag-ops 0) (set no-ops 0))))
(define* i! (subr hs () val) (lambda () (begin (ic!) (it!) (io!) v-null)))

(define* doit (subr parses (string) val)
  (lambda (input-file)
    (begin
      (i!)
      (let ((foo (dynamic-parse-file input-file)))
        (begin
          (normalize-global-constraints!)
          (reset-counters!)
          (tag-ast*-show foo)
          (counters-show))))))

;; The answer, as a datum to print.
(define* val->datum (subr (maxeff (read @heap) (alloc @heap) spin) (val) datum)
  (lambda (x)
    (tagcase x
      (vnull () (datum-list (the (listof datum @heap) nil)))
      (vbool (b) (datum-bool b))
      (vchar (c) (datum-char c))
      (vint (n) (datum-int n))
      (vstr (s) (datum-string s))
      (vsym (s) (datum-symbol (symbol->string s)))
      (vpair (p) (datum-cons (val->datum (car p)) (val->datum (cdr p))))
      (vvec (v) (datum-symbol "#<vector>"))
      (vproc (f) (datum-symbol "#<procedure>"))
      (veof () (datum-symbol "#<eof>")))))

;; Larceny's input file, inputs/dynamic.data, verbatim; `read-datum` reads it.
(define input-text string ";;; DYNAMIC -- Obtained from Andrew Wright.

;; Fritz's dynamic type inferencer, set up to run on itself
;; (see the end of this file).

;----------------------------------------------------------------------------
; Environment management
;----------------------------------------------------------------------------

;; environments are lists of pairs, the first component being the key

;; general environment operations
;;
;; empty-env: Env
;; gen-binding: Key x Value -> Binding
;; binding-key: Binding -> Key
;; binding-value: Binding -> Value
;; binding-show: Binding -> Symbol*
;; extend-env-with-binding: Env x Binding -> Env
;; extend-env-with-env: Env x Env -> Env
;; lookup: Key x Env -> (Binding + False)
;; env->list: Env -> Binding*
;; env-show: Env -> Symbol*


; bindings

(define gen-binding cons)
; generates a type binding, binding a symbol to a type variable

(define binding-key car)
; returns the key of a type binding

(define binding-value cdr)
; returns the tvariable of a type binding

(define (key-show key)
  ; default show procedure for keys
  key)

(define (value-show value)
  ; default show procedure for values
  value)

(define (binding-show binding)
  ; returns a printable representation of a type binding
  (cons (key-show (binding-key binding))
        (cons ': (value-show (binding-value binding)))))


; environments

(define dynamic-empty-env '())
; returns the empty environment

(define (extend-env-with-binding env binding)
  ; extends env with a binding, which hides any other binding in env
  ; for the same key (see dynamic-lookup)
  ; returns the extended environment
  (cons binding env))

(define (extend-env-with-env env ext-env)
  ; extends environment env with environment ext-env 
  ; a binding for a key in ext-env hides any binding in env for
  ; the same key (see dynamic-lookup)
  ; returns the extended environment
  (append ext-env env))

(define dynamic-lookup (lambda (x l) (assv x l)))
; returns the first pair in env that matches the key; returns #f
; if no such pair exists

(define (env->list e)
  ; converts an environment to a list of bindings
  e)

(define (env-show env)
  ; returns a printable list representation of a type environment
  (map binding-show env))
;----------------------------------------------------------------------------
;       Parsing for Scheme
;----------------------------------------------------------------------------


;; Needed packages: environment management

;(load \"env-mgmt.ss\")
;(load \"pars-act.ss\")

;; Lexical notions

(define syntactic-keywords
  ;; source: IEEE Scheme, 7.1, <expression keyword>, <syntactic keyword>
  '(lambda if set! begin cond and or case let let* letrec do
          quasiquote else => define unquote unquote-splicing))


;; Parse routines

; Datum

; dynamic-parse-datum: parses nonterminal <datum>

(define (dynamic-parse-datum e)
  ;; Source: IEEE Scheme, sect. 7.2, <datum>
  ;; Note: \"'\" is parsed as 'quote, \"`\" as 'quasiquote, \",\" as
  ;; 'unquote, \",@\" as 'unquote-splicing (see sect. 4.2.5, p. 18)
  ;; ***Note***: quasi-quotations are not permitted! (It would be
  ;; necessary to pass the environment to dynamic-parse-datum.)
  (cond
   ((null? e)
    (dynamic-parse-action-null-const))
   ((boolean? e)
    (dynamic-parse-action-boolean-const e))
   ((char? e)
    (dynamic-parse-action-char-const e))
   ((number? e)
    (dynamic-parse-action-number-const e))
   ((string? e)
    (dynamic-parse-action-string-const e))
   ((symbol? e)
    (dynamic-parse-action-symbol-const e))
   ((vector? e)
    (dynamic-parse-action-vector-const (map dynamic-parse-datum (vector->list e))))
   ((pair? e)
    (dynamic-parse-action-pair-const (dynamic-parse-datum (car e))
                             (dynamic-parse-datum (cdr e))))
   (else (fatal-error 'dynamic-parse-datum \"Unknown datum: ~s\" e))))


; VarDef

; dynamic-parse-formal: parses nonterminal <variable> in defining occurrence position

(define (dynamic-parse-formal f-env e)
  ; e is an arbitrary object, f-env is a forbidden environment;
  ; returns: a variable definition (a binding for the symbol), plus
  ; the value of the binding as a result
  (if (symbol? e)
      (cond
       ((memq e syntactic-keywords)
        (fatal-error 'dynamic-parse-formal \"Illegal identifier (keyword): ~s\" e))
       ((dynamic-lookup e f-env)
        (fatal-error 'dynamic-parse-formal \"Duplicate variable definition: ~s\" e))
       (else (let ((dynamic-parse-action-result (dynamic-parse-action-var-def e)))
               (cons (gen-binding e dynamic-parse-action-result)
                     dynamic-parse-action-result))))
      (fatal-error 'dynamic-parse-formal \"Not an identifier: ~s\" e)))

; dynamic-parse-formal*

(define (dynamic-parse-formal* formals)
  ;; parses a list of formals and returns a pair consisting of generated
  ;; environment and list of parsing action results
  (letrec
      ((pf*
        (lambda (f-env results formals)
          ;; f-env: \"forbidden\" environment (to avoid duplicate defs)
          ;; results: the results of the parsing actions
          ;; formals: the unprocessed formals
          ;; Note: generates the results of formals in reverse order!
          (cond
           ((null? formals)
            (cons f-env results))
           ((pair? formals)
            (let* ((fst-formal (car formals))
                   (binding-result (dynamic-parse-formal f-env fst-formal))
                   (binding (car binding-result))
                   (var-result (cdr binding-result)))
              (pf*
               (extend-env-with-binding f-env binding)
               (cons var-result results)
               (cdr formals))))
           (else (fatal-error 'dynamic-parse-formal* \"Illegal formals: ~s\" formals))))))
    (let ((renv-rres (pf* dynamic-empty-env '() formals)))
      (cons (car renv-rres) (reverse (cdr renv-rres))))))


; dynamic-parse-formals: parses <formals>

(define (dynamic-parse-formals formals)
  ;; parses <formals>; see IEEE Scheme, sect. 7.3
  ;; returns a pair: env and result
  (letrec ((pfs (lambda (f-env formals)
                  (cond
                   ((null? formals)
                    (cons dynamic-empty-env (dynamic-parse-action-null-formal)))
                   ((pair? formals)
                    (let* ((fst-formal (car formals))
                           (rem-formals (cdr formals))
                           (bind-res (dynamic-parse-formal f-env fst-formal))
                           (bind (car bind-res))
                           (res (cdr bind-res))
                           (nf-env (extend-env-with-binding f-env bind))
                           (renv-res* (pfs nf-env rem-formals))
                           (renv (car renv-res*))
                           (res* (cdr renv-res*)))
                      (cons
                       (extend-env-with-binding renv bind)
                       (dynamic-parse-action-pair-formal res res*))))
                   (else
                    (let* ((bind-res (dynamic-parse-formal f-env formals))
                           (bind (car bind-res))
                           (res (cdr bind-res)))
                      (cons
                       (extend-env-with-binding dynamic-empty-env bind)
                       res)))))))
    (pfs dynamic-empty-env formals)))


; Expr

; dynamic-parse-expression: parses nonterminal <expression>

(define (dynamic-parse-expression env e)
  (cond
   ((symbol? e)
    (dynamic-parse-variable env e))
   ((pair? e)
    (let ((op (car e)) (args (cdr e)))
      (case op
        ((quote) (dynamic-parse-quote env args))
        ((lambda) (dynamic-parse-lambda env args))
        ((if) (dynamic-parse-if env args))
        ((set!) (dynamic-parse-set env args))
        ((begin) (dynamic-parse-begin env args))
        ((cond) (dynamic-parse-cond env args))
        ((case) (dynamic-parse-case env args))
        ((and) (dynamic-parse-and env args))
        ((or) (dynamic-parse-or env args))
        ((let) (dynamic-parse-let env args))
        ((let*) (dynamic-parse-let* env args))
        ((letrec) (dynamic-parse-letrec env args))
        ((do) (dynamic-parse-do env args))
        ((quasiquote) (dynamic-parse-quasiquote env args))
        (else (dynamic-parse-procedure-call env op args)))))
   (else (dynamic-parse-datum e))))

; dynamic-parse-expression*

(define (dynamic-parse-expression* env exprs)
  ;; Parses lists of expressions (returns them in the right order!)
  (letrec ((pe*
            (lambda (results es)
              (cond
               ((null? es) results)
               ((pair? es) (pe* (cons (dynamic-parse-expression env (car es)) results) (cdr es)))
               (else (fatal-error 'dynamic-parse-expression* \"Not a list of expressions: ~s\" es))))))
    (reverse (pe* '() exprs))))


; dynamic-parse-expressions

(define (dynamic-parse-expressions env exprs)
  ;; parses lists of arguments of a procedure call
  (cond
   ((null? exprs) (dynamic-parse-action-null-arg))
   ((pair? exprs) (let* ((fst-expr (car exprs))
                         (rem-exprs (cdr exprs))
                         (fst-res (dynamic-parse-expression env fst-expr))
                         (rem-res (dynamic-parse-expressions env rem-exprs)))
                    (dynamic-parse-action-pair-arg fst-res rem-res)))
   (else (fatal-error 'dynamic-parse-expressions \"Illegal expression list: ~s\"
                exprs))))


; dynamic-parse-variable: parses variables (applied occurrences)

(define (dynamic-parse-variable env e)
  (if (symbol? e)
      (if (memq e syntactic-keywords)
          (fatal-error 'dynamic-parse-variable \"Illegal identifier (keyword): ~s\" e)
          (let ((assoc-var-def (dynamic-lookup e env)))
            (if assoc-var-def
                (dynamic-parse-action-variable (binding-value assoc-var-def))
                (dynamic-parse-action-identifier e))))
      (fatal-error 'dynamic-parse-variable \"Not an identifier: ~s\" e)))


; dynamic-parse-procedure-call

(define (dynamic-parse-procedure-call env op args)
  (dynamic-parse-action-procedure-call
   (dynamic-parse-expression env op)
   (dynamic-parse-expressions env args)))


; dynamic-parse-quote

(define (dynamic-parse-quote env args)
  (if (list-of-1? args)
      (dynamic-parse-datum (car args))
      (fatal-error 'dynamic-parse-quote \"Not a datum (multiple arguments): ~s\" args)))


; dynamic-parse-lambda

(define (dynamic-parse-lambda env args)
  (if (pair? args)
      (let* ((formals (car args))
             (body (cdr args))
             (nenv-fresults (dynamic-parse-formals formals))
             (nenv (car nenv-fresults))
             (fresults (cdr nenv-fresults)))
        (dynamic-parse-action-lambda-expression
         fresults
         (dynamic-parse-body (extend-env-with-env env nenv) body)))
      (fatal-error 'dynamic-parse-lambda \"Illegal formals/body: ~s\" args)))


; dynamic-parse-body

(define (dynamic-parse-body env body)
  ; <body> = <definition>* <expression>+
  (define (def-var* f-env body)
    ; finds the defined variables in a body and returns an 
    ; environment containing them
    (if (pair? body)
        (let ((n-env (def-var f-env (car body))))
          (if n-env
              (def-var* n-env (cdr body))
              f-env))
        f-env))
  (define (def-var f-env clause)
    ; finds the defined variables in a single clause and extends
    ; f-env accordingly; returns false if it's not a definition
    (if (pair? clause)
        (case (car clause)
          ((define) (if (pair? (cdr clause))
                        (let ((pattern (cadr clause)))
                          (cond
                           ((symbol? pattern)
                            (extend-env-with-binding 
                             f-env 
                             (gen-binding pattern
                                          (dynamic-parse-action-var-def pattern))))
                           ((and (pair? pattern) (symbol? (car pattern)))
                            (extend-env-with-binding
                             f-env
                             (gen-binding (car pattern)
                                          (dynamic-parse-action-var-def 
                                           (car pattern)))))
                           (else f-env)))
                        f-env))
          ((begin) (def-var* f-env (cdr clause)))
          (else #f))
        #f))
  (if (pair? body)
      (dynamic-parse-command* (def-var* env body) body)
      (fatal-error 'dynamic-parse-body \"Illegal body: ~s\" body)))

; dynamic-parse-if

(define (dynamic-parse-if env args)
  (cond
   ((list-of-3? args)
    (dynamic-parse-action-conditional
     (dynamic-parse-expression env (car args))
     (dynamic-parse-expression env (cadr args))
     (dynamic-parse-expression env (caddr args))))
   ((list-of-2? args)
    (dynamic-parse-action-conditional
     (dynamic-parse-expression env (car args))
     (dynamic-parse-expression env (cadr args))
     (dynamic-parse-action-empty)))
   (else (fatal-error 'dynamic-parse-if \"Not an if-expression: ~s\" args))))


; dynamic-parse-set

(define (dynamic-parse-set env args)
  (if (list-of-2? args)
      (dynamic-parse-action-assignment
       (dynamic-parse-variable env (car args))
       (dynamic-parse-expression env (cadr args)))
      (fatal-error 'dynamic-parse-set \"Not a variable/expression pair: ~s\" args)))


; dynamic-parse-begin

(define (dynamic-parse-begin env args)
  (dynamic-parse-action-begin-expression
   (dynamic-parse-body env args)))


; dynamic-parse-cond

(define (dynamic-parse-cond env args)
  (if (and (pair? args) (list? args))
      (dynamic-parse-action-cond-expression
       (map (lambda (e)
              (dynamic-parse-cond-clause env e))
            args))
      (fatal-error 'dynamic-parse-cond \"Not a list of cond-clauses: ~s\" args)))

; dynamic-parse-cond-clause

(define (dynamic-parse-cond-clause env e)
  ;; ***Note***: Only (<test> <sequence>) is permitted!
  (if (pair? e)
      (cons
       (if (eqv? (car e) 'else)
           (dynamic-parse-action-empty)
           (dynamic-parse-expression env (car e)))
       (dynamic-parse-body env (cdr e)))
      (fatal-error 'dynamic-parse-cond-clause \"Not a cond-clause: ~s\" e)))


; dynamic-parse-and

(define (dynamic-parse-and env args)
  (if (list? args)
      (dynamic-parse-action-and-expression
       (dynamic-parse-expression* env args))
      (fatal-error 'dynamic-parse-and \"Not a list of arguments: ~s\" args)))


; dynamic-parse-or

(define (dynamic-parse-or env args)
  (if (list? args)
      (dynamic-parse-action-or-expression
       (dynamic-parse-expression* env args))
      (fatal-error 'dynamic-parse-or \"Not a list of arguments: ~s\" args)))


; dynamic-parse-case

(define (dynamic-parse-case env args)
  (if (and (list? args) (> (length args) 1))
      (dynamic-parse-action-case-expression
       (dynamic-parse-expression env (car args))
       (map (lambda (e)
               (dynamic-parse-case-clause env e))
             (cdr args)))
      (fatal-error 'dynamic-parse-case \"Not a list of clauses: ~s\" args)))

; dynamic-parse-case-clause

(define (dynamic-parse-case-clause env e)
  (if (pair? e)
      (cons
       (cond
        ((eqv? (car e) 'else)
         (list (dynamic-parse-action-empty)))
        ((list? (car e))
         (map dynamic-parse-datum (car e)))
        (else (fatal-error 'dynamic-parse-case-clause \"Not a datum list: ~s\" (car e))))
       (dynamic-parse-body env (cdr e)))
      (fatal-error 'dynamic-parse-case-clause \"Not case clause: ~s\" e)))


; dynamic-parse-let

(define (dynamic-parse-let env args)
  (if (pair? args)
      (if (symbol? (car args))
          (dynamic-parse-named-let env args)
          (dynamic-parse-normal-let env args))
      (fatal-error 'dynamic-parse-let \"Illegal bindings/body: ~s\" args)))


; dynamic-parse-normal-let

(define (dynamic-parse-normal-let env args)
  ;; parses \"normal\" let-expressions
  (let* ((bindings (car args))
         (body (cdr args))
         (env-ast (dynamic-parse-parallel-bindings env bindings))
         (nenv (car env-ast))
         (bresults (cdr env-ast)))
    (dynamic-parse-action-let-expression
     bresults
     (dynamic-parse-body (extend-env-with-env env nenv) body))))

; dynamic-parse-named-let

(define (dynamic-parse-named-let env args)
  ;; parses a named let-expression
  (if (pair? (cdr args))
      (let* ((variable (car args))
             (bindings (cadr args))
             (body (cddr args))
             (vbind-vres (dynamic-parse-formal dynamic-empty-env variable))
             (vbind (car vbind-vres))
             (vres (cdr vbind-vres))
             (env-ast (dynamic-parse-parallel-bindings env bindings))
             (nenv (car env-ast))
             (bresults (cdr env-ast)))
        (dynamic-parse-action-named-let-expression
         vres bresults
         (dynamic-parse-body (extend-env-with-env 
                      (extend-env-with-binding env vbind)
                      nenv) body)))
      (fatal-error 'dynamic-parse-named-let \"Illegal named let-expression: ~s\" args)))


; dynamic-parse-parallel-bindings

(define (dynamic-parse-parallel-bindings env bindings)
  ; returns a pair consisting of an environment
  ; and a list of pairs (variable . asg)
  ; ***Note***: the list of pairs is returned in reverse unzipped form!
  (if (list-of-list-of-2s? bindings)
      (let* ((env-formals-asg
             (dynamic-parse-formal* (map car bindings)))
            (nenv (car env-formals-asg))
            (bresults (cdr env-formals-asg))
            (exprs-asg
             (dynamic-parse-expression* env (map cadr bindings))))
        (cons nenv (cons bresults exprs-asg)))
      (fatal-error 'dynamic-parse-parallel-bindings
             \"Not a list of bindings: ~s\" bindings)))


; dynamic-parse-let*

(define (dynamic-parse-let* env args)
  (if (pair? args)
      (let* ((bindings (car args))
             (body (cdr args))
             (env-ast (dynamic-parse-sequential-bindings env bindings))
             (nenv (car env-ast))
             (bresults (cdr env-ast)))
        (dynamic-parse-action-let*-expression
         bresults
         (dynamic-parse-body (extend-env-with-env env nenv) body)))
      (fatal-error 'dynamic-parse-let* \"Illegal bindings/body: ~s\" args)))

; dynamic-parse-sequential-bindings

(define (dynamic-parse-sequential-bindings env bindings)
  ; returns a pair consisting of an environment
  ; and a list of pairs (variable . asg)
  ;; ***Note***: the list of pairs is returned in reverse unzipped form!
  (letrec
      ((psb
        (lambda (f-env c-env var-defs expr-asgs binds)
          ;; f-env: forbidden environment
          ;; c-env: constructed environment
          ;; var-defs: results of formals
          ;; expr-asgs: results of corresponding expressions
          ;; binds: reminding bindings to process
          (cond
           ((null? binds)
            (cons f-env (cons var-defs expr-asgs)))
           ((pair? binds)
            (let ((fst-bind (car binds)))
              (if (list-of-2? fst-bind)
                  (let* ((fbinding-bres
                          (dynamic-parse-formal f-env (car fst-bind)))
                         (fbind (car fbinding-bres))
                         (bres (cdr fbinding-bres))
                         (new-expr-asg
                          (dynamic-parse-expression c-env (cadr fst-bind))))
                    (psb
                     (extend-env-with-binding f-env fbind)
                     (extend-env-with-binding c-env fbind)
                     (cons bres var-defs)
                     (cons new-expr-asg expr-asgs)
                     (cdr binds)))
                  (fatal-error 'dynamic-parse-sequential-bindings
                         \"Illegal binding: ~s\" fst-bind))))
           (else (fatal-error 'dynamic-parse-sequential-bindings
                        \"Illegal bindings: ~s\" binds))))))
    (let ((env-vdefs-easgs (psb dynamic-empty-env env '() '() bindings)))
      (cons (car env-vdefs-easgs)
            (cons (reverse (cadr env-vdefs-easgs))
                  (reverse (cddr env-vdefs-easgs)))))))


; dynamic-parse-letrec

(define (dynamic-parse-letrec env args)
  (if (pair? args)
      (let* ((bindings (car args))
             (body (cdr args))
             (env-ast (dynamic-parse-recursive-bindings env bindings))
             (nenv (car env-ast))
             (bresults (cdr env-ast)))
        (dynamic-parse-action-letrec-expression
          bresults
          (dynamic-parse-body (extend-env-with-env env nenv) body)))
      (fatal-error 'dynamic-parse-letrec \"Illegal bindings/body: ~s\" args)))

; dynamic-parse-recursive-bindings

(define (dynamic-parse-recursive-bindings env bindings)
  ;; ***Note***: the list of pairs is returned in reverse unzipped form!
  (if (list-of-list-of-2s? bindings)
      (let* ((env-formals-asg
              (dynamic-parse-formal* (map car bindings)))
             (formals-env
              (car env-formals-asg))
             (formals-res
              (cdr env-formals-asg))
             (exprs-asg
              (dynamic-parse-expression*
               (extend-env-with-env env formals-env)
               (map cadr bindings))))
        (cons
         formals-env
         (cons formals-res exprs-asg)))
      (fatal-error 'dynamic-parse-recursive-bindings \"Illegal bindings: ~s\" bindings)))


; dynamic-parse-do

(define (dynamic-parse-do env args)
  ;; parses do-expressions
  ;; ***Note***: Not implemented!
  (fatal-error 'dynamic-parse-do \"Nothing yet...\"))

; dynamic-parse-quasiquote

(define (dynamic-parse-quasiquote env args)
  ;; ***Note***: Not implemented!
  (fatal-error 'dynamic-parse-quasiquote \"Nothing yet...\"))


;; Command

; dynamic-parse-command

(define (dynamic-parse-command env c)
  (if (pair? c)
      (let ((op (car c))
            (args (cdr c)))
        (case op
         ((define) (dynamic-parse-define env args))
;        ((begin) (dynamic-parse-command* env args))  ;; AKW
         ((begin) (dynamic-parse-action-begin-expression (dynamic-parse-command* env args)))
         (else (dynamic-parse-expression env c))))
      (dynamic-parse-expression env c)))


; dynamic-parse-command*

(define (dynamic-parse-command* env commands)
  ;; parses a sequence of commands
  (if (list? commands)
      (map (lambda (command) (dynamic-parse-command env command)) commands)
      (fatal-error 'dynamic-parse-command* \"Invalid sequence of commands: ~s\" commands)))


; dynamic-parse-define

(define (dynamic-parse-define env args)
  ;; three cases -- see IEEE Scheme, sect. 5.2
  ;; ***Note***: the parser admits forms (define (x . y) ...)
  ;; ***Note***: Variables are treated as applied occurrences!
  (if (pair? args)
      (let ((pattern (car args))
            (exp-or-body (cdr args)))
        (cond
         ((symbol? pattern)
          (if (list-of-1? exp-or-body)
              (dynamic-parse-action-definition
               (dynamic-parse-variable env pattern)
               (dynamic-parse-expression env (car exp-or-body)))
              (fatal-error 'dynamic-parse-define \"Not a single expression: ~s\" exp-or-body)))
         ((pair? pattern)
          (let* ((function-name (car pattern))
                 (function-arg-names (cdr pattern))
                 (env-ast (dynamic-parse-formals function-arg-names))
                 (formals-env (car env-ast))
                 (formals-ast (cdr env-ast)))
            (dynamic-parse-action-function-definition
             (dynamic-parse-variable env function-name)
             formals-ast
             (dynamic-parse-body (extend-env-with-env env formals-env) exp-or-body))))
         (else (fatal-error 'dynamic-parse-define \"Not a valid pattern: ~s\" pattern))))
      (fatal-error 'dynamic-parse-define \"Not a valid definition: ~s\" args)))

;; Auxiliary routines

; forall?

(define (forall? pred list)
  (if (null? list)
      #t
      (and (pred (car list)) (forall? pred (cdr list)))))

; list-of-1?

(define (list-of-1? l)
  (and (pair? l) (null? (cdr l))))

; list-of-2?

(define (list-of-2? l)
  (and (pair? l) (pair? (cdr l)) (null? (cddr l))))

; list-of-3?

(define (list-of-3? l)
  (and (pair? l) (pair? (cdr l)) (pair? (cddr l)) (null? (cdddr l))))

; list-of-list-of-2s?

(define (list-of-list-of-2s? e)
  (cond
   ((null? e)
    #t)
   ((pair? e)
    (and (list-of-2? (car e)) (list-of-list-of-2s? (cdr e))))
   (else #f)))


;; File processing

; dynamic-parse-from-port

(define (dynamic-parse-from-port port)
  (let ((next-input (read port)))
    (if (eof-object? next-input)
        '()
        (dynamic-parse-action-commands
         (dynamic-parse-command dynamic-empty-env next-input)
         (dynamic-parse-from-port port)))))

; dynamic-parse-file

(define (dynamic-parse-file file-name)
  (let ((input-port (open-input-file file-name)))
    (dynamic-parse-from-port input-port)))
;----------------------------------------------------------------------------
; Implementation of Union/find data structure in Scheme
;----------------------------------------------------------------------------

;; for union/find the following attributes are necessary: rank, parent 
;; (see Tarjan, \"Data structures and network algorithms\", 1983)
;; In the Scheme realization an element is represented as a single
;; cons cell; its address is the element itself; the car field contains 
;; the parent, the cdr field is an address for a cons
;; cell containing the rank (car field) and the information (cdr field)


;; general union/find data structure
;; 
;; gen-element: Info -> Elem
;; find: Elem -> Elem
;; link: Elem! x Elem! -> Elem
;; asymm-link: Elem! x Elem! -> Elem
;; info: Elem -> Info
;; set-info!: Elem! x Info -> Void


(define (gen-element info)
  ; generates a new element: the parent field is initialized to '(),
  ; the rank field to 0
  (cons '() (cons 0 info)))

(define info (lambda (l) (cddr l)))
  ; returns the information stored in an element

(define (set-info! elem info)
  ; sets the info-field of elem to info
  (set-cdr! (cdr elem) info))

; (define (find! x)
;   ; finds the class representative of x and sets the parent field 
;   ; directly to the class representative (a class representative has
;   ; '() as its parent) (uses path halving)
;   ;(display \"Find!: \")
;   ;(display (pretty-print (info x)))
;   ;(newline)
;   (let ((px (car x)))
;     (if (null? px)
;       x
;       (let ((ppx (car px)))
;         (if (null? ppx)
;             px
;             (begin
;               (set-car! x ppx)
;               (find! ppx)))))))

(define (find! elem)
  ; finds the class representative of elem and sets the parent field 
  ; directly to the class representative (a class representative has
  ; '() as its parent)
  ;(display \"Find!: \")
  ;(display (pretty-print (info elem)))
  ;(newline)
  (let ((p-elem (car elem)))
    (if (null? p-elem)
        elem
        (let ((rep-elem (find! p-elem)))
          (set-car! elem rep-elem)
          rep-elem))))

(define (link! elem-1 elem-2)
  ; links class elements by rank
  ; they must be distinct class representatives
  ; returns the class representative of the merged equivalence classes
  ;(display \"Link!: \")
  ;(display (pretty-print (list (info elem-1) (info elem-2))))
  ;(newline)
  (let ((rank-1 (cadr elem-1))
        (rank-2 (cadr elem-2)))
    (cond
     ((= rank-1 rank-2)
      (set-car! (cdr elem-2) (+ rank-2 1))
      (set-car! elem-1 elem-2)
      elem-2)
     ((> rank-1 rank-2)
      (set-car! elem-2 elem-1)
      elem-1)
     (else
      (set-car! elem-1 elem-2)
      elem-2))))

(define asymm-link! (lambda (l x) (set-car! l x)))

;(define (asymm-link! elem-1 elem-2)
  ; links elem-1 onto elem-2 no matter what rank; 
  ; does not update the rank of elem-2 and does not return a value
  ; the two arguments must be distinct
  ;(display \"AsymmLink: \")
  ;(display (pretty-print (list (info elem-1) (info elem-2))))
  ;(newline)
  ;(set-car! elem-1 elem-2))

;----------------------------------------------------------------------------
; Type management
;----------------------------------------------------------------------------

; introduces type variables and types for Scheme,


;; type TVar (type variables)
;;
;; gen-tvar:          () -> TVar
;; gen-type:          TCon x TVar* -> TVar
;; dynamic:           TVar
;; tvar-id:           TVar -> Symbol
;; tvar-def:          TVar -> Type + Null
;; tvar-show:         TVar -> Symbol*
;;
;; set-def!:          !TVar x TCon x TVar* -> Null
;; equiv!:            !TVar x !TVar -> Null
;;
;;
;; type TCon (type constructors)
;;
;; ...
;;
;; type Type (types)
;;
;; gen-type:          TCon x TVar* -> Type
;; type-con:          Type -> TCon
;; type-args:         Type -> TVar*
;;
;; boolean:           TVar
;; character:         TVar
;; null:              TVar
;; pair:              TVar x TVar -> TVar
;; procedure:         TVar x TVar* -> TVar
;; charseq:           TVar
;; symbol:            TVar
;; array:             TVar -> TVar


; Needed packages: union/find

;(load \"union-fi.so\")

; TVar

(define counter 0)
; counter for generating tvar id's

(define (gen-id)
  ; generates a new id (for printing purposes)
  (set! counter (+ counter 1))
  counter)

(define (gen-tvar)
  ; generates a new type variable from a new symbol
  ; uses union/find elements with two info fields
  ; a type variable has exactly four fields:
  ; car:     TVar (the parent field; initially null)
  ; cadr:    Number (the rank field; is always nonnegative)
  ; caddr:   Symbol (the type variable identifier; used only for printing)
  ; cdddr:   Type (the leq field; initially null)
  (gen-element (cons (gen-id) '())))

(define (gen-type tcon targs)
  ; generates a new type variable with an associated type definition
  (gen-element (cons (gen-id) (cons tcon targs))))

(define dynamic (gen-element (cons 0 '())))
; the special type variable dynamic
; Generic operations

(define (tvar-id tvar)
  ; returns the (printable) symbol representing the type variable
  (car (info tvar)))

(define (tvar-def tvar)
  ; returns the type definition (if any) of the type variable
  (cdr (info tvar)))

(define (set-def! tvar tcon targs)
  ; sets the type definition part of tvar to type
  (set-cdr! (info tvar) (cons tcon targs))
  '())

(define (reset-def! tvar)
  ; resets the type definition part of tvar to nil
  (set-cdr! (info tvar) '()))

(define type-con (lambda (l) (car l)))
; returns the type constructor of a type definition

(define type-args (lambda (l) (cdr l)))
; returns the type variables of a type definition

(define (tvar->string tvar)
  ; converts a tvar's id to a string
  (if (eqv? (tvar-id tvar) 0)
      \"Dynamic\"
      (string-append \"t#\" (number->string (tvar-id tvar) 10))))

(define (tvar-show tv)
  ; returns a printable list representation of type variable tv
  (let* ((tv-rep (find! tv))
         (tv-def (tvar-def tv-rep)))
    (cons (tvar->string tv-rep)
          (if (null? tv-def)
              '()
              (cons 'is (type-show tv-def))))))

(define (type-show type)
  ; returns a printable list representation of type definition type
  (cond
   ((eqv? (type-con type) ptype-con)
    (let ((new-tvar (gen-tvar)))
      (cons ptype-con
            (cons (tvar-show new-tvar)
                  (tvar-show ((type-args type) new-tvar))))))
   (else
    (cons (type-con type)
          (map (lambda (tv)
                 (tvar->string (find! tv)))
               (type-args type))))))



; Special type operations

; type constructor literals

(define boolean-con 'boolean)
(define char-con 'char)
(define null-con 'null)
(define number-con 'number)
(define pair-con 'pair)
(define procedure-con 'procedure)
(define string-con 'string)
(define symbol-con 'symbol)
(define vector-con 'vector)

; type constants and type constructors

(define (null)
  ; ***Note***: Temporarily changed to be a pair!
  ; (gen-type null-con '())
  (pair (gen-tvar) (gen-tvar)))
(define (boolean)
  (gen-type boolean-con '()))
(define (character)
  (gen-type char-con '()))
(define (number)
  (gen-type number-con '()))
(define (charseq)
  (gen-type string-con '()))
(define (symbol)
  (gen-type symbol-con '()))
(define (pair tvar-1 tvar-2)
  (gen-type pair-con (list tvar-1 tvar-2)))
(define (array tvar)
  (gen-type vector-con (list tvar)))
(define (procedure arg-tvar res-tvar)
  (gen-type procedure-con (list arg-tvar res-tvar)))


; equivalencing of type variables

(define (equiv! tv1 tv2)
  (let* ((tv1-rep (find! tv1))
         (tv2-rep (find! tv2))
         (tv1-def (tvar-def tv1-rep))
         (tv2-def (tvar-def tv2-rep)))
    (cond
     ((eqv? tv1-rep tv2-rep)
      '())
     ((eqv? tv2-rep dynamic)
      (equiv-with-dynamic! tv1-rep))
     ((eqv? tv1-rep dynamic)
      (equiv-with-dynamic! tv2-rep))
     ((null? tv1-def)
      (if (null? tv2-def)
          ; both tv1 and tv2 are distinct type variables
          (link! tv1-rep tv2-rep)
          ; tv1 is a type variable, tv2 is a (nondynamic) type
          (asymm-link! tv1-rep tv2-rep)))
     ((null? tv2-def)
      ; tv1 is a (nondynamic) type, tv2 is a type variable
      (asymm-link! tv2-rep tv1-rep))
     ((eqv? (type-con tv1-def) (type-con tv2-def))
      ; both tv1 and tv2 are (nondynamic) types with equal numbers of
      ; arguments
      (link! tv1-rep tv2-rep)
      (map equiv! (type-args tv1-def) (type-args tv2-def)))
     (else
      ; tv1 and tv2 are types with distinct type constructors or different
      ; numbers of arguments
      (equiv-with-dynamic! tv1-rep)
      (equiv-with-dynamic! tv2-rep))))
  '())

(define (equiv-with-dynamic! tv)
  (let ((tv-rep (find! tv)))
    (if (not (eqv? tv-rep dynamic))
        (let ((tv-def (tvar-def tv-rep)))
          (asymm-link! tv-rep dynamic)
          (if (not (null? tv-def))
              (map equiv-with-dynamic! (type-args tv-def))))))
  '())
;----------------------------------------------------------------------------
; Polymorphic type management
;----------------------------------------------------------------------------

; introduces parametric polymorphic types


;; forall: (Tvar -> Tvar) -> TVar
;; fix: (Tvar -> Tvar) -> Tvar
;;  
;; instantiate-type: TVar -> TVar

; type constructor literal for polymorphic types

(define ptype-con 'forall)

(define (forall tv-func)
  (gen-type ptype-con tv-func))

(define (forall2 tv-func2)
  (forall (lambda (tv1)
            (forall (lambda (tv2)
                      (tv-func2 tv1 tv2))))))

(define (forall3 tv-func3)
  (forall (lambda (tv1)
            (forall2 (lambda (tv2 tv3)
                       (tv-func3 tv1 tv2 tv3))))))

(define (forall4 tv-func4)
  (forall (lambda (tv1)
            (forall3 (lambda (tv2 tv3 tv4)
                       (tv-func4 tv1 tv2 tv3 tv4))))))

(define (forall5 tv-func5)
  (forall (lambda (tv1)
            (forall4 (lambda (tv2 tv3 tv4 tv5)
                       (tv-func5 tv1 tv2 tv3 tv4 tv5))))))


; (polymorphic) instantiation

(define (instantiate-type tv)
  ; instantiates type tv and returns a generic instance
  (let* ((tv-rep (find! tv))
         (tv-def (tvar-def tv-rep)))
    (cond 
     ((null? tv-def)
      tv-rep)
     ((eqv? (type-con tv-def) ptype-con)
      (instantiate-type ((type-args tv-def) (gen-tvar))))
     (else
      tv-rep))))

(define (fix tv-func)
  ; forms a recursive type: the fixed point of type mapping tv-func
  (let* ((new-tvar (gen-tvar))
         (inst-tvar (tv-func new-tvar))
         (inst-def (tvar-def inst-tvar)))
    (if (null? inst-def)
        (fatal-error 'fix \"Illegal recursive type: ~s\"
               (list (tvar-show new-tvar) '= (tvar-show inst-tvar)))
        (begin
          (set-def! new-tvar 
                    (type-con inst-def)
                    (type-args inst-def))
          new-tvar))))

  
;----------------------------------------------------------------------------
;       Constraint management 
;----------------------------------------------------------------------------


; constraints

(define gen-constr (lambda (a b) (cons a b)))
; generates an equality between tvar1 and tvar2

(define constr-lhs (lambda (c) (car c)))
; returns the left-hand side of a constraint

(define constr-rhs (lambda (c) (cdr c)))
; returns the right-hand side of a constraint

(define (constr-show c)
  (cons (tvar-show (car c)) 
        (cons '= 
              (cons (tvar-show (cdr c)) '()))))


; constraint set management

(define global-constraints '())

(define (init-global-constraints!)
  (set! global-constraints '()))

(define (add-constr! lhs rhs)
  (set! global-constraints
        (cons (gen-constr lhs rhs) global-constraints))
  '())

(define (glob-constr-show) 
  ; returns printable version of global constraints
  (map constr-show global-constraints))


; constraint normalization

; Needed packages: type management

;(load \"typ-mgmt.so\")

(define (normalize-global-constraints!) 
  (normalize! global-constraints)
  (init-global-constraints!))

(define (normalize! constraints)
  (map (lambda (c)
         (equiv! (constr-lhs c) (constr-rhs c))) constraints))
; ----------------------------------------------------------------------------
; Abstract syntax definition and parse actions
; ----------------------------------------------------------------------------

; Needed packages: ast-gen.ss
;(load \"ast-gen.ss\")

;; Abstract syntax
;;
;; VarDef
;;
;; Identifier =         Symbol - SyntacticKeywords
;; SyntacticKeywords =  { ... } (see Section 7.1, IEEE Scheme Standard)
;;
;; Datum
;;
;; null-const:          Null            -> Datum
;; boolean-const:       Bool            -> Datum
;; char-const:          Char            -> Datum
;; number-const:        Number          -> Datum
;; string-const:        String          -> Datum
;; vector-const:        Datum*          -> Datum
;; pair-const:          Datum x Datum   -> Datum
;;
;; Expr
;;
;; Datum <              Expr
;;
;; var-def:             Identifier              -> VarDef
;; variable:            VarDef                  -> Expr
;; identifier:          Identifier              -> Expr
;; procedure-call:      Expr x Expr*            -> Expr
;; lambda-expression:   Formals x Body          -> Expr
;; conditional:         Expr x Expr x Expr      -> Expr
;; assignment:          Variable x Expr         -> Expr
;; cond-expression:     CondClause+             -> Expr
;; case-expression:     Expr x CaseClause*      -> Expr
;; and-expression:      Expr*                   -> Expr
;; or-expression:       Expr*                   -> Expr
;; let-expression:      (VarDef* x Expr*) x Body -> Expr
;; named-let-expression: VarDef x (VarDef* x Expr*) x Body -> Expr
;; let*-expression:     (VarDef* x Expr*) x Body -> Expr
;; letrec-expression:   (VarDef* x Expr*) x Body -> Expr
;; begin-expression:    Expr+                   -> Expr
;; do-expression:       IterDef* x CondClause x Expr* -> Expr
;; empty:                                       -> Expr
;;
;; VarDef* <            Formals
;;
;; simple-formal:       VarDef                  -> Formals
;; dotted-formals:      VarDef* x VarDef        -> Formals
;;
;; Body =               Definition* x Expr+     (reversed)
;; CondClause =         Expr x Expr+
;; CaseClause =         Datum* x Expr+
;; IterDef =            VarDef x Expr x Expr
;;
;; Definition
;;
;; definition:          Identifier x Expr       -> Definition
;; function-definition: Identifier x Formals x Body -> Definition
;; begin-command:       Definition*             -> Definition
;;
;; Expr <               Command
;; Definition <         Command
;;
;; Program =            Command*


;; Abstract syntax operators

; Datum

(define null-const 0)
(define boolean-const 1)
(define char-const 2)
(define number-const 3)
(define string-const 4)
(define symbol-const 5)
(define vector-const 6)
(define pair-const 7)

; Bindings

(define var-def 8)
(define null-def 29)
(define pair-def 30)

; Expr

(define variable 9)
(define identifier 10)
(define procedure-call 11)
(define lambda-expression 12)
(define conditional 13)
(define assignment 14)
(define cond-expression 15)
(define case-expression 16)
(define and-expression 17)
(define or-expression 18)
(define let-expression 19)
(define named-let-expression 20)
(define let*-expression 21)
(define letrec-expression 22)
(define begin-expression 23)
(define do-expression 24)
(define empty 25)
(define null-arg 31)
(define pair-arg 32)

; Command

(define definition 26)
(define function-definition 27)
(define begin-command 28)


;; Parse actions for abstract syntax construction

(define (dynamic-parse-action-null-const)
  ;; dynamic-parse-action for '()
  (ast-gen null-const '()))

(define (dynamic-parse-action-boolean-const e)
  ;; dynamic-parse-action for #f and #t
  (ast-gen boolean-const e))

(define (dynamic-parse-action-char-const e)
  ;; dynamic-parse-action for character constants
  (ast-gen char-const e))

(define (dynamic-parse-action-number-const e)
  ;; dynamic-parse-action for number constants
  (ast-gen number-const e))

(define (dynamic-parse-action-string-const e)
  ;; dynamic-parse-action for string literals
  (ast-gen string-const e))

(define (dynamic-parse-action-symbol-const e)
  ;; dynamic-parse-action for symbol constants
  (ast-gen symbol-const e))

(define (dynamic-parse-action-vector-const e)
  ;; dynamic-parse-action for vector literals
  (ast-gen vector-const e))

(define (dynamic-parse-action-pair-const e1 e2)
  ;; dynamic-parse-action for pairs
  (ast-gen pair-const (cons e1 e2)))

(define (dynamic-parse-action-var-def e)
  ;; dynamic-parse-action for defining occurrences of variables;
  ;; e is a symbol
  (ast-gen var-def e))

(define (dynamic-parse-action-null-formal)
  ;; dynamic-parse-action for null-list of formals
  (ast-gen null-def '()))

(define (dynamic-parse-action-pair-formal d1 d2)
  ;; dynamic-parse-action for non-null list of formals;
  ;; d1 is the result of parsing the first formal,
  ;; d2 the result of parsing the remaining formals
  (ast-gen pair-def (cons d1 d2)))

(define (dynamic-parse-action-variable e)
  ;; dynamic-parse-action for applied occurrences of variables
  ;; ***Note***: e is the result of a dynamic-parse-action on the
  ;; corresponding variable definition!
  (ast-gen variable e))

(define (dynamic-parse-action-identifier e)
  ;; dynamic-parse-action for undeclared identifiers (free variable
  ;; occurrences)
  ;; ***Note***: e is a symbol (legal identifier)
  (ast-gen identifier e))
 
(define (dynamic-parse-action-null-arg)
  ;; dynamic-parse-action for a null list of arguments in a procedure call
  (ast-gen null-arg '()))

(define (dynamic-parse-action-pair-arg a1 a2)
  ;; dynamic-parse-action for a non-null list of arguments in a procedure call
  ;; a1 is the result of parsing the first argument, 
  ;; a2 the result of parsing the remaining arguments
  (ast-gen pair-arg (cons a1 a2)))

(define (dynamic-parse-action-procedure-call op args)
  ;; dynamic-parse-action for procedure calls: op function, args list of arguments
  (ast-gen procedure-call (cons op args)))

(define (dynamic-parse-action-lambda-expression formals body)
  ;; dynamic-parse-action for lambda-abstractions
  (ast-gen lambda-expression (cons formals body)))

(define (dynamic-parse-action-conditional test then-branch else-branch)
  ;; dynamic-parse-action for conditionals (if-then-else expressions)
  (ast-gen conditional (cons test (cons then-branch else-branch))))

(define (dynamic-parse-action-empty)
  ;; dynamic-parse-action for missing or empty field
  (ast-gen empty '()))

(define (dynamic-parse-action-assignment lhs rhs)
  ;; dynamic-parse-action for assignment
  (ast-gen assignment (cons lhs rhs)))

(define (dynamic-parse-action-begin-expression body)
  ;; dynamic-parse-action for begin-expression
  (ast-gen begin-expression body))

(define (dynamic-parse-action-cond-expression clauses)
  ;; dynamic-parse-action for cond-expressions
  (ast-gen cond-expression clauses))

(define (dynamic-parse-action-and-expression args)
  ;; dynamic-parse-action for and-expressions
  (ast-gen and-expression args))

(define (dynamic-parse-action-or-expression args)
  ;; dynamic-parse-action for or-expressions
  (ast-gen or-expression args))

(define (dynamic-parse-action-case-expression key clauses)
  ;; dynamic-parse-action for case-expressions
  (ast-gen case-expression (cons key clauses)))

(define (dynamic-parse-action-let-expression bindings body)
  ;; dynamic-parse-action for let-expressions
  (ast-gen let-expression (cons bindings body)))

(define (dynamic-parse-action-named-let-expression variable bindings body)
  ;; dynamic-parse-action for named-let expressions
  (ast-gen named-let-expression (cons variable (cons bindings body))))

(define (dynamic-parse-action-let*-expression bindings body)
  ;; dynamic-parse-action for let-expressions
  (ast-gen let*-expression (cons bindings body)))

(define (dynamic-parse-action-letrec-expression bindings body)
  ;; dynamic-parse-action for let-expressions
  (ast-gen letrec-expression (cons bindings body)))

(define (dynamic-parse-action-definition variable expr)
  ;; dynamic-parse-action for simple definitions
  (ast-gen definition (cons variable expr)))

(define (dynamic-parse-action-function-definition variable formals body)
  ;; dynamic-parse-action for function definitions
  (ast-gen function-definition (cons variable (cons formals body))))


(define dynamic-parse-action-commands (lambda (a b) (cons a b)))
;; dynamic-parse-action for processing a command result followed by a the
;; result of processing the remaining commands


;; Pretty-printing abstract syntax trees

(define (ast-show ast)
  ;; converts abstract syntax tree to list representation (Scheme program)
  ;; ***Note***: check translation of constructors to numbers at the top of the file
  (let ((syntax-op (ast-con ast))
        (syntax-arg (ast-arg ast)))
    (case syntax-op
      ((0 1 2 3 4 8 10) syntax-arg)
      ((29 31) '())
      ((30 32) (cons (ast-show (car syntax-arg)) (ast-show (cdr syntax-arg))))
      ((5) (list 'quote syntax-arg))
      ((6) (list->vector (map ast-show syntax-arg)))
      ((7) (list 'cons (ast-show (car syntax-arg)) (ast-show (cdr syntax-arg))))
      ((9) (ast-arg syntax-arg))
      ((11) (cons (ast-show (car syntax-arg)) (ast-show (cdr syntax-arg))))
      ((12) (cons 'lambda (cons (ast-show (car syntax-arg)) 
                                (map ast-show (cdr syntax-arg)))))
      ((13) (cons 'if (cons (ast-show (car syntax-arg))
                            (cons (ast-show (cadr syntax-arg))
                                  (let ((alt (cddr syntax-arg)))
                                    (if (eqv? (ast-con alt) empty)
                                        '()
                                        (list (ast-show alt))))))))
      ((14) (list 'set! (ast-show (car syntax-arg)) (ast-show (cdr syntax-arg))))
      ((15) (cons 'cond
                  (map (lambda (cc)
                         (let ((guard (car cc))
                               (body (cdr cc)))
                           (cons
                            (if (eqv? (ast-con guard) empty)
                                'else
                                (ast-show guard))
                            (map ast-show body))))
                       syntax-arg)))
      ((16) (cons 'case
                  (cons (ast-show (car syntax-arg))
                        (map (lambda (cc)
                               (let ((data (car cc)))
                                 (if (and (pair? data)
                                          (eqv? (ast-con (car data)) empty))
                                     (cons 'else
                                           (map ast-show (cdr cc)))
                                     (cons (map datum-show data)
                                           (map ast-show (cdr cc))))))
                             (cdr syntax-arg)))))
      ((17) (cons 'and (map ast-show syntax-arg)))
      ((18) (cons 'or (map ast-show syntax-arg)))
      ((19) (cons 'let
                  (cons (map
                         (lambda (vd e)
                           (list (ast-show vd) (ast-show e)))
                         (caar syntax-arg)
                         (cdar syntax-arg))
                        (map ast-show (cdr syntax-arg)))))
      ((20) (cons 'let
                  (cons (ast-show (car syntax-arg))
                        (cons (map
                               (lambda (vd e)
                                 (list (ast-show vd) (ast-show e)))
                               (caadr syntax-arg)
                               (cdadr syntax-arg))
                              (map ast-show (cddr syntax-arg))))))
      ((21) (cons 'let*
                  (cons (map
                         (lambda (vd e)
                           (list (ast-show vd) (ast-show e)))
                         (caar syntax-arg)
                         (cdar syntax-arg))
                        (map ast-show (cdr syntax-arg)))))
      ((22) (cons 'letrec
                  (cons (map
                         (lambda (vd e)
                           (list (ast-show vd) (ast-show e)))
                         (caar syntax-arg)
                         (cdar syntax-arg))
                        (map ast-show (cdr syntax-arg)))))
      ((23) (cons 'begin
                  (map ast-show syntax-arg)))
      ((24) (fatal-error 'ast-show \"Do expressions not handled! (~s)\" syntax-arg))
      ((25) (fatal-error 'ast-show \"This can't happen: empty encountered!\"))
      ((26) (list 'define
                  (ast-show (car syntax-arg))
                  (ast-show (cdr syntax-arg))))
      ((27) (cons 'define
                  (cons
                   (cons (ast-show (car syntax-arg))
                         (ast-show (cadr syntax-arg)))
                   (map ast-show (cddr syntax-arg)))))
      ((28) (cons 'begin
                  (map ast-show syntax-arg)))
      (else (fatal-error 'ast-show \"Unknown abstract syntax operator: ~s\"
                   syntax-op)))))


;; ast*-show

(define (ast*-show p)
  ;; shows a list of abstract syntax trees
  (map ast-show p))


;; datum-show

(define (datum-show ast)
  ;; prints an abstract syntax tree as a datum
  (case (ast-con ast)
    ((0 1 2 3 4 5) (ast-arg ast))
    ((6) (list->vector (map datum-show (ast-arg ast))))
    ((7) (cons (datum-show (car (ast-arg ast))) (datum-show (cdr (ast-arg ast)))))
    (else (fatal-error 'datum-show \"This should not happen!\"))))

; write-to-port

(define (write-to-port prog port)
  ; writes a program to a port
  (for-each
   (lambda (command)
     (write command port)
     (newline port))
   prog)
  '())

; write-file 

(define (write-to-file prog filename)
  ; write a program to a file
  (let ((port (open-output-file filename)))
    (write-to-port prog port)
    (close-output-port port)
    '()))

; ----------------------------------------------------------------------------
; Typed abstract syntax tree management: constraint generation, display, etc.
; ----------------------------------------------------------------------------


;; Abstract syntax operations, incl. constraint generation

(define (ast-gen syntax-op arg)
  ; generates all attributes and performs semantic side effects
  (let ((ntvar
         (case syntax-op
           ((0 29 31) (null))
           ((1) (boolean))
           ((2) (character))
           ((3) (number))
           ((4) (charseq))
           ((5) (symbol))
           ((6) (let ((aux-tvar (gen-tvar)))
                  (for-each (lambda (t)
                              (add-constr! t aux-tvar))
                            (map ast-tvar arg))
                  (array aux-tvar)))
           ((7 30 32) (let ((t1 (ast-tvar (car arg)))
                            (t2 (ast-tvar (cdr arg))))
                        (pair t1 t2)))
           ((8) (gen-tvar))
           ((9) (ast-tvar arg))
           ((10) (let ((in-env (dynamic-lookup arg dynamic-top-level-env)))
                   (if in-env
                       (instantiate-type (binding-value in-env))
                       (let ((new-tvar (gen-tvar)))
                         (set! dynamic-top-level-env (extend-env-with-binding
                                              dynamic-top-level-env
                                              (gen-binding arg new-tvar)))
                         new-tvar))))
           ((11) (let ((new-tvar (gen-tvar)))
                   (add-constr! (procedure (ast-tvar (cdr arg)) new-tvar)
                                (ast-tvar (car arg)))
                   new-tvar))
           ((12) (procedure (ast-tvar (car arg))
                            (ast-tvar (tail (cdr arg)))))
           ((13) (let ((t-test (ast-tvar (car arg)))
                       (t-consequent (ast-tvar (cadr arg)))
                       (t-alternate (ast-tvar (cddr arg))))
                   (add-constr! (boolean) t-test)
                   (add-constr! t-consequent t-alternate)
                   t-consequent))
           ((14) (let ((var-tvar (ast-tvar (car arg)))
                       (exp-tvar (ast-tvar (cdr arg))))
                   (add-constr! var-tvar exp-tvar)
                   var-tvar))
           ((15) (let ((new-tvar (gen-tvar)))
                   (for-each (lambda (body)
                               (add-constr! (ast-tvar (tail body)) new-tvar))
                             (map cdr arg))
                   (for-each (lambda (e)
                               (add-constr! (boolean) (ast-tvar e)))
                             (map car arg))
                   new-tvar))
           ((16) (let* ((new-tvar (gen-tvar))
                        (t-key (ast-tvar (car arg)))
                        (case-clauses (cdr arg)))
                   (for-each (lambda (exprs)
                               (for-each (lambda (e)
                                           (add-constr! (ast-tvar e) t-key))
                                         exprs))
                             (map car case-clauses))
                   (for-each (lambda (body)
                               (add-constr! (ast-tvar (tail body)) new-tvar))
                             (map cdr case-clauses))
                   new-tvar))
           ((17 18) (for-each (lambda (e)
                                (add-constr! (boolean) (ast-tvar e)))
                              arg)
                    (boolean))
           ((19 21 22) (let ((var-def-tvars (map ast-tvar (caar arg)))
                             (def-expr-types (map ast-tvar (cdar arg)))
                             (body-type (ast-tvar (tail (cdr arg)))))
                         (for-each add-constr! var-def-tvars def-expr-types)
                         body-type))
           ((20) (let ((var-def-tvars (map ast-tvar (caadr arg)))
                       (def-expr-types (map ast-tvar (cdadr arg)))
                       (body-type (ast-tvar (tail (cddr arg))))
                       (named-var-type (ast-tvar (car arg))))
                   (for-each add-constr! var-def-tvars def-expr-types)
                   (add-constr! (procedure (convert-tvars var-def-tvars) body-type)
                                named-var-type)
                   body-type))
           ((23) (ast-tvar (tail arg)))
           ((24) (fatal-error 'ast-gen
                        \"Do-expressions not handled! (Argument: ~s) arg\"))
           ((25) (gen-tvar))
           ((26) (let ((t-var (ast-tvar (car arg)))
                       (t-exp (ast-tvar (cdr arg))))
                   (add-constr! t-var t-exp)
                   t-var))
           ((27) (let ((t-var (ast-tvar (car arg)))
                       (t-formals (ast-tvar (cadr arg)))
                       (t-body (ast-tvar (tail (cddr arg)))))
                   (add-constr! (procedure t-formals t-body) t-var)
                   t-var))
           ((28) (gen-tvar))
           (else (fatal-error 'ast-gen \"Can't handle syntax operator: ~s\" syntax-op)))))
    (cons syntax-op (cons ntvar arg))))

(define ast-con car)
;; extracts the ast-constructor from an abstract syntax tree

(define ast-arg cddr)
;; extracts the ast-argument from an abstract syntax tree

(define ast-tvar cadr)
;; extracts the tvar from an abstract syntax tree


;; tail

(define (tail l)
  ;; returns the tail of a nonempty list
  (if (null? (cdr l))
      (car l)
      (tail (cdr l))))

; convert-tvars

(define (convert-tvars tvar-list)
  ;; converts a list of tvars to a single tvar
  (cond
   ((null? tvar-list) (null))
   ((pair? tvar-list) (pair (car tvar-list)
                            (convert-tvars (cdr tvar-list))))
   (else (fatal-error 'convert-tvars \"Not a list of tvars: ~s\" tvar-list))))


;; Pretty-printing abstract syntax trees

(define (tast-show ast)
  ;; converts abstract syntax tree to list representation (Scheme program)
  (let ((syntax-op (ast-con ast))
        (syntax-tvar (tvar-show (ast-tvar ast)))
        (syntax-arg (ast-arg ast)))
    (cons
     (case syntax-op
       ((0 1 2 3 4 8 10) syntax-arg)
       ((29 31) '())
       ((30 32) (cons (tast-show (car syntax-arg))
                      (tast-show (cdr syntax-arg))))
       ((5) (list 'quote syntax-arg))
       ((6) (list->vector (map tast-show syntax-arg)))
       ((7) (list 'cons (tast-show (car syntax-arg))
                  (tast-show (cdr syntax-arg))))
       ((9) (ast-arg syntax-arg))
       ((11) (cons (tast-show (car syntax-arg)) (tast-show (cdr syntax-arg))))
       ((12) (cons 'lambda (cons (tast-show (car syntax-arg))
                                 (map tast-show (cdr syntax-arg)))))
       ((13) (cons 'if (cons (tast-show (car syntax-arg))
                             (cons (tast-show (cadr syntax-arg))
                                   (let ((alt (cddr syntax-arg)))
                                     (if (eqv? (ast-con alt) empty)
                                         '()
                                         (list (tast-show alt))))))))
       ((14) (list 'set! (tast-show (car syntax-arg))
                   (tast-show (cdr syntax-arg))))
       ((15) (cons 'cond
                   (map (lambda (cc)
                          (let ((guard (car cc))
                                (body (cdr cc)))
                            (cons
                             (if (eqv? (ast-con guard) empty)
                                 'else
                                 (tast-show guard))
                             (map tast-show body))))
                        syntax-arg)))
       ((16) (cons 'case
                   (cons (tast-show (car syntax-arg))
                         (map (lambda (cc)
                                (let ((data (car cc)))
                                  (if (and (pair? data)
                                           (eqv? (ast-con (car data)) empty))
                                      (cons 'else
                                            (map tast-show (cdr cc)))
                                      (cons (map datum-show data)
                                            (map tast-show (cdr cc))))))
                              (cdr syntax-arg)))))
       ((17) (cons 'and (map tast-show syntax-arg)))
       ((18) (cons 'or (map tast-show syntax-arg)))
       ((19) (cons 'let
                   (cons (map
                          (lambda (vd e)
                            (list (tast-show vd) (tast-show e)))
                          (caar syntax-arg)
                          (cdar syntax-arg))
                         (map tast-show (cdr syntax-arg)))))
       ((20) (cons 'let
                   (cons (tast-show (car syntax-arg))
                         (cons (map
                                (lambda (vd e)
                                  (list (tast-show vd) (tast-show e)))
                                (caadr syntax-arg)
                                (cdadr syntax-arg))
                               (map tast-show (cddr syntax-arg))))))
       ((21) (cons 'let*
                   (cons (map
                          (lambda (vd e)
                            (list (tast-show vd) (tast-show e)))
                          (caar syntax-arg)
                          (cdar syntax-arg))
                         (map tast-show (cdr syntax-arg)))))
       ((22) (cons 'letrec
                   (cons (map
                          (lambda (vd e)
                            (list (tast-show vd) (tast-show e)))
                          (caar syntax-arg)
                          (cdar syntax-arg))
                         (map tast-show (cdr syntax-arg)))))
       ((23) (cons 'begin
                   (map tast-show syntax-arg)))
       ((24) (fatal-error 'tast-show \"Do expressions not handled! (~s)\" syntax-arg))
       ((25) (fatal-error 'tast-show \"This can't happen: empty encountered!\"))
       ((26) (list 'define
                   (tast-show (car syntax-arg))
                   (tast-show (cdr syntax-arg))))
       ((27) (cons 'define
                   (cons
                    (cons (tast-show (car syntax-arg))
                          (tast-show (cadr syntax-arg)))
                    (map tast-show (cddr syntax-arg)))))
       ((28) (cons 'begin
                   (map tast-show syntax-arg)))
       (else (fatal-error 'tast-show \"Unknown abstract syntax operator: ~s\"
                    syntax-op)))
     syntax-tvar)))

;; tast*-show

(define (tast*-show p)
  ;; shows a list of abstract syntax trees
  (map tast-show p))


;; counters for tagging/untagging

(define untag-counter 0)
(define no-untag-counter 0)
(define tag-counter 0)
(define no-tag-counter 0)
(define may-untag-counter 0)
(define no-may-untag-counter 0)

(define (reset-counters!)
  (set! untag-counter 0)
  (set! no-untag-counter 0)
  (set! tag-counter 0)
  (set! no-tag-counter 0)
  (set! may-untag-counter 0)
  (set! no-may-untag-counter 0))

(define (counters-show)
  (list
   (cons tag-counter no-tag-counter)
   (cons untag-counter no-untag-counter)
   (cons may-untag-counter no-may-untag-counter)))  


;; tag-show

(define (tag-show tvar-rep prog)
  ; display prog with tagging operation
  (if (eqv? tvar-rep dynamic)
      (begin
        (set! tag-counter (+ tag-counter 1))
        (list 'tag prog))
      (begin
        (set! no-tag-counter (+ no-tag-counter 1))
        (list 'no-tag prog))))


;; untag-show

(define (untag-show tvar-rep prog)
  ; display prog with untagging operation
  (if (eqv? tvar-rep dynamic)
      (begin
        (set! untag-counter (+ untag-counter 1))
        (list 'untag prog))
      (begin
        (set! no-untag-counter (+ no-untag-counter 1))
        (list 'no-untag prog))))

(define (may-untag-show tvar-rep prog)
  ; display possible untagging in actual arguments
  (if (eqv? tvar-rep dynamic)
      (begin
        (set! may-untag-counter (+ may-untag-counter 1))
        (list 'may-untag prog))
      (begin
        (set! no-may-untag-counter (+ no-may-untag-counter 1))
        (list 'no-may-untag prog))))


;; tag-ast-show

(define (tag-ast-show ast)
  ;; converts typed and normalized abstract syntax tree to
  ;; a Scheme program with explicit tagging and untagging operations
  (let ((syntax-op (ast-con ast))
        (syntax-tvar (find! (ast-tvar ast)))
        (syntax-arg (ast-arg ast)))
    (case syntax-op
      ((0 1 2 3 4)
       (tag-show syntax-tvar syntax-arg))
      ((8 10) syntax-arg)
      ((29 31) '())
      ((30) (cons (tag-ast-show (car syntax-arg))
                  (tag-ast-show (cdr syntax-arg))))
      ((32) (cons (may-untag-show (find! (ast-tvar (car syntax-arg)))
                              (tag-ast-show (car syntax-arg)))
                  (tag-ast-show (cdr syntax-arg))))
      ((5) (tag-show syntax-tvar (list 'quote syntax-arg)))
      ((6) (tag-show syntax-tvar (list->vector (map tag-ast-show syntax-arg))))
      ((7) (tag-show syntax-tvar (list 'cons (tag-ast-show (car syntax-arg))
                                       (tag-ast-show (cdr syntax-arg)))))
      ((9) (ast-arg syntax-arg))
      ((11) (let ((proc-tvar (find! (ast-tvar (car syntax-arg)))))
              (cons (untag-show proc-tvar 
                                (tag-ast-show (car syntax-arg)))
                    (tag-ast-show (cdr syntax-arg)))))
      ((12) (tag-show syntax-tvar
                      (cons 'lambda (cons (tag-ast-show (car syntax-arg))
                                          (map tag-ast-show (cdr syntax-arg))))))
      ((13) (let ((test-tvar (find! (ast-tvar (car syntax-arg)))))
              (cons 'if (cons (untag-show test-tvar
                                          (tag-ast-show (car syntax-arg)))
                              (cons (tag-ast-show (cadr syntax-arg))
                                    (let ((alt (cddr syntax-arg)))
                                      (if (eqv? (ast-con alt) empty)
                                          '()
                                          (list (tag-ast-show alt)))))))))
      ((14) (list 'set! (tag-ast-show (car syntax-arg))
                  (tag-ast-show (cdr syntax-arg))))
      ((15) (cons 'cond
                  (map (lambda (cc)
                         (let ((guard (car cc))
                               (body (cdr cc)))
                           (cons
                            (if (eqv? (ast-con guard) empty)
                                'else
                                (untag-show (find! (ast-tvar guard))
                                            (tag-ast-show guard)))
                            (map tag-ast-show body))))
                       syntax-arg)))
      ((16) (cons 'case
                  (cons (tag-ast-show (car syntax-arg))
                        (map (lambda (cc)
                               (let ((data (car cc)))
                                 (if (and (pair? data)
                                          (eqv? (ast-con (car data)) empty))
                                     (cons 'else
                                           (map tag-ast-show (cdr cc)))
                                     (cons (map datum-show data)
                                           (map tag-ast-show (cdr cc))))))
                             (cdr syntax-arg)))))
      ((17) (cons 'and (map
                        (lambda (ast)
                          (let ((bool-tvar (find! (ast-tvar ast))))
                            (untag-show bool-tvar (tag-ast-show ast))))
                        syntax-arg)))
      ((18) (cons 'or (map
                       (lambda (ast)
                         (let ((bool-tvar (find! (ast-tvar ast))))
                           (untag-show bool-tvar (tag-ast-show ast))))
                       syntax-arg)))
      ((19) (cons 'let
                  (cons (map
                         (lambda (vd e)
                           (list (tag-ast-show vd) (tag-ast-show e)))
                         (caar syntax-arg)
                         (cdar syntax-arg))
                        (map tag-ast-show (cdr syntax-arg)))))
      ((20) (cons 'let
                  (cons (tag-ast-show (car syntax-arg))
                        (cons (map
                               (lambda (vd e)
                                 (list (tag-ast-show vd) (tag-ast-show e)))
                               (caadr syntax-arg)
                               (cdadr syntax-arg))
                              (map tag-ast-show (cddr syntax-arg))))))
      ((21) (cons 'let*
                  (cons (map
                         (lambda (vd e)
                           (list (tag-ast-show vd) (tag-ast-show e)))
                         (caar syntax-arg)
                         (cdar syntax-arg))
                        (map tag-ast-show (cdr syntax-arg)))))
      ((22) (cons 'letrec
                  (cons (map
                         (lambda (vd e)
                           (list (tag-ast-show vd) (tag-ast-show e)))
                         (caar syntax-arg)
                         (cdar syntax-arg))
                        (map tag-ast-show (cdr syntax-arg)))))
      ((23) (cons 'begin
                  (map tag-ast-show syntax-arg)))
      ((24) (fatal-error 'tag-ast-show \"Do expressions not handled! (~s)\" syntax-arg))
      ((25) (fatal-error 'tag-ast-show \"This can't happen: empty encountered!\"))
      ((26) (list 'define
                  (tag-ast-show (car syntax-arg))
                  (tag-ast-show (cdr syntax-arg))))
      ((27) (let ((func-tvar (find! (ast-tvar (car syntax-arg)))))
              (list 'define
                    (tag-ast-show (car syntax-arg))
                    (tag-show func-tvar
                              (cons 'lambda
                                    (cons (tag-ast-show (cadr syntax-arg))
                                          (map tag-ast-show (cddr syntax-arg))))))))
      ((28) (cons 'begin
                  (map tag-ast-show syntax-arg)))
      (else (fatal-error 'tag-ast-show \"Unknown abstract syntax operator: ~s\"
                   syntax-op)))))


; tag-ast*-show

(define (tag-ast*-show p)
  ; display list of commands/expressions with tagging/untagging
  ; operations
  (map tag-ast-show p))
; ----------------------------------------------------------------------------
; Top level type environment
; ----------------------------------------------------------------------------


; Needed packages: type management (monomorphic and polymorphic)

;(load \"typ-mgmt.ss\")
;(load \"ptyp-mgm.ss\")


; type environment for miscellaneous

(define misc-env
  (list
   (cons 'quote (forall (lambda (tv) tv)))
   (cons 'eqv? (forall (lambda (tv) (procedure (convert-tvars (list tv tv))
                                               (boolean)))))
   (cons 'eq? (forall (lambda (tv) (procedure (convert-tvars (list tv tv))
                                              (boolean)))))
   (cons 'equal? (forall (lambda (tv) (procedure (convert-tvars (list tv tv))
                                                 (boolean)))))
   ))

; type environment for input/output

(define io-env
  (list
   (cons 'open-input-file (procedure (convert-tvars (list (charseq))) dynamic))
   (cons 'eof-object? (procedure (convert-tvars (list dynamic)) (boolean)))
   (cons 'read (forall (lambda (tv)
                         (procedure (convert-tvars (list tv)) dynamic))))
   (cons 'write (forall (lambda (tv)
                          (procedure (convert-tvars (list tv)) dynamic))))
   (cons 'display (forall (lambda (tv)
                            (procedure (convert-tvars (list tv)) dynamic))))
   (cons 'newline (procedure (null) dynamic))
   (cons 'pretty-print (forall (lambda (tv)
                                 (procedure (convert-tvars (list tv)) dynamic))))))


; type environment for Booleans

(define boolean-env
  (list
   (cons 'boolean? (forall (lambda (tv)
                             (procedure (convert-tvars (list tv)) (boolean)))))
   ;(cons #f (boolean))
   ; #f doesn't exist in Chez Scheme, but gets mapped to null!
   (cons #t (boolean))
   (cons 'not (procedure (convert-tvars (list (boolean))) (boolean)))
   ))


; type environment for pairs and lists

(define (list-type tv)
  (fix (lambda (tv2) (pair tv tv2))))

(define list-env
  (list
   (cons 'pair? (forall2 (lambda (tv1 tv2)
                           (procedure (convert-tvars (list (pair tv1 tv2)))
                                      (boolean)))))
   (cons 'null? (forall2 (lambda (tv1 tv2)
                           (procedure (convert-tvars (list (pair tv1 tv2)))
                                      (boolean)))))
   (cons 'list? (forall2 (lambda (tv1 tv2)
                           (procedure (convert-tvars (list (pair tv1 tv2)))
                                      (boolean)))))
   (cons 'cons (forall2 (lambda (tv1 tv2)
                          (procedure (convert-tvars (list tv1 tv2))
                                     (pair tv1 tv2)))))
   (cons 'car (forall2 (lambda (tv1 tv2)
                         (procedure (convert-tvars (list (pair tv1 tv2)))
                                    tv1))))
   (cons 'cdr (forall2 (lambda (tv1 tv2)
                         (procedure (convert-tvars (list (pair tv1 tv2)))
                                    tv2))))
   (cons 'set-car! (forall2 (lambda (tv1 tv2)
                              (procedure (convert-tvars (list (pair tv1 tv2)
                                                              tv1))
                                         dynamic))))
   (cons 'set-cdr! (forall2 (lambda (tv1 tv2)
                              (procedure (convert-tvars (list (pair tv1 tv2)
                                                              tv2))
                                         dynamic))))
   (cons 'caar (forall3 (lambda (tv1 tv2 tv3)
                          (procedure (convert-tvars
                                      (list (pair (pair tv1 tv2) tv3)))
                                     tv1))))
   (cons 'cdar (forall3 (lambda (tv1 tv2 tv3)
                          (procedure (convert-tvars
                                      (list (pair (pair tv1 tv2) tv3)))
                                     tv2))))

   (cons 'cadr (forall3 (lambda (tv1 tv2 tv3)
                          (procedure (convert-tvars
                                      (list (pair tv1 (pair tv2 tv3))))
                                     tv2))))
   (cons 'cddr (forall3 (lambda (tv1 tv2 tv3)
                          (procedure (convert-tvars
                                      (list (pair tv1 (pair tv2 tv3))))
                                     tv3))))
   (cons 'caaar (forall4
                 (lambda (tv1 tv2 tv3 tv4)
                   (procedure (convert-tvars
                               (list (pair (pair (pair tv1 tv2) tv3) tv4)))
                              tv1))))
   (cons 'cdaar (forall4
                 (lambda (tv1 tv2 tv3 tv4)
                   (procedure (convert-tvars
                               (list (pair (pair (pair tv1 tv2) tv3) tv4)))
                              tv2))))
   (cons 'cadar (forall4
                 (lambda (tv1 tv2 tv3 tv4)
                   (procedure (convert-tvars
                               (list (pair (pair tv1 (pair tv2 tv3)) tv4)))
                              tv2))))
   (cons 'cddar (forall4
                 (lambda (tv1 tv2 tv3 tv4)
                   (procedure (convert-tvars
                               (list (pair (pair tv1 (pair tv2 tv3)) tv4)))
                              tv3))))
   (cons 'caadr (forall4
                 (lambda (tv1 tv2 tv3 tv4)
                   (procedure (convert-tvars
                               (list (pair tv1 (pair (pair tv2 tv3) tv4))))
                              tv2))))
   (cons 'cdadr (forall4
                 (lambda (tv1 tv2 tv3 tv4)
                   (procedure (convert-tvars
                               (list (pair tv1 (pair (pair tv2 tv3) tv4))))
                              tv3))))
   (cons 'caddr (forall4
                 (lambda (tv1 tv2 tv3 tv4)
                   (procedure (convert-tvars
                               (list (pair tv1 (pair tv2 (pair tv3 tv4)))))
                              tv3))))
   (cons 'cdddr (forall4
                 (lambda (tv1 tv2 tv3 tv4)
                   (procedure (convert-tvars
                               (list (pair tv1 (pair tv2 (pair tv3 tv4)))))
                              tv4))))
   (cons 'cadddr
         (forall5 (lambda (tv1 tv2 tv3 tv4 tv5)
                    (procedure (convert-tvars
                                (list (pair tv1
                                            (pair tv2
                                                  (pair tv3
                                                        (pair tv4 tv5))))))
                               tv4))))
   (cons 'cddddr
         (forall5 (lambda (tv1 tv2 tv3 tv4 tv5)
                    (procedure (convert-tvars
                                (list (pair tv1
                                            (pair tv2
                                                  (pair tv3
                                                        (pair tv4 tv5))))))
                               tv5))))
   (cons 'list (forall (lambda (tv)
                         (procedure tv tv))))
   (cons 'length (forall (lambda (tv)
                           (procedure (convert-tvars (list (list-type tv)))
                                      (number)))))
   (cons 'append (forall (lambda (tv)
                           (procedure (convert-tvars (list (list-type tv)
                                                           (list-type tv)))
                                      (list-type tv)))))
   (cons 'reverse (forall (lambda (tv)
                            (procedure (convert-tvars (list (list-type tv)))
                                       (list-type tv)))))
   (cons 'list-ref (forall (lambda (tv)
                             (procedure (convert-tvars (list (list-type tv)
                                                             (number)))
                                        tv))))
   (cons 'memq (forall (lambda (tv)
                         (procedure (convert-tvars (list tv
                                                         (list-type tv)))
                                    (boolean)))))
   (cons 'memv (forall (lambda (tv)
                         (procedure (convert-tvars (list tv
                                                         (list-type tv)))
                                    (boolean)))))
   (cons 'member (forall (lambda (tv)
                           (procedure (convert-tvars (list tv
                                                           (list-type tv)))
                                      (boolean)))))
   (cons 'assq (forall2 (lambda (tv1 tv2)
                          (procedure (convert-tvars
                                      (list tv1
                                            (list-type (pair tv1 tv2))))
                                     (pair tv1 tv2)))))
   (cons 'assv (forall2 (lambda (tv1 tv2)
                          (procedure (convert-tvars
                                      (list tv1
                                            (list-type (pair tv1 tv2))))
                                     (pair tv1 tv2)))))
   (cons 'assoc (forall2 (lambda (tv1 tv2)
                           (procedure (convert-tvars
                                       (list tv1
                                             (list-type (pair tv1 tv2))))
                                      (pair tv1 tv2)))))
   ))


(define symbol-env
  (list
   (cons 'symbol? (forall (lambda (tv)
                            (procedure (convert-tvars (list tv)) (boolean)))))
   (cons 'symbol->string (procedure (convert-tvars (list (symbol))) (charseq)))
   (cons 'string->symbol (procedure (convert-tvars (list (charseq))) (symbol)))
   ))

(define number-env
  (list
   (cons 'number? (forall (lambda (tv)
                            (procedure (convert-tvars (list tv)) (boolean)))))
   (cons '+ (procedure (convert-tvars (list (number) (number))) (number)))
   (cons '- (procedure (convert-tvars (list (number) (number))) (number)))
   (cons '* (procedure (convert-tvars (list (number) (number))) (number)))
   (cons '/ (procedure (convert-tvars (list (number) (number))) (number)))
   (cons 'number->string (procedure (convert-tvars (list (number))) (charseq)))
   (cons 'string->number (procedure (convert-tvars (list (charseq))) (number)))
   ))

(define char-env
  (list
   (cons 'char? (forall (lambda (tv)
                          (procedure (convert-tvars (list tv)) (boolean)))))
   (cons 'char->integer (procedure (convert-tvars (list (character)))
                                   (number)))
   (cons 'integer->char (procedure (convert-tvars (list (number)))
                                   (character)))
   ))

(define string-env
  (list
   (cons 'string? (forall (lambda (tv)
                            (procedure (convert-tvars (list tv)) (boolean)))))
   ))

(define vector-env
  (list
   (cons 'vector? (forall (lambda (tv)
                            (procedure (convert-tvars (list tv)) (boolean)))))
   (cons 'make-vector (forall (lambda (tv)
                                (procedure (convert-tvars (list (number)))
                                           (array tv)))))
   (cons 'vector-length (forall (lambda (tv)
                                  (procedure (convert-tvars (list (array tv)))
                                             (number)))))
   (cons 'vector-ref (forall (lambda (tv)
                               (procedure (convert-tvars (list (array tv)
                                                               (number)))
                                          tv))))
   (cons 'vector-set! (forall (lambda (tv)
                                (procedure (convert-tvars (list (array tv)
                                                                (number)
                                                                tv))
                                           dynamic))))
   ))

(define procedure-env
  (list
   (cons 'procedure? (forall (lambda (tv)
                               (procedure (convert-tvars (list tv)) (boolean)))))
   (cons 'map (forall2 (lambda (tv1 tv2)
                         (procedure (convert-tvars
                                     (list (procedure (convert-tvars
                                                       (list tv1)) tv2)
                                           (list-type tv1)))
                                    (list-type tv2)))))
   (cons 'foreach (forall2 (lambda (tv1 tv2)
                             (procedure (convert-tvars
                                         (list (procedure (convert-tvars
                                                           (list tv1)) tv2)
                                               (list-type tv1)))
                                        (list-type tv2)))))
   (cons 'call-with-current-continuation
         (forall2 (lambda (tv1 tv2) 
                   (procedure (convert-tvars
                               (list (procedure
                                      (convert-tvars
                                       (list (procedure (convert-tvars
                                                         (list tv1)) tv2)))
                                      tv2)))
                              tv2))))
   ))


; global top level environment

(define (global-env)
  (append misc-env
          io-env
          boolean-env
          symbol-env
          number-env
          char-env
          string-env
          vector-env
          procedure-env
          list-env))

(define dynamic-top-level-env (global-env))

(define (init-dynamic-top-level-env!)
  (set! dynamic-top-level-env (global-env))
  '())

(define (dynamic-top-level-env-show)
  ; displays the top level environment
  (map (lambda (binding)
         (cons (key-show (binding-key binding))
               (cons ': (tvar-show (binding-value binding)))))
       (env->list dynamic-top-level-env)))
; ----------------------------------------------------------------------------
; Dynamic type inference for Scheme
; ----------------------------------------------------------------------------

; Needed packages:

(define (ic!) (init-global-constraints!))
(define (pc) (glob-constr-show))
(define (lc) (length global-constraints))
(define (n!) (normalize-global-constraints!))
(define (pt) (dynamic-top-level-env-show))
(define (it!) (init-dynamic-top-level-env!))
(define (io!) (set! tag-ops 0) (set! no-ops 0))
(define (i!) (ic!) (it!) (io!) '())

(define tag-ops 0)
(define no-ops 0)


(define doit 
  (lambda ()
    (i!)
    (let ((foo (dynamic-parse-file \"../../src/dynamic.scm\")))
      (normalize-global-constraints!)
      (reset-counters!)
      (tag-ast*-show foo)
      (counters-show))))

(define (main . args)
  (run-benchmark
   \"dynamic\"
   dynamic-iters
   (lambda (result) (equal? result '((218 . 455) (6 . 1892) (2204 . 446))))
   (lambda () (lambda () (doit)))))
")

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 string input-text)
(define iterations int 500)

(define* run (subr parses (int val) val)
  (lambda (i result) (if (= i 0) result (run (- i 1) (doit input1)))))
(val->datum (run iterations v-null))
