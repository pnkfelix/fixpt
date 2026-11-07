;;; Typed hygienic macros, in FX-26: syntax types (Herman's `σ`), as the
;;; Rust expander has them (`macros.rs`, whose comment says the notation),
;;; read from syntax, and compared: by the shapes of source syntax
;;; (`overlap`, `fits`) and as types (`sub`). Part of the expander
;;; (`macros.fx`, which loads it). How one fails is the caller's (`fails`),
;;; as `parser-forms.fx`'s.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define parser-module ((proj (load-module "fx26:parser.fx") rs re rm rc rp)))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted vec (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol len nth
        (type syns-a names) (effect parses))
(define kernel (load-module "fx26:macros-kernel.fx"))

;; How a part of the expander fails: the caller's `pfail-at`.
(define-type fails (subr parses (string int int) void))
(define fail-at (->* (fails string syn) void)
  (lambda (fail message s) (fail message (syn-start s) (syn-end s))))

;;; ------------------------------------------------------------ the types

;; An address's steps from its root, first first: `#t` the car.
(define-type addr (listof bool acyclic))
;; What a part at an address binds (Herman's `δ`): 0 nothing, 1 a variable,
;; 2 a rib, 3 a ribcage.
(define-type entries (listof (tupleof addr int) acyclic))
;; One of a ribcage's: a rib, or the ribcage exported at an address.
(define-datatype ring (ring-rib entries) (ring-at addr))
(define-type rings (listof ring acyclic))
;; What an annotation binds (Herman's `β`): a rib, or a ribcage.
(define-datatype bind (bind-rib entries) (bind-cage rings))
;; A syntax type. A `mu` is by its number in `mus`, its variable the same.
(define-datatype sty
  (s-expr) (s-bvar) (s-id) (s-data) (s-type) (s-label) (s-nil)
  (s-literal symbol) (s-pair sty sty) (s-import sty bind) (s-export sty bind)
  (s-mu int) (s-many sty) (s-union (listof sty acyclic)))
(define-type stys (listof sty acyclic))

;; Each `mu`'s body, by its number: the program's, and every file's
;; macros', which refer to them by number.
(define mus (ref (arrayof sty rs) rs) (new (make-array 64 (s-nil))))
(define nmus (ref int rs) (new 0))
(define mu-body (->* (int) sty) (lambda (i) (array-ref (get mus) i)))
;; A new `mu`, its body not yet read: its number.
(define mu-new (->* () int)
  (lambda ()
    (let ((n (get nmus)))
      (begin
        (if (= n (array-length (get mus)))
            (let ((bigger (the (arrayof sty rs) (make-array (* 2 n) (s-nil)))))
              (begin (copy-stys (get mus) bigger 0) (set mus bigger)))
            #u)
        (set nmus (+ n 1))
        n))))
(define copy-stys (->* ((arrayof sty rs) (arrayof sty rs) int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i)) (copy-stys from to (+ i 1))))))
(define mu-set! (->* (int sty) unit) (lambda (i t) (array-set! (get mus) i t)))

;;; ------------------------------------------------------------ names

;; Whether `name` is a form's, `#%fx`, `#%toplevel` or `define-syntax`: never
;; bound, so never a binder or a variable.
(define reserved? (->* (string) bool)
  (lambda (name)
    (or (string=? name "#%fx") (string=? name "#%toplevel") (string=? name "define-syntax")
        (word-in? name (with kernel reserved-words)))))
(define word-in? (->* (string datum) bool)
  (lambda (name ws)
    (and (pair? ws)
         (or (and (symbol? (car ws)) (string=? name (symbol->string (car ws))))
             (word-in? name (cdr ws))))))
;; Whether `s` is a name, and a reserved one.
(define reserved-syn? (->* (syn) bool)
  (lambda (s) (and (syn-symbol? s) (reserved? (syn-name s)))))
(define name-in? (->* (symbol names) bool)
  (lambda (n ns) (and (not (null? ns)) (or (symbol=? n (car ns)) (name-in? n (cdr ns))))))

;;; ------------------------------------------------------------ syntax

;; Whether `s` is `()`.
(define syn-nil? (->* (syn) bool)
  (lambda (s)
    (tagcase s
      (atom (d a b x) (null? d))
      (lst (items d a b x) (null? items))
      (else y #f))))
;; Whether `s` is a keyword, `#:name`.
(define syn-keyword? (->* (syn) bool)
  (lambda (s) (tagcase s (atom (d a b x) (keyword? d)) (else y #f))))
;; A list's car and cdr, the cdr a list of the rest (or the tail), in a list
;; of two; none if `s` is no pair.
(define split (->* (syn) syns-a)
  (lambda (s)
    (tagcase s
      (lst (items d a b x)
        (if (null? items)
            nil
            (list (car items)
                  (if (null? (cdr items))
                      (atom '() a b x)
                      (lst (cdr items) (if (pair? d) (cdr d) d) a b x)))))
      (dotted (items tail d a b x)
        (list (car items)
              (if (null? (cdr items))
                  tail
                  (dotted (cdr items) tail (if (pair? d) (cdr d) d) a b x))))
      (else y nil))))
;; `d`, a datum, as syntax at no place.
(define datum->syn (->* (datum) syn)
  (lambda (d)
    (if (pair? d)
        (let ((parts (datum-parts d)))
          (if (null? (cdr parts))
              (lst (car parts) d 0 0 0)
              (dotted (car parts) (car (car (cdr parts))) d 0 0 0)))
        (atom d 0 0 0))))
;; A pair's elements as syntax, and its tail if it is not `()`, in a list.
(define datum-parts (->* (datum) (listof syns-a acyclic))
  (lambda (d)
    (letrec ((go (subr (maxeff (read @globals) spin) (datum) syns-a)
               (lambda (x) (if (pair? x) (cons (datum->syn (car x)) (go (cdr x))) nil)))
             (end (subr (maxeff (read @globals) spin) (datum) datum)
               (lambda (x) (if (pair? x) (end (cdr x)) x))))
      (let ((e (end d)))
        (if (null? e)
            (list (go d))
            (list (go d) (the syns-a (list (atom e 0 0 0)))))))))

;; `s` written as the Rust front end's `write_syntax` writes it, for what
;; is said of it.
(define show-syn (->* (syn) string)
  (lambda (s)
    (tagcase s
      (lst (items d a b x) (if (null? items) "()" (string-append "(" (show-each items) ")")))
      (dotted (items tail d a b x)
        (string-append "(" (show-each items) " . " (show-syn tail) ")"))
      (vec (items d a b x) (string-append "#(" (show-each items) ")"))
      (atom (d a b x) (show-datum d)))))
(define show-each (->* (syns-a) string)
  (lambda (xs)
    (cond ((null? xs) "")
          ((null? (cdr xs)) (show-syn (car xs)))
          (else (string-append (show-syn (car xs)) " " (show-each (cdr xs)))))))
(define show-datum (->* (datum) string)
  (lambda (d)
    (cond ((null? d) "()")
          ((symbol? d) (symbol->string d))
          ((keyword? d) (string-append "#:" (symbol->string (keyword->symbol d))))
          ((string? d) (string-append "\"" d "\""))
          ((char? d) (string-append "#\\" (char->string d)))
          ((int? d) (int->string d))
          ((f64? d) (f64->string d))
          ((bool? d) (if d "#t" "#f"))
          (else "…"))))

;;; ------------------------------------------------------------ reading

;; Syntax type `s`, read: `named`'s names (the kernel's abbreviations), and
;; the `mu` variables in scope, innermost first.
(define-type named (listof (tupleof symbol sty) acyclic))
(define-type mu-scope (listof (tupleof symbol int) acyclic))
(define read-sty (->* (fails syn named mu-scope) sty)
  (lambda (fail s named scope)
    (cond
      ((syn-nil? s) (s-nil))
      ((syn-symbol? s) (read-sty-name fail s named scope))
      (else
       (let* ((parts (split s)) (hd (if (null? parts) s (car parts)))
              ;; The forms below are proper lists; a dotted one is a pair.
              (head (if (and (syn-symbol? hd) (proper? s)) (syn-name hd) "")))
         (cond
           ((null? parts) (begin (fail-at fail "a syntax type: not one" s) (s-nil)))
           ((or (string=? head "import") (string=? head "export"))
            (let ((args (proper-items s)))
              (if (= (len args) 3)
                  (let ((body (read-sty fail (nth args 1) named scope))
                        (b (read-bind fail (nth args 2))))
                    (if (string=? head "import") (s-import body b) (s-export body b)))
                  (read-pair fail s parts named scope))))
           ((string=? head "mu") (read-mu fail s named scope))
           ((string=? head "union")
            (let ((ms (read-each fail (cdr (proper-items s)) named scope)))
              (begin (if (any-overlap? ms)
                         (fail-at fail (string-append "a syntax type: a `union`'s members must be "
                                                      "told apart by their shapes in the source "
                                                      "(an `expr` may be anything)")
                                  s)
                         #u)
                     (s-union ms))))
           ((and (string=? head "many") (= (len (proper-items s)) 2))
            (s-many (read-sty fail (nth (proper-items s) 1) named scope)))
           ((and (string=? head "literal") (= (len (proper-items s)) 2))
            (if (syn-symbol? (nth (proper-items s) 1))
                (s-literal (syn-symbol (nth (proper-items s) 1)))
                (begin (fail-at fail "a syntax type: `(literal name)`" s) (s-nil))))
           (else (read-pair fail s parts named scope))))))))
(define read-pair (->* (fails syn syns-a named mu-scope) sty)
  (lambda (fail s parts named scope)
    (s-pair (read-sty fail (car parts) named scope) (read-sty fail (nth parts 1) named scope))))
(define read-each (->* (fails syns-a named mu-scope) stys)
  (lambda (fail xs named scope)
    (if (null? xs)
        nil
        (cons (read-sty fail (car xs) named scope) (read-each fail (cdr xs) named scope)))))
(define read-sty-name (->* (fails syn named mu-scope) sty)
  (lambda (fail s named scope)
    (let ((n (syn-symbol s)))
      (let ((mu (scope-of n scope)))
        (if (>= mu 0)
            (s-mu mu)
            (let ((t (named-of n named)))
              (if (null? t)
                  (case n
                    ((expr) (s-expr)) ((bvar) (s-bvar)) ((id) (s-id)) ((data) (s-data))
                    ((type) (s-type)) ((label) (s-label))
                    (else
                     (begin
                       (fail-at fail (string-append "a syntax type: `" (symbol->string n) "` is "
                                                    "none (`expr`, `bvar`, `id`, `data`, `type`, "
                                                    "`label`, or a `mu`'s variable)")
                                s)
                       (s-nil))))
                  (car t))))))))
(define scope-of (->* (symbol mu-scope) int)
  (lambda (n scope)
    (cond ((null? scope) -1)
          ((symbol=? n (extract (car scope) 1)) (extract (car scope) 2))
          (else (scope-of n (cdr scope))))))
(define named-of (->* (symbol named) stys)
  (lambda (n named)
    (cond ((null? named) nil)
          ((symbol=? n (extract (car named) 1)) (list (extract (car named) 2)))
          (else (named-of n (cdr named))))))
;; `(mu v body)`.
(define read-mu (->* (fails syn named mu-scope) sty)
  (lambda (fail s named scope)
    (let ((args (proper-items s)))
      (if (and (= (len args) 3) (syn-symbol? (nth args 1)))
          (let* ((id (mu-new))
                 (body (read-sty fail (nth args 2) named
                                 (cons (tuple (syn-symbol (nth args 1)) id) scope))))
            (begin
              (if (guarded? body id)
                  #u
                  (fail-at fail (string-append "a syntax type: a `mu`'s variable is used where no "
                                               "pair is around it (Herman's types are "
                                               "contractive)")
                           s))
              (mu-set! id body)
              (s-mu id)))
          (begin (fail-at fail "a syntax type: `(mu variable type)`" s) (s-nil))))))
;; Whether `s` is a proper list of one or more.
(define proper? (->* (syn) bool)
  (lambda (s) (tagcase s (lst (items d a b x) (not (null? items))) (else y #f))))

;; A binding, `(rho (address δ) …)` or `(cage (rho …) (at address) …)`.
(define bind-usage string
  "a binding is `(rho (address δ) …)` or `(cage (rho …) (at address) …)`")
(define read-bind (->* (fails syn) bind)
  (lambda (fail b)
    (let* ((items (proper-items b)) (head (if (and (pair? items) (syn-symbol? (car items)))
                                             (syn-name (car items))
                                             "")))
      (cond ((string=? head "rho") (bind-rib (read-rib fail (cdr items))))
            ((string=? head "cage") (bind-cage (read-rings fail (cdr items))))
            (else (begin (fail-at fail bind-usage b) (bind-rib nil)))))))
(define read-rings (->* (fails syns-a) rings)
  (lambda (fail rs)
    (if (null? rs)
        nil
        (let* ((parts (proper-items (car rs)))
               (head (if (and (pair? parts) (syn-symbol? (car parts))) (syn-name (car parts)) ""))
               (r (cond ((string=? head "rho") (ring-rib (read-rib fail (cdr parts))))
                        ((and (string=? head "at") (= (len parts) 2))
                         (ring-at (read-addr fail (nth parts 1))))
                        (else (begin (fail-at fail bind-usage (car rs)) (ring-rib nil))))))
          (cons r (read-rings fail (cdr rs)))))))
(define read-rib (->* (fails syns-a) entries)
  (lambda (fail es)
    (if (null? es)
        nil
        (let ((parts (proper-items (car es))))
          (if (= (len parts) 2)
              (cons (tuple (read-addr fail (car parts)) (read-delta fail (nth parts 1)))
                    (read-rib fail (cdr es)))
              (begin (fail-at fail bind-usage (car es)) (the entries nil)))))))
(define read-delta (->* (fails syn) int)
  (lambda (fail d)
    (let ((n (if (syn-symbol? d) (syn-name d) "")))
      (cond ((string=? n "none") 0) ((string=? n "var") 1) ((string=? n "rib") 2)
            ((string=? n "env") 3)
            (else (begin (fail-at fail "δ is `none`, `var`, `rib` or `env`" d) 0))))))
;; An address, `A`s and `D`s read right to left: its steps, first first.
(define read-addr (->* (fails syn) addr)
  (lambda (fail a)
    (let ((name (if (syn-symbol? a) (syn-name a) "")))
      (if (and (> (string-length name) 0) (a-or-d? name 0))
          (steps name 0 nil)
          (begin (fail-at fail (string-append "an address is a word of `A` (car) and `D` (cdr), "
                                              "read right to left")
                          a)
                 (the addr nil))))))
(define a-or-d? (->* (string int) bool)
  (lambda (s i)
    (or (= i (string-length s))
        (and (or (char=? (string-ref s i) #\A) (char=? (string-ref s i) #\D))
             (a-or-d? s (+ i 1))))))
;; The steps of `s`'s letters, the last first: from `j` on, onto `out`.
(define steps (->* (string int addr) addr)
  (lambda (s j out)
    (if (= j (string-length s))
        out
        (steps s (+ j 1) (cons (char=? (string-ref s j) #\A) out)))))
;; A proper list's elements; none if `s` is not one.
(define proper-items (->* (syn) syns-a)
  (lambda (s) (tagcase s (lst (items d a b x) items) (else y nil))))

;; The kernel's forms' signatures, each by its name, and its abbreviations
;; read on the way: read once, the first time.
(define kernel-read (ref named rs) (new nil))
(define kernel-sigs (->* (fails) named)
  (lambda (fail)
    (begin
      (if (null? (get kernel-read))
          (set kernel-read (read-kernel fail (proper-items (datum->syn (with kernel kernel-forms)))
                                        nil nil))
          #u)
      (get kernel-read))))
(define read-kernel (->* (fails syns-a named named) named)
  (lambda (fail fs named out)
    (if (null? fs)
        out
        (let* ((items (proper-items (car fs)))
               (t (read-sty fail (nth items 2) named nil))
               (n (syn-symbol (nth items 1))))
          (if (string=? (syn-name (car items)) "define")
              (read-kernel fail (cdr fs) (cons (tuple n t) named) out)
              (read-kernel fail (cdr fs) named (cons (tuple n t) out)))))))

;;; ------------------------------------------------------------ comparing

;; The type at `t`, its annotations, `mu`s seen through to what is under
;; them.
(define unfold (->* (sty) sty)
  (lambda (t)
    (tagcase t
      (s-import (b x) (unfold b)) (s-export (b x) (unfold b)) (s-many (b) (unfold b))
      (s-mu (id) (unfold (mu-body id)))
      (else y t))))
;; Whether `t` uses `mu` `id`'s variable only under a pair.
(define guarded? (->* (sty int) bool)
  (lambda (t id)
    (tagcase t
      (s-mu (j) (not (= j id)))
      (s-import (b x) (guarded? b id)) (s-export (b x) (guarded? b id)) (s-many (b) (guarded? b id))
      (s-union (ms) (all-guarded? ms id))
      (else y #t))))
(define all-guarded? (->* (stys int) bool)
  (lambda (ms id) (or (null? ms) (and (guarded? (car ms) id) (all-guarded? (cdr ms) id)))))

;; Whether some source syntax could be of both `a` and `b` (Herman's
;; shapes, §5.2.3): `expr` may be anything but a form's name; looked at to
;; `depth` pairs, past which they are taken to overlap.
(define overlap? (->* (sty sty int) bool)
  (lambda (a0 b0 depth)
    (let ((a (unfold a0)) (b (unfold b0)))
      (tagcase a
        (s-union (ms) (any-overlaps? ms b depth))
        (else y
          (tagcase b
            (s-union (ms) (any-overlaps-of? a ms depth))
            (else z (overlap-base? a b depth))))))))
(define any-overlaps? (->* (stys sty int) bool)
  (lambda (ms b depth)
    (and (not (null? ms)) (or (overlap? (car ms) b depth) (any-overlaps? (cdr ms) b depth)))))
(define any-overlaps-of? (->* (sty stys int) bool)
  (lambda (a ms depth)
    (and (not (null? ms)) (or (overlap? a (car ms) depth) (any-overlaps-of? a (cdr ms) depth)))))
;; A kind's number, for the cases of `overlap-base?`: 0 expr, 1 bvar, 2 id,
;; 3 data, 4 type, 5 label, 6 nil, 7 literal, 8 pair, 9 anything else.
(define kind-of (->* (sty) int)
  (lambda (t)
    (tagcase t
      (s-expr () 0) (s-bvar () 1) (s-id () 2) (s-data () 3) (s-type () 4) (s-label () 5)
      (s-nil () 6) (s-literal (n) 7) (s-pair (a d) 8) (else y 9))))
(define literal-of (->* (sty) symbol)
  (lambda (t) (tagcase t (s-literal (n) n) (else y (string->symbol "")))))
(define overlap-base? (->* (sty sty int) bool)
  (lambda (a b depth)
    (let ((ka (kind-of a)) (kb (kind-of b)))
      (cond
        ((and (= ka 7) (or (= kb 0) (= kb 1))) #f)
        ((and (= kb 7) (or (= ka 0) (= ka 1))) #f)
        ((and (= ka 7) (= kb 7)) (symbol=? (literal-of a) (literal-of b)))
        ((or (and (= ka 7) (= kb 2)) (and (= ka 2) (= kb 7))) #t)
        ((or (= ka 0) (= ka 3) (= ka 4) (= kb 0) (= kb 3) (= kb 4)) #t)
        ((and (= ka 8) (= kb 8))
         (or (= depth 0)
             (tagcase a
               (s-pair (a1 d1)
                 (tagcase b
                   (s-pair (a2 d2) (and (overlap? a1 a2 (- depth 1)) (overlap? d1 d2 (- depth 1))))
                   (else y #f)))
               (else y #f))))
        ((and (= ka 6) (= kb 6)) #t)
        ((and (= ka 5) (= kb 5)) #t)
        ((or (= ka 5) (= kb 5)) #f)
        ((and (or (= ka 1) (= ka 2)) (or (= kb 1) (= kb 2))) #t)
        (else #f)))))
;; Whether two of `ms` overlap.
(define any-overlap? (->* (stys) bool)
  (lambda (ms)
    (and (not (null? ms))
         (or (any-overlaps-of? (car ms) (cdr ms) 6) (any-overlap? (cdr ms))))))

;; Whether `s` has the shape of `t`, in `mode` (0 a pattern, 1 a template,
;; 2 a use): a pattern variable in a template (`pvar?`), or any name in a
;; pattern, fits anything.
(define fits? (->* (sty syn int (subr pure (symbol) bool)) bool)
  (lambda (t s mode pvar?)
    (let ((u (unfold t)))
      (if (and (syn-symbol? s)
               (or (and (= mode 0) (not (= (kind-of u) 7)) (not (string=? (syn-name s) "_")))
                   (and (= mode 1) (pvar? (syn-symbol s)))))
          #t
          (tagcase u
            (s-union (ms) (any-fits? ms s mode pvar?))
            (s-pair (a d)
              (let ((parts (split s)))
                (and (not (null? parts))
                     (fits? a (car parts) mode pvar?) (fits? d (nth parts 1) mode pvar?))))
            (s-nil () (syn-nil? s))
            (s-literal (n) (and (syn-symbol? s) (symbol=? (syn-symbol s) n)))
            (s-bvar () (and (syn-symbol? s) (not (reserved-syn? s))))
            (s-id () (syn-symbol? s))
            (s-label () (or (syn-keyword? s) (and (= mode 2) (syn-symbol? s))))
            (s-expr () (and (not (reserved-syn? s)) (not (syn-nil? s))))
            (else y #t))))))
(define any-fits? (->* (stys syn int (subr pure (symbol) bool)) bool)
  (lambda (ms s mode pvar?)
    (and (not (null? ms)) (or (fits? (car ms) s mode pvar?) (any-fits? (cdr ms) s mode pvar?)))))

;; Whether two types are the same, structurally (a `mu` by its number).
(define sty=? (->* (sty sty) bool)
  (lambda (a b)
    (tagcase a
      (s-literal (n) (tagcase b (s-literal (m) (symbol=? n m)) (else y #f)))
      (s-pair (x y) (tagcase b (s-pair (p q) (and (sty=? x p) (sty=? y q))) (else z #f)))
      (s-import (x p) (tagcase b (s-import (y q) (and (sty=? x y) (bind=? p q))) (else z #f)))
      (s-export (x p) (tagcase b (s-export (y q) (and (sty=? x y) (bind=? p q))) (else z #f)))
      (s-mu (i) (tagcase b (s-mu (j) (= i j)) (else y #f)))
      (s-many (x) (tagcase b (s-many (y) (sty=? x y)) (else z #f)))
      (s-union (ms) (tagcase b (s-union (ns) (all-sty=? ms ns)) (else y #f)))
      (else y (and (< (kind-of a) 7) (= (kind-of a) (kind-of b)))))))
(define all-sty=? (->* (stys stys) bool)
  (lambda (ms ns)
    (if (null? ms)
        (null? ns)
        (and (not (null? ns)) (sty=? (car ms) (car ns)) (all-sty=? (cdr ms) (cdr ns))))))
(define bind=? (->* (bind bind) bool)
  (lambda (p q)
    (tagcase p
      (bind-rib (es) (tagcase q (bind-rib (fs) (entries=? es fs)) (else y #f)))
      (bind-cage (rs) (tagcase q (bind-cage (ss) (rings=? rs ss)) (else y #f))))))
(define rings=? (->* (rings rings) bool)
  (lambda (rs ss)
    (if (null? rs)
        (null? ss)
        (and (not (null? ss))
             (tagcase (car rs)
               (ring-rib (es) (tagcase (car ss) (ring-rib (fs) (entries=? es fs)) (else y #f)))
               (ring-at (a) (tagcase (car ss) (ring-at (b) (addr=? a b)) (else y #f))))
             (rings=? (cdr rs) (cdr ss))))))
(define entries=? (->* (entries entries) bool)
  (lambda (es fs)
    (if (null? es)
        (null? fs)
        (and (not (null? fs))
             (addr=? (extract (car es) 1) (extract (car fs) 1))
             (= (extract (car es) 2) (extract (car fs) 2))
             (entries=? (cdr es) (cdr fs))))))
(define addr=? (->* (addr addr) bool)
  (lambda (a b)
    (if (null? a)
        (null? b)
        (and (not (null? b)) (eq? (car a) (car b)) (addr=? (cdr a) (cdr b))))))

;; Whether syntax of type `a` is all of type `b`, binding structure alike:
;; coinductive, as FX-26's recursive types are, each pair compared assumed
;; (`assumed`) while it is, by structure.
(define-type assumed (listof (tupleof sty sty) acyclic))
(define sub? (->* (sty sty assumed) bool)
  (lambda (a b assumed)
    (if (or (sty=? a b) (assumed? a b assumed))
        #t
        (let ((more (the assumed (cons (tuple a b) assumed))))
          (tagcase a
            (s-many (x) (sub? x b more))
            (s-mu (i) (sub? (mu-body i) b more))
            (s-union (ms) (all-sub? ms b more))
            (else y
              (tagcase b
                (s-many (x) (sub? a x more))
                (s-mu (j) (sub? a (mu-body j) more))
                (s-union (ms) (any-sub? a ms more))
                (else z (sub-base? a b more)))))))))
(define sub-base? (->* (sty sty assumed) bool)
  (lambda (a b more)
    (tagcase a
      (s-import (x p) (tagcase b (s-import (y q) (and (bind=? p q) (sub? x y more))) (else z #f)))
      (s-export (x p) (tagcase b (s-export (y q) (and (bind=? p q) (sub? x y more))) (else z #f)))
      (s-pair (a1 d1)
        (tagcase b (s-pair (a2 d2) (and (sub? a1 a2 more) (sub? d1 d2 more))) (else z #f)))
      (else y (sty=? a b)))))
(define assumed? (->* (sty sty assumed) bool)
  (lambda (a b xs)
    (and (not (null? xs))
         (or (and (sty=? a (extract (car xs) 1)) (sty=? b (extract (car xs) 2)))
             (assumed? a b (cdr xs))))))
(define all-sub? (->* (stys sty assumed) bool)
  (lambda (ms b more) (or (null? ms) (and (sub? (car ms) b more) (all-sub? (cdr ms) b more)))))
(define any-sub? (->* (sty stys assumed) bool)
  (lambda (a ms more)
    (and (not (null? ms)) (or (sub? a (car ms) more) (any-sub? a (cdr ms) more)))))
