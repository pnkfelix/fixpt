;;; Procedural macros, a prototype, in the expander written in FX-26
;;; (`macros/procedural.rs`, the Rust one's; `TODO.md` §228): explicit
;;; renaming, `(er-macro-transformer proc)`, and syntactic closures,
;;; `(sc-macro-transformer proc)` and `(rsc-macro-transformer proc)`. The
;;; transformer, FX-26 text, is checked and run by the runtime's own session
;;; for them (`%macros:expand-procedural`), the one the Rust expander uses;
;;; what is decided of its answer is decided here, as there: its syntactic
;;; closures opened, its aliases that name keywords made the keywords, and
;;; quoted ones their names. On top of `macros-solve.fx`, which it loads and
;;; gives on (`solve-module`), for `macros.fx`.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define solve-module ((proj (load-module "fx26:macros-solve.fx") rs re rm rc rp)))
(define infer-module (with solve-module infer-module))
(define files-module (with infer-module files-module))
(define align-module (with files-module align-module))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted vec (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol syn-datums syn->datum
        syn-expansion len (type syns-a))
(import types-module reserved? desc-word? type-form? kernel-sigs kernel-definitions s-expr
        (type fails sty))
(import align-module macro? defined def-env-top
        (type macro clauses def-env def-envs macro-env scopes))


;;; ------------------------------------------------------------ the programs

;; A style, by its form's name: 0 explicit renaming, 1 syntactic closures,
;; 2 reversed; -1 none.
(define style-named (->* (string) int)
  (lambda (n)
    (cond ((string=? n "er-macro-transformer") 0)
          ((string=? n "sc-macro-transformer") 1)
          ((string=? n "rsc-macro-transformer") 2)
          (else -1))))
;; The type a transformer of style `s` is checked at.
(define style-type (->* (int) string)
  (lambda (s)
    (if (= s 0)
        (string-append "(subr spin (datum (subr pure (symbol) symbol) "
                       "(subr spin (symbol symbol) bool)) datum)")
        "(subr spin (datum symbol) datum)")))
;; `code` with the prelude's procedures bound around it, as locals.
(define helpers (->* (string) string)
  (lambda (code)
    (string-append "(let ((make-syntactic-closure %make-syntactic-closure) "
                   "(identifier? %identifier?) (identifier=? %identifier=?)) "
                   code ")")))
;; The program that checks a transformer.
(define checked-text (->* (int string) string)
  (lambda (s code)
    (string-append "(begin (the " (style-type s) " " (helpers code) ") #u)")))
;; The program that runs one on `form` (as text), in expansion `made`.
(define applied-text (->* (int string string int) string)
  (lambda (s code form made)
    (let ((head (string-append "((the " (style-type s) " " (helpers code) ") (quote " form ") ")))
      (cond ((= s 0)
             (string-append head "(%er-renamer " (int->string made) ") %er-compare)"))
            ((= s 1) (string-append head "(quote %env:use))"))
            (else (string-append head "(quote %env:macro))"))))))
;; The runtime's answer to `code`: what it gave (`=`), or why not (`!`),
;; in a sum.
(define run (->* (string) (sumof (ok string) (failed string)))
  (lambda (code)
    (let ((a (%macros:expand-procedural code)))
      (if (and (> (string-length a) 0) (char=? (string-ref a 0) #\=))
          (sum ok (substring a 1 (string-length a)))
          (sum failed (if (> (string-length a) 0) (substring a 1 (string-length a)) a))))))

;;; ------------------------------------------------------------ written

;; `s` as text the reader reads back.
(define syn-text (->* (syn) string)
  (lambda (s)
    (tagcase s
      (atom (d a b x) (datum-text d))
      (lst (items d a b x) (string-append "(" (syns-text items) ")"))
      (dotted (items tail d a b x)
        (string-append "(" (syns-text items) " . " (syn-text tail) ")"))
      (vec (items d a b x) (string-append "#(" (syns-text items) ")")))))
(define syns-text (->* (syns-a) string)
  (lambda (xs)
    (cond ((null? xs) "")
          ((null? (cdr xs)) (syn-text (car xs)))
          (else (string-append (syn-text (car xs)) " " (syns-text (cdr xs)))))))
(define datum-text (->* (datum) string)
  (lambda (d)
    (cond ((null? d) "()")
          ((symbol? d) (symbol->string d))
          ((keyword? d) (string-append "#:" (symbol->string (keyword->symbol d))))
          ((string? d) (string-append "\"" (escaped d 0 "") "\""))
          ((char? d) (char-text d))
          ((int? d) (int->string d))
          ((f64? d) (f64->string d))
          ((bool? d) (if d "#t" "#f"))
          (else "#u"))))
(define escaped (->* (string int string) string)
  (lambda (s i out)
    (if (>= i (string-length s))
        out
        (let ((c (string-ref s i)))
          (escaped s (+ i 1)
                   (string-append out (cond ((char=? c #\") "\\\"")
                                            ((char=? c #\\) "\\\\")
                                            ((char=? c (integer->char 10)) "\\n")
                                            (else (char->string c)))))))))
(define char-text (->* (char) string)
  (lambda (c)
    (cond ((char=? c #\space) "#\\space")
          ((char=? c (integer->char 10)) "#\\newline")
          ((char=? c (integer->char 9)) "#\\tab")
          (else (string-append "#\\" (char->string c))))))

;;; ------------------------------------------------------------ places

;; Where a part a template made is: a key of its own, which no other part
;; and no text has, a place past every text's (`source-base`, above the
;; positions of every file loaded, `load-base` apart); and, by its key,
;; where the template wrote it and which expansion made it, for what is
;; said of it (`source-of`; the driver's `fx26_span`), as the Rust front
;; end's `Span` has a template's place and its `expansion`. Provenance
;; only: what the checkers find of an expression is keyed by its place in
;; the parser's walk (`docs/research/loads-and-places.md`), so parts that
;; share a key, or a part placed twice, are told apart. Keys are made
;; in order, a list's start before its parts' and its end after, so that
;; a part is within its list. One table for the session, so that no key is
;; given twice.
(define source-base int 1125899906842624)
(define sources (ref (arrayof (tupleof int int) rs) rs) (new (make-array 1024 (tuple 0 0))))
(define nsources (ref int rs) (new 0))
;; A new key, for template place `p`, of expansion `made`; none in a
;; template's check (`made` 0), whose places are the template's.
(define source-key (->* (int int) int)
  (lambda (p made)
    (if (= made 0) p (new-source-key p made))))
(define new-source-key (->* (int int) int)
  (lambda (p made)
    (let ((i (get nsources)))
      (begin
        (if (= i (array-length (get sources)))
            (let ((bigger (the (arrayof (tupleof int int) rs) (make-array (* 2 i) (tuple 0 0)))))
              (begin (copy-sources (get sources) bigger 0) (set sources bigger)))
            #u)
        (array-set! (get sources) i (tuple p made))
        (set nsources (+ i 1))
        (+ source-base i)))))
(define copy-sources (->* ((arrayof (tupleof int int) rs) (arrayof (tupleof int int) rs) int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i)) (copy-sources from to (+ i 1))))))
;; How many keys have been made: the next one's number, from `source-base`.
(define sources-made (->* () int) (lambda () (get nsources)))
;; Key `k`'s template place and expansion; a place that is no key, itself
;; and 0.
(define source-of (->* (int) (tupleof int int))
  (lambda (k)
    (let ((i (- k source-base)))
      (if (and (>= i 0) (< i (get nsources))) (array-ref (get sources) i) (tuple k 0)))))

;;; ------------------------------------------------------------ read

;; What the runtime gave, `text`, read: a datum's syntax, every part at
;; `a`..`b` of expansion `x`, the use's place; none if it is not one.
(define-type read-one (listof (tupleof syn int) acyclic))
(define read-answer (->* (string int int int) (listof syn acyclic))
  (lambda (text a b x)
    (let ((r (read-at text (skip text 0) a b x)))
      (if (and (not (null? r)) (= (skip text (extract (car r) 2)) (string-length text)))
          (list (extract (car r) 1))
          nil))))
(define delimiter? (->* (char) bool)
  (lambda (c) (or (char-whitespace? c) (char=? c #\() (char=? c #\)) (char=? c #\"))))
(define skip (->* (string int) int)
  (lambda (s i)
    (if (and (< i (string-length s)) (char-whitespace? (string-ref s i))) (skip s (+ i 1)) i)))
;; The datum at `i`, and where it ends.
(define read-at (->* (string int int int int) read-one)
  (lambda (s i a b x)
    (if (>= i (string-length s))
        nil
        (let ((c (string-ref s i)))
          (cond ((char=? c #\() (read-items s (skip s (+ i 1)) a b x nil))
                ((char=? c #\") (read-string-at s (+ i 1) "" a b x))
                ((char=? c #\')
                 (let ((r (read-at s (skip s (+ i 1)) a b x)))
                   (if (null? r)
                       nil
                       (let ((q (list (atom 'quote a b x) (extract (car r) 1))))
                         (list (tuple (lst q (syn-datums q) a b x) (extract (car r) 2)))))))
                ((and (char=? c #\#) (< (+ i 1) (string-length s))
                      (char=? (string-ref s (+ i 1)) #\())
                 (let ((r (read-items s (skip s (+ i 2)) a b x nil)))
                   (if (null? r)
                       nil
                       (tagcase (extract (car r) 1)
                         (lst (items d a2 b2 x2)
                           (list (tuple (vec items (datum-list->vector (syn-datums items)) a b x)
                                        (extract (car r) 2))))
                         (else y nil)))))
                (else (read-token s i (token-end s i) a b x)))))))
(define token-end (->* (string int) int)
  (lambda (s i)
    (cond ((>= i (string-length s)) i)
          ;; `#\(`: a character, not a list.
          ((and (char=? (string-ref s i) #\\) (> i 0) (char=? (string-ref s (- i 1)) #\#))
           (token-end s (+ i 2)))
          ((delimiter? (string-ref s i)) i)
          (else (token-end s (+ i 1))))))
(define read-token (->* (string int int int int int) read-one)
  (lambda (s i j a b x)
    (let* ((t (substring s i j)) (n (parse-number t 10)))
      (list (tuple (atom (cond ((not (null? n)) (car n))
                               ((string=? t "#t") #t)
                               ((string=? t "#f") #f)
                               ((and (> (string-length t) 2) (string=? (substring t 0 2) "#\\"))
                                (char-named (substring t 2 (string-length t))))
                               ((and (> (string-length t) 2) (string=? (substring t 0 2) "#:"))
                                (symbol->keyword
                                 (string->symbol (substring t 2 (string-length t)))))
                               (else (string->symbol t)))
                         a b x)
                   j)))))
(define char-named (->* (string) datum)
  (lambda (n)
    (cond ((string=? n "space") #\space)
          ((string=? n "newline") (integer->char 10))
          ((string=? n "tab") (integer->char 9))
          (else (string-ref n 0)))))
(define read-string-at (->* (string int string int int int) read-one)
  (lambda (s i out a b x)
    (cond ((>= i (string-length s)) nil)
          ((char=? (string-ref s i) #\") (list (tuple (atom out a b x) (+ i 1))))
          ((and (char=? (string-ref s i) #\\) (< (+ i 1) (string-length s)))
           (let ((c (string-ref s (+ i 1))))
             (read-string-at s (+ i 2)
                             (string-append out (if (char=? c #\n)
                                                    (char->string (integer->char 10))
                                                    (char->string c)))
                             a b x)))
          (else (read-string-at s (+ i 1) (string-append out (char->string (string-ref s i)))
                                a b x)))))
;; A list's items from `i`, `out` those read, the last first.
(define read-items (->* (string int int int int syns-a) read-one)
  (lambda (s i a b x out)
    (cond ((>= i (string-length s)) nil)
          ((char=? (string-ref s i) #\))
           (let ((items (reverse out)))
             (list (tuple (lst items (syn-datums items) a b x) (+ i 1)))))
          ((and (char=? (string-ref s i) #\.) (< (+ i 1) (string-length s))
                (delimiter? (string-ref s (+ i 1))) (not (null? out)))
           (let ((r (read-at s (skip s (+ i 1)) a b x)))
             (if (null? r)
                 nil
                 (let ((e (skip s (extract (car r) 2))) (items (reverse out))
                       (t (extract (car r) 1)))
                   (if (and (< e (string-length s)) (char=? (string-ref s e) #\)))
                       (list (tuple (dotted items t (datum-dotted (syn-datums items) (syn->datum t))
                                            a b x)
                                    (+ e 1)))
                       nil)))))
          (else
           (let ((r (read-at s i a b x)))
             (if (null? r)
                 nil
                 (read-items s (skip s (extract (car r) 2)) a b x
                             (cons (extract (car r) 1) out))))))))

;;; ------------------------------------------------------------ aliases

;; `x`'s name as where its alias's macro was defined, if it is an alias
;; (`%~N:x`): every `%~N:` taken off; else "".
(define alias-base (->* (string) string)
  (lambda (n) (alias-base-from n #f)))
(define alias-base-from (->* (string bool) string)
  (lambda (n any)
    (let ((c (if (and (> (string-length n) 2) (string=? (substring n 0 2) "%~"))
                 (digits-end n 2)
                 -1)))
      (if (and (> c 2) (< c (string-length n)) (char=? (string-ref n c) #\:))
          (alias-base-from (substring n (+ c 1) (string-length n)) #t)
          (if any n "")))))
(define digits-end (->* (string int) int)
  (lambda (s i)
    (if (and (< i (string-length s)) (char-numeric? (string-ref s i))) (digits-end s (+ i 1)) i)))
(define alias (->* (string int) string)
  (lambda (n made) (string-append "%~" (int->string made) ":" n)))

;; What a syntactic-closure transformer gave, `s`, its closures opened: in
;; the macro's environment (`macro-env`), each name an alias of expansion
;; `made`, else as written; a closure's form in its own environment, its
;; free names in the one around it; a quoted datum as it is
;; (`procedural::closed`).
(define closed (->* (fails syn bool int) syn)
  (lambda (fail s macro-env made)
    (tagcase s
      (atom (d a b x)
        (if (and macro-env (symbol? d))
            (atom (string->symbol (alias (symbol->string d) made)) a b x)
            s))
      (lst (items d a b x)
        (let ((head (head-of items)))
          (cond ((string=? head "quote") s)
                ((string=? head "%sc") (opened-closure fail s items macro-env made))
                (else (let ((xs (closed-each fail items macro-env made)))
                        (lst xs (syn-datums xs) a b x))))))
      (dotted (items tail d a b x)
        (let ((xs (closed-each fail items macro-env made)) (t (closed fail tail macro-env made)))
          (dotted xs t (datum-dotted (syn-datums xs) (syn->datum t)) a b x)))
      (vec (items d a b x) s))))
(define closed-each (->* (fails syns-a bool int) syns-a)
  (lambda (fail xs macro-env made)
    (if (null? xs) nil (cons (closed fail (car xs) macro-env made)
                             (closed-each fail (cdr xs) macro-env made)))))
(define head-of (->* (syns-a) string)
  (lambda (items)
    (if (and (not (null? items)) (syn-symbol? (car items))) (syn-name (car items)) "")))
;; A closure, `(%sc env (free …) form)`, placed where names are in
;; `outer`'s environment.
(define opened-closure (->* (fails syn syns-a bool int) syn)
  (lambda (fail s items outer made)
    (if (not (= (len items) 4))
        (begin (fail (string-append "a syntactic closure is `(%sc env (free …) form)`")
                     (syn-start s) (syn-end s))
               s)
        (let* ((env (car (cdr items))) (free (car (cdr (cdr items))))
               (form (car (cdr (cdr (cdr items)))))
               (e (if (syn-symbol? env) (syn-name env) "")))
          (cond ((not (or (string=? e "%env:use") (string=? e "%env:macro")))
                 (begin (fail "a syntactic closure's environment is one a transformer was given"
                              (syn-start env) (syn-end env))
                        s))
                (else (opened fail form (string=? e "%env:macro") outer (free-names free)
                              made)))))))
(define free-names (->* (syn) (listof symbol acyclic))
  (lambda (s)
    (tagcase s
      (lst (items d a b x) (symbols-of items))
      (else y nil))))
(define symbols-of (->* (syns-a) (listof symbol acyclic))
  (lambda (xs)
    (cond ((null? xs) nil)
          ((syn-symbol? (car xs)) (cons (syn-symbol (car xs)) (symbols-of (cdr xs))))
          (else (symbols-of (cdr xs))))))
(define in-names? (->* (symbol (listof symbol acyclic)) bool)
  (lambda (n ns) (and (not (null? ns)) (or (symbol=? n (car ns)) (in-names? n (cdr ns))))))
;; A closure's form, `s`, closed in `inner`, its `free` names in `outer`.
(define opened (->* (fails syn bool bool (listof symbol acyclic) int) syn)
  (lambda (fail s inner outer free made)
    (tagcase s
      (atom (d a b x)
        (if (and (symbol? d) (in-names? d free))
            (closed fail s outer made)
            (closed fail s inner made)))
      (lst (items d a b x)
        (let ((head (head-of items)))
          (if (or (string=? head "quote") (string=? head "%sc"))
              (closed fail s inner made)
              (let ((xs (opened-each fail items inner outer free made)))
                (lst xs (syn-datums xs) a b x)))))
      (dotted (items tail d a b x)
        (let ((xs (opened-each fail items inner outer free made))
              (t (opened fail tail inner outer free made)))
          (dotted xs t (datum-dotted (syn-datums xs) (syn->datum t)) a b x)))
      (vec (items d a b x) s))))
(define opened-each (->* (fails syns-a bool bool (listof symbol acyclic) int) syns-a)
  (lambda (fail xs inner outer free made)
    (if (null? xs)
        nil
        (cons (opened fail (car xs) inner outer free made)
              (opened-each fail (cdr xs) inner outer free made)))))

;; Whether `n` is a keyword's name, which nothing binds: a form's, a
;; description's word, a macro's (`Macros::expand_procedural`'s).
(define keyword-name? (->* (fails string) bool)
  (lambda (fail n)
    (or (reserved? n) (desc-word? n #t) (type-form? n)
        (named? n (kernel-sigs fail)) (named? n (kernel-definitions fail))
        (string=? n "else") (string=? n "=>") (string=? n "quote") (string=? n "quasiquote")
        (string=? n "unquote") (string=? n "unquote-splicing")
        (macro? (string->symbol n)))))
(define named? (->* (string (listof (tupleof symbol sty) acyclic)) bool)
  (lambda (n ns)
    (and (not (null? ns))
         (or (string=? n (symbol->string (extract (car ns) 1))) (named? n (cdr ns))))))
;; What a transformer gave, `s`, each alias that is a keyword's name made
;; the keyword, and every alias quoted made its name (`procedural::
;; keywords`).
(define keywords (->* (fails syn) syn)
  (lambda (fail s)
    (tagcase s
      (atom (d a b x)
        (if (symbol? d)
            (let ((base (alias-base (symbol->string d))))
              (if (and (not (string=? base "")) (keyword-name? fail base))
                  (atom (string->symbol base) a b x)
                  s))
            s))
      (lst (items d a b x)
        (let* ((head (head-of items)) (base (alias-base head))
               (h (if (string=? base "") head base)))
          (if (or (string=? h "quote") (string=? h "quasiquote"))
              (unaliased s)
              (let ((xs (keywords-each fail items))) (lst xs (syn-datums xs) a b x)))))
      (dotted (items tail d a b x)
        (let ((xs (keywords-each fail items)) (t (keywords fail tail)))
          (dotted xs t (datum-dotted (syn-datums xs) (syn->datum t)) a b x)))
      (vec (items d a b x)
        (let ((xs (keywords-each fail items)))
          (vec xs (datum-list->vector (syn-datums xs)) a b x))))))
(define keywords-each (->* (fails syns-a) syns-a)
  (lambda (fail xs)
    (if (null? xs) nil (cons (keywords fail (car xs)) (keywords-each fail (cdr xs))))))
;; `s` with every alias its name.
(define unaliased (->* (syn) syn)
  (lambda (s)
    (tagcase s
      (atom (d a b x)
        (if (symbol? d)
            (let ((base (alias-base (symbol->string d))))
              (if (string=? base "") s (atom (string->symbol base) a b x)))
            s))
      (lst (items d a b x) (let ((xs (unaliased-each items))) (lst xs (syn-datums xs) a b x)))
      (dotted (items tail d a b x)
        (let ((xs (unaliased-each items)) (t (unaliased tail)))
          (dotted xs t (datum-dotted (syn-datums xs) (syn->datum t)) a b x)))
      (vec (items d a b x)
        (let ((xs (unaliased-each items))) (vec xs (datum-list->vector (syn-datums xs)) a b x))))))
(define unaliased-each (->* (syns-a) syns-a)
  (lambda (xs) (if (null? xs) nil (cons (unaliased (car xs)) (unaliased-each (cdr xs))))))

;;; ------------------------------------------------------------ defined, used

;; Each procedural macro, by its name: its style, and its transformer as
;; text; the last defined first.
(define procedurals (ref (listof (tupleof symbol int string def-env) acyclic) rs) (new nil))
(define procedural-of (->* (symbol) (listof (tupleof int string def-env) acyclic))
  (lambda (n) (procedural-in n (get procedurals))))
(define procedural-in
  (->* (symbol (listof (tupleof symbol int string def-env) acyclic))
       (listof (tupleof int string def-env) acyclic))
  (lambda (n ps)
    (cond ((null? ps) nil)
          ((symbol=? n (extract (car ps) 1))
           (list (tuple (extract (car ps) 2) (extract (car ps) 3) (extract (car ps) 4))))
          (else (procedural-in n (cdr ps))))))
;; `(define-syntax name (STYLE proc))`, its parts: the name, the style and
;; the procedure, in a list of one; none if `form` is not one.
(define procedural-form (->* (syn) (listof (tupleof syn int syn) acyclic))
  (lambda (form)
    (tagcase form
      (lst (items d a b x)
        (if (and (= (len items) 3) (string=? (head-of items) "define-syntax"))
            (tagcase (car (cdr (cdr items)))
              (lst (parts d2 a2 b2 x2)
                (let ((s (style-named (head-of parts))))
                  (if (and (>= s 0) (= (length parts) 2))
                      (list (tuple (car (cdr items)) s (car (cdr parts))))
                      nil)))
              (else y nil))
            nil))
      (else y nil))))
;; `(define-syntax name (STYLE proc))`, `form`, defined, its transformer
;; checked; its name (`macros.fx`'s `define-macro`). As `defined` has it, a
;; procedural macro has no signature nor clauses, and makes `3`
;; (`macros-align.fx`'s `makes`); its transformer is `procedurals`'.
(define define-procedural (->* (fails syn def-env) (listof symbol acyclic))
  (lambda (fail form e)
    (let* ((p (car (procedural-form form))) (name (extract p 1)) (code (extract p 3))
           (text (syn-text code)))
      (cond
        ((or (not (syn-symbol? name)) (reserved? (syn-name name)))
         (begin (fail "a macro's name, not a form's" (syn-start name) (syn-end name)) nil))
        (else
         (tagcase (run (checked-text (extract p 2) text))
           (ok v
             (begin
               (set procedurals
                    (cons (tuple (syn-symbol name) (extract p 2) text e) (get procedurals)))
               (set defined
                    (cons (tuple (syn-symbol name)
                                 (the macro (tuple (s-expr) (the clauses nil) (the syns-a nil) 3)))
                          (get defined)))
               (list (syn-symbol name))))
           (failed why
             (begin (fail (string-append "`" (syn-name name) "`'s transformer: " why)
                          (syn-start code) (syn-end code))
                    nil))))))))
;; A use of procedural macro `name`, `s`, in expansion `made`: what its
;; transformer gave, at the use's place, its closures opened and its
;; keywords' aliases the keywords (`Macros::expand_procedural`).
(define expand-procedural (->* (fails symbol syn int) syn)
  (lambda (fail name s made)
    (let* ((p (car (procedural-of name))) (style (extract p 1))
           (a (syn-start s)) (b (syn-end s))
           (in-use (lambda ((m string))
                    (fail (string-append "a use of `" (symbol->string name) "`: " m) a b))))
      (tagcase (run (applied-text style (extract p 2) (syn-text s) made))
        (failed why (begin (in-use (string-append "its transformer: " why)) s))
        (ok out
          (let ((read (read-answer out (new-source-key a made) (new-source-key b made) made)))
            (if (null? read)
                (begin (in-use (string-append "its transformer gave `" out "`, not one form")) s)
                (let ((opened (cond ((= style 1) (closed fail (car read) #t made))
                                    ((= style 2) (closed fail (car read) #f made))
                                    (else (car read)))))
                  (keywords fail opened)))))))))

;;; ------------------------------------------------------------ definition environments

;; Where a macro defined now is defined: in a file's scope, if `file` has
;; one, as its importer has it; else where macros are now (`def-env-now`).
(define def-env-of-file (->* (scopes) def-env)
  (lambda (file)
    (if (null? file)
        (get def-env-now)
        (tuple 1 (extract (car file) 1) (extract (car file) 2)))))
(define def-env-now (ref def-env rs) (new (def-env-top)))
;; A module file's own macros' scope begun: none of these macros, nor any
;; procedural, defined, and macros defined where the file's items are; what
;; was, given back, for `file-scope-end!` (`Macros::in_file_scope`).
(define-type scope-saved (tupleof macro-env (listof (tupleof symbol int string def-env) acyclic)
                                  def-env))
(define file-scope-begin! (->* () scope-saved)
  (lambda ()
    (let ((saved (tuple (get defined) (get procedurals) (get def-env-now))))
      (begin (set defined nil) (set procedurals nil) (set def-env-now (tuple 2 'within nil))
             saved))))
(define file-scope-end! (->* (scope-saved) unit)
  (lambda (s)
    (begin (set defined (extract s 1)) (set procedurals (extract s 2))
           (set def-env-now (extract s 3)))))
;; Where the macro each expansion's aliases are of was defined, by the
;; expansion's number, the last first; a template's check is expansion 0
;; (`macros.rs`'s `Withs::def_envs`). Given to the resolution after expansion
;; (`macros-shapes.fx`'s `aliases-resolved`), which another instance of the
;; expander's files reads.
(define def-envs (ref def-envs rs) (new nil))
(define def-env! (->* (int def-env) unit)
  (lambda (k h) (set def-envs (cons (tuple k h) (get def-envs)))))
(define def-envs-given (->* () def-envs) (lambda () (get def-envs)))
