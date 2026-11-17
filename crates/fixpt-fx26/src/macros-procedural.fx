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
(define contracts-module ((proj (load-module "fx26:macros-contracts.fx") rs re rm rc rp)))
(define solve-module (with contracts-module solve-module))
(define infer-module (with solve-module infer-module))
(define files-module (with infer-module files-module))
(define align-module (with files-module align-module))
(define exports-module (with files-module exports-module))
(define match-module (with exports-module match-module))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define scopes-module (with exports-module scopes-module))
(define reader-types (with parser-module reader-types))
(define fresh-module (with contracts-module fresh-module))
(import fresh-module tag-of tag-char?)
(import reader-types atom lst dotted vec (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol syn-datums syn->datum
        syn-expansion len parse-tag p-ok p-err (type syns-a names presult))
(import types-module reserved? desc-word? type-form? kernel-sigs kernel-definitions s-expr s-defn
        marks (type fails sty marked))
(import align-module macro? defined def-env-top align node-syn node-kids nnodes makes pvar? split
        nth k-form nodes-reset! node-core node-hole env-empty env-levels lv-rib lv-earlier k-pvar
        k-binder k-ref program-walk
        (type macro clause clauses def-env def-envs macro-env scopes pvars levels found))
(import files-module signature-of)
(import contracts-module contract-renames renamed-use contract-held defined-held syn-same?
        made-syntax-reset! made-syntax-add! made-syntax-count made-syntax-taken! syntax-held
        (type renames))
(import types-module fail-at)
(import match-module same-atom?)
(import exports-module heads-checked)


;;; ------------------------------------------------------------ the programs

;; A style, by its form's name: 0 explicit renaming, 1 syntactic closures,
;; 2 reversed; -1 none.
(define style-named (->* (string) int)
  (lambda (n)
    (cond ((string=? n "er-macro-transformer") 0)
          ((string=? n "sc-macro-transformer") 1)
          ((string=? n "rsc-macro-transformer") 2)
          (else -1))))
;; The request that defines a transformer, `code`, where its macro is
;; defined: checked at its style's type and compiled, once, for its uses to
;; call (`procedural::define`, which the Rust expander calls itself).
(define checked-text (->* (int string (listof string acyclic)) string)
  (lambda (s code fs)
    (string-append "%define " (int->string s) " " (int->string (length fs)) "\n"
                   (forms-given fs) code)))
;; Phase-1 forms `fs`, each its length in characters on a line of its own
;; and its text, as a request gives them (`procedural::asked`).
(define forms-given (->* ((listof string acyclic)) string)
  (lambda (fs)
    (if (null? fs)
        ""
        (string-append (int->string (string-length (car fs))) "\n" (car fs)
                       (forms-given (cdr fs))))))
;; The request that checks phase-1 forms `fs`, in force from a
;; `begin-for-syntax` on.
(define forms-text (->* ((listof string acyclic)) string)
  (lambda (fs) (string-append "%forms " (int->string (length fs)) "\n" (forms-given fs))))
;; The request that runs one on `form` (as text), in expansion `made`, by its tag: the
;; transformer checked and compiled at its first use, then called
;; (`procedural::apply`, which the Rust expander calls itself).
(define applied-text (->* (int string string int (listof string acyclic)) string)
  (lambda (s code form made fs)
    (string-append "%apply " (int->string s) " " (tag-of made) " "
                   (int->string (string-length code)) " " (int->string (length fs)) "\n"
                   (forms-given fs) code form)))
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
;;; ------------------------------------------------------------ contracts

;; A use `s` of procedural macro `name`, in expansion `made`: expanded, and
;; held to its contract if it has one (`Macros::contract_expanded`;
;; `typed-macros.md`, "Decided: procedural macros checked by their
;; contracts"): the use aligned with it; then, unless
;; `FIXPT_MACRO_CONTRACTS=0`, the transformer run on it and on it with each
;; binder's name fresh throughout its scope, the second's fresh names where
;; their binders' scopes are (placement), and, named back, the first
;; (commutation). The first is the expansion. Of a contract that makes
;; definitions, the expansion is definitions, and defines of the use's names
;; exactly those it says (`defined-held`); a name it defines is a binder,
;; renamed as any other.
(define procedural-expanded (->* (fails symbol syn int) syn)
  (lambda (fail name s made)
    (let* ((shown (string-append "a use of `" (symbol->string name) "`: "))
           (in-use (lambda ((m string) (a int) (b int)) (fail (string-append shown m) a b)))
           (at-use (lambda ((m string) (a int) (b int))
                     (fail (string-append shown m) (syn-start s) (syn-end s))))
           (m (car (macro-of-defined name (get defined))))
           (sig (extract m 1))
           (defn (= (extract m 4) 1))
           (contract (extract (car (procedural-of name)) 4))
           (operands (nth (split s) 1)))
      (if (not contract)
          (expand-procedural fail name s made)
          (begin
            (nodes-reset!)
            (align in-use 2 (the pvars nil) sig operands -1 nil)
            (let ((out (expand-procedural fail name s made)))
              (if (= (get contracts) 0)
                  out
                  (let* ((held (if defn
                                   (begin (defined-held at-use sig operands out made)
                                          (nodes-reset!)
                                          (align in-use 2 (the pvars nil) sig operands -1 nil))
                                   0))
                         (r (contract-renames in-use sig operands)) (fresh (extract r 2)))
                    (if (null? fresh)
                        out
                        (let ((out2 (expand-procedural fail name
                                                       (renamed-use in-use s (extract r 1)) made)))
                          (begin (contract-held in-use s out out2 fresh made
                                                (if defn (s-defn) (s-expr)))
                                 out)))))))))))
(define macro-of-defined (->* (symbol macro-env) (listof macro acyclic))
  (lambda (n ms)
    (cond ((null? ms) nil)
          ((symbol=? n (extract (car ms) 1)) (list (extract (car ms) 2)))
          (else (macro-of-defined n (cdr ms))))))
;;; ------------------------------------------------------------ uses checked once

;; A template's checked uses (`Clause::checked_uses`), by where each starts:
;; each list its alignment (`template-actions`, just made) met as a use of a
;; macro, its operands aligned with that one's signature; and each use of
;; `name`, the macro being defined, whose operands fit its signature `sig`,
;; tried apart, the pattern's variables `ps` as theirs, so that no
;; definition is refused for one (`typed-macros.md`, "Decided: a use a
;; template made is not aligned again").
(define checked-uses (->* (symbol sty pvars) (listof int acyclic))
  (lambda (name sig ps) (append (get heads-checked) (checked-from 0 (get nnodes) name sig ps nil))))
(define checked-from (->* (int int symbol sty pvars (listof int acyclic)) (listof int acyclic))
  (lambda (i n name sig ps out)
    (if (= i n)
        out
        (let* ((s (node-syn i)) (parts (split s))
               (h (if (or (null? parts) (not (syn-symbol? (car parts)))
                          (pvar? (syn-symbol (car parts)) ps)
                          (tagcase (node-kids i) (k-form (x) #f) (else y #t)))
                      nil
                      (list (syn-symbol (car parts)))))
               (checked (and (not (null? h))
                             (if (macro? (car h))
                                 (or (= (makes (car h)) 0) (= (makes (car h)) 1))
                                 (and (symbol=? (car h) name)
                                      (fits-apart? sig (nth parts 1) ps))))))
          (checked-from (+ i 1) n name sig ps (if checked (cons (syn-start s) out) out))))))
(define fits-apart? (->* (sty syn pvars) bool)
  (lambda (sig operands ps)
    (tagcase (prompt parse-tag (begin (align pfail-apart 1 ps sig operands -1 nil) (p-ok nil))
                     (lambda ((r presult)) r))
      (p-err (why a b) #f)
      (else y #t))))
(define pfail-apart (->* (string int int) void)
  (lambda (message a b) (abort-current-continuation parse-tag (p-err message a b))))
;; Each key's part made at a template's checked use, by key, from
;; `source-base`: what it makes fits its macro's signature.
(define trusts (ref (arrayof bool rs) rs) (new (make-array 1024 #f)))
;; Key `a`, made for template place `ta` of clause `c` by expansion `made`:
;; trusted if `ta` is a checked use's.
(define trust-if! (->* (clause int int int) unit)
  (lambda (c ta a made)
    (if (and (> made 0) (int-in? ta (extract c 8)))
        (let ((i (- a source-base)))
          (begin
            (if (>= i (array-length (get trusts)))
                (let ((bigger (the (arrayof bool rs) (make-array (* 2 (+ i 1)) #f))))
                  (begin (copy-trusts (get trusts) bigger 0) (set trusts bigger)))
                #u)
            (array-set! (get trusts) i #t)))
        #u)))
(define copy-trusts (->* ((arrayof bool rs) (arrayof bool rs) int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i)) (copy-trusts from to (+ i 1))))))
(define int-in? (->* (int (listof int acyclic)) bool)
  (lambda (x xs) (and (not (null? xs)) (or (= x (car xs)) (int-in? x (cdr xs))))))
(define trusted-key? (->* (int) bool)
  (lambda (k)
    (let ((i (- k source-base)))
      (and (>= i 0) (< i (array-length (get trusts))) (array-ref (get trusts) i)))))
;; A use `s`'s operands aligned with its macro's signature `sig`, failing by
;; `in-use`; not where the use is trusted (`trusted-key?`), unless
;; `FIXPT_MACRO_RECHECK` asks, and then a refusal is the binding-shape
;; check's fault, said so.
(define use-aligned! (->* (fails syn sty syn) unit)
  (lambda (in-use s sig operands)
    (let ((trusted (trusted-key? (syn-start s))))
      (if (and trusted (= (get recheck) 0))
          #u
          (begin
            (align (if trusted
                       (lambda ((msg string) (a int) (b int))
                         (in-use (string-append msg " (a use a template made, which its macro's "
                                                "definition found fits: a fault in the "
                                                "binding-shape check, not in the program)")
                                 a b))
                       in-use)
                   2 (the pvars nil) sig operands -1 nil)
            #u)))))

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
;; (`%~T:x`, `T` its expansion's tag): every `%~T:` taken off; else "".
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
    (if (and (< i (string-length s)) (tag-char? (string-ref s i))) (digits-end s (+ i 1)) i)))
;; `n`'s alias, of expansion `made`, by its tag.
(define alias (->* (string int) string)
  (lambda (n made) (string-append "%~" (tag-of made) ":" n)))

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
;; description's word, a macro's definition's, a macro's
;; (`Macros::procedural_opened`'s).
(define keyword-name? (->* (fails string) bool)
  (lambda (fail n)
    (or (reserved? n) (desc-word? n #t) (type-form? n)
        (named? n (kernel-sigs fail)) (named? n (kernel-definitions fail))
        (string=? n "else") (string=? n "=>") (string=? n "quote") (string=? n "quasiquote")
        (string=? n "unquote") (string=? n "unquote-splicing")
        ;; A macro's definition's words (`transformer_word`).
        (string=? n "syntax-rules") (string=? n "trailmark") (>= (style-named n) 0)
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
;; And whether its signature is written, its contract
;; (`procedural::Procedural::contract`).
(define-type procedural (tupleof symbol int string def-env bool (listof string acyclic)))
(define procedurals (ref (listof procedural acyclic) rs) (new nil))
;; The phase-1 forms in force (`begin-for-syntax`'s texts, in order), each
;; transformer defined now running where they are (`phase1.rs`): its own,
;; the sixth of its `procedural`.
(define phase1-forms (ref (listof string acyclic) rs) (new nil))
(define phase1-forms-now (->* () (listof string acyclic)) (lambda () (get phase1-forms)))
(define phase1-forms! (->* ((listof string acyclic)) unit) (lambda (fs) (set phase1-forms fs)))
;; Both, as a session's state after a form keeps them (`by-state`): a state
;; read again has its own transformers, not a later form's of their names.
(define-type phase1-state (tupleof (listof string acyclic) (listof procedural acyclic)))
(define phase1-state-now (->* () phase1-state)
  (lambda () (tuple (get phase1-forms) (get procedurals))))
(define phase1-state! (->* (phase1-state) unit)
  (lambda (s) (begin (set phase1-forms (extract s 1)) (set procedurals (extract s 2)))))
(define phase1-none? (->* () bool)
  (lambda () (and (null? (get phase1-forms)) (null? (get procedurals)))))
;; `(begin-for-syntax form …)`, `s`: its forms in force from now on, checked,
;; compiled and run in their namespace now, so that one refused is refused
;; here, as the Rust expander refuses it (`Macros::for_syntax`).
(define for-syntax! (->* (fails syn) unit)
  (lambda (fail s)
    (let ((fs (append (get phase1-forms)
                      (syns-texts (tagcase s (lst (items d a b x) (cdr items)) (else y nil))))))
      (tagcase (run (forms-text fs))
        (ok v (set phase1-forms fs))
        (failed why
          (fail (string-append "`begin-for-syntax`: " why) (syn-start s) (syn-end s)))))))
(define syns-texts (->* (syns-a) (listof string acyclic))
  (lambda (xs) (if (null? xs) nil (cons (syn-text (car xs)) (syns-texts (cdr xs))))))
(define procedural-of
  (->* (symbol) (listof (tupleof int string def-env bool (listof string acyclic)) acyclic))
  (lambda (n)
    ;; Only while `defined` has it so (it, not `procedurals`, is what a
    ;; state saves and gives back, `macros-at!`): one that makes `3`, or one
    ;; of a contract, which has no clauses; a `syntax-rules` macro since
    ;; defined of the name is not one.
    (let ((m (macro-of-defined n (get defined))))
      (if (and (not (null? m)) (or (= (extract (car m) 4) 3) (null? (extract (car m) 2))))
          (procedural-in n (get procedurals))
          nil))))
(define procedural-in
  (->* (symbol (listof procedural acyclic))
       (listof (tupleof int string def-env bool (listof string acyclic)) acyclic))
  (lambda (n ps)
    (cond ((null? ps) nil)
          ((symbol=? n (extract (car ps) 1))
           (list (tuple (extract (car ps) 2) (extract (car ps) 3) (extract (car ps) 4)
                        (extract (car ps) 5) (extract (car ps) 6))))
          (else (procedural-in n (cdr ps))))))
;; `(define-syntax name [σ] (STYLE proc))`, its parts: the name, the style,
;; the procedure, and its contract if written; in a list of one; none if
;; `form` is not one.
(define procedural-form (->* (syn) (listof (tupleof syn int syn syns-a) acyclic))
  (lambda (form)
    (tagcase form
      (lst (items d a b x)
        (if (and (or (= (len items) 3) (= (len items) 4))
                 (string=? (head-of items) "define-syntax"))
            (let ((t (if (= (len items) 4) (nth items 3) (nth items 2)))
                  (sig (if (= (len items) 4) (list (nth items 2)) nil)))
              (tagcase t
                (lst (parts d2 a2 b2 x2)
                  (let ((s (style-named (head-of parts))))
                    (if (and (>= s 0) (= (length parts) 2))
                        (list (tuple (car (cdr items)) s (car (cdr parts)) sig))
                        nil)))
                (else y nil)))
            nil))
      (else y nil))))
;; `(define-syntax name (STYLE proc))`, `form`, defined, its transformer
;; checked; its name (`macros.fx`'s `define-macro`). As `defined` has it, a
;; procedural macro has no signature nor clauses, and makes `3`
;; (`macros-align.fx`'s `makes`); its transformer is `procedurals`'.
(define define-procedural (->* (fails syn def-env) (listof symbol acyclic))
  (lambda (fail form e)
    (let* ((p (car (procedural-form form))) (name (extract p 1)) (code (extract p 3))
           (text (syn-text code))
           ;; Its contract: an expression's or definitions', of untyped parts, yet.
           (signed (if (null? (extract p 4)) nil (list (signature-of fail (car (extract p 4))))))
           (sig (if (null? signed) (s-expr) (extract (car signed) 2))))
      (cond
        ((or (not (syn-symbol? name)) (reserved? (syn-name name)))
         (begin (fail "a macro's name, not a form's" (syn-start name) (syn-end name)) nil))
        ((and (not (null? signed))
              (or (not (null? (extract (car signed) 1))) (= (extract (car signed) 3) 2)))
         (begin (fail-at fail (string-append "`" (syn-name name) "`'s contract: a procedural "
                                             "macro's is an expression's or definitions', of "
                                             "untyped parts, not yet another")
                         (car (extract p 4)))
                nil))
        (else
         (tagcase (run (checked-text (extract p 2) text (get phase1-forms)))
           (ok v
             (begin
               (set procedurals
                    (cons (tuple (syn-symbol name) (extract p 2) text e (not (null? signed))
                                 (get phase1-forms))
                          (get procedurals)))
               ;; With a contract, a macro by its signature (an expression's or definitions'),
               ;; which a template's alignment takes as a `syntax-rules`
               ;; one's; with none, one that makes `3`, whose binding
               ;; structure nothing says.
               (set defined
                    (cons (tuple (syn-symbol name)
                                 (the macro (tuple sig (the clauses nil) (the syns-a nil)
                                                   (if (null? signed) 3 (extract (car signed) 3)))))
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
                    (fail (string-append "a use of `" (symbol->string name) "`: " m) a b)))
           (opened (lambda ((at syn))
                     (keywords fail (cond ((= style 1) (closed fail at #t made))
                                          ((= style 2) (closed fail at #f made))
                                          (else at))))))
      ;; In the expansion's phase-1 namespace, on the use's datum, the one
      ;; the Rust expander calls it in (`phase1.rs`): what it gives made
      ;; syntax at the use's place, no text between; apart, by text, where
      ;; the runtime has none.
      (tagcase (%macros:call-procedural style (extract p 2) (syn->datum s) (tag-of made)
                                        (extract p 5))
        (ok d (opened (syn-of-datum d (new-source-key a made) (new-source-key b made) made)))
        (failed why (begin (in-use (string-append "its transformer: " why)) s))
        (apart u
          (tagcase (run (applied-text style (extract p 2) (syn-text s) made (extract p 5)))
            (failed why (begin (in-use (string-append "its transformer: " why)) s))
            (ok out
              (let ((read (read-answer out (new-source-key a made) (new-source-key b made) made)))
                (if (null? read)
                    (begin (in-use (string-append "its transformer gave `" out "`, not one form"))
                           s)
                    (opened (car read)))))))))))
;; Datum `d` as syntax, each part at `a`..`b` of expansion `x`: what
;; `read-answer` of its text makes, with no text between (`heap_syn`'s
;; `syn_of_datum`, the Rust expander's).
(define syn-of-datum (->* (datum int int int) syn)
  (lambda (d a b x)
    (cond ((vector? d)
           (vec (syns-of-datum (datum-vector->list d) a b x) d a b x))
          ((pair? d) (syn-of-list d nil a b x))
          ((null? d) (lst nil d a b x))
          (else (atom d a b x)))))
(define syn-of-list (->* (datum syns-a int int int) syn)
  (lambda (whole out a b x) (syn-of-rest whole whole out a b x)))
;; The list `whole`, its parts before `l` made, newest first, `out`.
(define syn-of-rest (->* (datum datum syns-a int int int) syn)
  (lambda (whole l out a b x)
    (if (pair? l)
        (syn-of-rest whole (cdr l) (cons (syn-of-datum (car l) a b x) out) a b x)
        (if (null? l)
            (lst (reverse out) whole a b x)
            (dotted (reverse out) (syn-of-datum l a b x) whole a b x)))))
(define syns-of-datum (->* (datum int int int) syns-a)
  (lambda (l a b x)
    (if (pair? l) (cons (syn-of-datum (car l) a b x) (syns-of-datum (cdr l) a b x)) nil)))

;;; ------------------------------------------------------------ definition environments

;; Where a macro defined now is defined: in a file's scope, if `file` has
;; one, as its importer has it; else where macros are now (`def-env-now`).
(define def-env-of-file (->* (scopes) def-env)
  (lambda (file)
    (if (null? file)
        (get def-env-now)
        (tuple (if (= (extract (get def-env-now) 1) 3) 3 1) (extract (car file) 1)
               (extract (car file) 2)))))
(define def-env-now (ref def-env rs) (new (def-env-top)))
(define def-env-is (->* () def-env) (lambda () (get def-env-now)))
(define def-env-now! (->* (def-env) unit) (lambda (h) (set def-env-now h)))
;; A module file's own macros' scope begun: none of these macros, nor any
;; procedural, defined, and macros defined where the file's items are; what
;; was, given back, for `file-scope-end!` (`Macros::in_file_scope`).
(define-type scope-saved
  (tupleof macro-env (listof procedural acyclic) def-env marked (listof string acyclic)))
(define file-scope-begin! (->* () scope-saved)
  (lambda ()
    (let ((saved (tuple (get defined) (get procedurals) (get def-env-now) (get marks)
                        (get phase1-forms))))
      (begin (set defined nil) (set procedurals nil) (set def-env-now (tuple 2 'within nil))
             (set phase1-forms nil)
             (set marks nil)
             saved))))
(define file-scope-end! (->* (scope-saved) unit)
  (lambda (s)
    (begin (set defined (extract s 1)) (set procedurals (extract s 2))
           (set def-env-now (extract s 3)) (set marks (extract s 4))
           (set phase1-forms (extract s 5)))))
;; Where the macro each expansion's aliases are of was defined, by the
;; expansion's tag (`tag-of`), the last first; a template's check's is `0`
;; (`macros.rs`'s `Withs::def_envs`). Given to the resolution after expansion
;; (`macros-shapes.fx`'s `aliases-resolved`), which another instance of the
;; expander's files reads.
(define def-envs (ref def-envs rs) (new nil))
(define def-env! (->* (int def-env) unit)
  (lambda (k h) (set def-envs (cons (tuple (tag-of k) h) (get def-envs)))))
(define def-envs-given (->* () def-envs) (lambda () (get def-envs)))
;; `s`, each part at `a`..`b` of expansion `x`: a hole's call, where the
;; template has the hole.
(define respanned (->* (syn int int int) syn)
  (lambda (s a b x)
    (tagcase s
      (lst (items d c e y) (lst (respanned-each items a b x) d a b x))
      (dotted (items tail d c e y)
        (dotted (respanned-each items a b x) (respanned tail a b x) d a b x))
      (vec (items d c e y) (vec (respanned-each items a b x) d a b x))
      (atom (d c e y) (atom d a b x)))))
(define respanned-each (->* (syns-a int int int) syns-a)
  (lambda (xs a b x)
    (if (null? xs) nil (cons (respanned (car xs) a b x) (respanned-each (cdr xs) a b x)))))
;; `s`, each part of it at a key of its own for its place, in expansion
;; `made`.
(define in-expansion (->* (syn int) syn)
  (lambda (s made)
    (let ((a (source-key (syn-start s) made)))
      (tagcase s
        (lst (items d c e x)
          (let* ((xs (each-in items made)) (b (source-key e made))) (lst xs d a b made)))
        (dotted (items tail d c e x)
          (let* ((xs (each-in items made)) (tl (in-expansion tail made)) (b (source-key e made)))
            (dotted xs tl d a b made)))
        (vec (items d c e x)
          (let* ((xs (each-in items made)) (b (source-key e made))) (vec xs d a b made)))
        (atom (d c e x) (atom d a (source-key e made) made))))))
(define each-in (->* (syns-a int) syns-a)
  (lambda (xs made)
    (if (null? xs) nil (cons (in-expansion (car xs) made) (each-in (cdr xs) made)))))

;;; ------------------------------------------------------------ expansions that do not end

;; The uses of macros the expansion is inside, the innermost first: each
;; its macro, its form, and how many parts the form has, -1 if it was not
;; counted; and how many there are (`macros.rs`'s `Withs::chain`).
(define-type link (tupleof symbol syn int))
(define chain (ref (listof link acyclic) rs) (new nil))
(define chain-depth (ref int rs) (new 0))
;; The uses one form's expansion may expand, and how deep, each in the
;; expansion of the one before (`macros.rs`'s `limits`).
;; The limits of one form's expansion, read as it begins (`macros.rs`'s
;; `limits`): 10000 and 1000, or as `FIXPT_MACRO_USES` and
;; `FIXPT_MACRO_DEPTH` set them.
(define max-uses (ref int rs) (new 10000))
(define max-depth (ref int rs) (new 1000))
;; Whether a use a template made is aligned again, 1, or not, 0
;; (`FIXPT_MACRO_RECHECK`; `use-aligned!`); whether a procedural macro's
;; expansions are held to its contract (`FIXPT_MACRO_CONTRACTS`).
(define recheck (ref int rs) (new 0))
(define contracts (ref int rs) (new 1))
;; Limit `name`, `USES` or `DEPTH`, as the runtime reads it; -1 where the
;; value set is none, said at `s`.
(define limit-of (->* (fails syn string) int)
  (lambda (fail s name)
    (let* ((a (%macros:limit name)) (rest (substring a 1 (string-length a))))
      (if (char=? (string-ref a 0) #\=)
          (parse-nat rest 10)
          (begin (fail-at fail rest s) -1)))))
;; One form's expansion begun, at `s`: its chain empty, its limits read.
;; The uses it may expand, or -1 where a limit set is none.
(define chain-begun! (->* (fails syn) int)
  (lambda (fail s)
    (let* ((u (limit-of fail s "USES")) (d (if (< u 0) -1 (limit-of fail s "DEPTH")))
           (r (if (< d 0) -1 (limit-of fail s "RECHECK")))
           (c (if (< r 0) -1 (limit-of fail s "CONTRACTS"))))
      (begin (set chain nil) (set chain-depth 0)
             (set max-uses u) (set max-depth d) (set recheck r) (set contracts c)
             (if (< c 0) -1 u)))))
(define use-left! (->* () unit)
  (lambda () (begin (set chain (cdr (get chain))) (set chain-depth (- (get chain-depth) 1)))))
;; A use of `n`, `s`, about to be expanded, `fuel` uses left: entered in the
;; chain; or refused where a limit is reached, the fuel spent or the depth,
;; saying why (`limit-failed`). Nothing more is looked at here
;; (`Macros::enter`, `TODO.md` §231). Whether it is entered.
(define use-entered? (->* (fails symbol syn int) bool)
  (lambda (fail n s fuel)
    (let ((ls (get chain)) (shown (string-append "`" (symbol->string n) "`")))
      (cond
        ((= fuel 0)
         (limit-failed fail n s ls (string-append "this macro's expansion does not end: "
                                                  (int->string (get max-uses))
                                                  " uses expanded in one form, the last of "
                                                  shown (inside-said ls 4 ""))))
        ((= (get chain-depth) (get max-depth))
         (limit-failed fail n s ls
                       (string-append "this macro's expansion does not end: its uses are "
                                      (int->string (get max-depth)) " deep, each in the "
                                      "expansion of the one before, the last of " shown
                                      (inside-said ls 4 ""))))
        (else
         (begin (set chain (cons (tuple n s -1) ls))
                (set chain-depth (+ (get chain-depth) 1))
                #t))))))
;; A limit reached at use `s` of `n`, inside `ls`: `why`, unless the chain
;; says better, its outermost use that is, part by part, one of the same
;; macro it is inside: "this use of `m` is one it was expanded from,
;; unchanged[, through …]", at that use (`Macros::limit_error`). #f.
(define limit-failed (->* (fails symbol syn (listof link acyclic) string) bool)
  (lambda (fail n s ls why)
    (let ((r (first-repeat (sized (cons (tuple n s -1) ls)))))
      (begin
        (if (null? r)
            (fail-at fail why s)
            (fail-at fail (string-append "this use of `" (symbol->string (extract (car r) 2))
                                         "` is one it was expanded from, unchanged"
                                         (through-said (extract (car r) 3))
                                         ": its expansion would never end")
                     (extract (car r) 1)))
        #f))))
;; `ls` (innermost first), each use's parts counted once where a use of its
;; macro is around it, -1 where none is.
(define sized (->* ((listof link acyclic)) (listof link acyclic))
  (lambda (ls)
    (if (null? ls)
        nil
        (let ((n (extract (car ls) 1)) (s (extract (car ls) 2)))
          (cons (tuple n s (if (link-of? n (cdr ls)) (syn-size s) -1)) (sized (cdr ls)))))))
;; The outermost use of `ls` (innermost first, each sized) that is one of
;; those around it: it, its macro and the macros passed, in a list of one.
(define first-repeat (->* ((listof link acyclic)) (listof (tupleof syn symbol names) acyclic))
  (lambda (ls)
    (if (null? ls)
        nil
        (let ((outer (first-repeat (cdr ls))))
          (if (not (null? outer))
              outer
              (let* ((n (extract (car ls) 1)) (s (extract (car ls) 2)) (size (extract (car ls) 3))
                     (back (if (< size 0) nil (came-back n s size (cdr ls) nil))))
                (if (null? back) nil (list (tuple s n (car back))))))))))
(define link-of? (->* (symbol (listof link acyclic)) bool)
  (lambda (n ls)
    (and (not (null? ls)) (or (symbol=? n (extract (car ls) 1)) (link-of? n (cdr ls))))))
;; The macros of the uses inside the one in `ls` that `s` is, of `n` and
;; `size` parts, innermost first, in a list of one; none if it is none.
(define came-back
  (->* (symbol syn int (listof link acyclic) names) (listof names acyclic))
  (lambda (n s size ls passed)
    (cond ((null? ls) nil)
          ((and (symbol=? n (extract (car ls) 1))
                (= size (if (< (extract (car ls) 3) 0) (syn-size (extract (car ls) 2))
                            (extract (car ls) 3)))
                (syn-same? (extract (car ls) 2) s))
           (list passed))
          (else (came-back n s size (cdr ls) (cons (extract (car ls) 1) passed))))))
;; `, through `a`, `b``: the macros passed, outermost first, each once.
(define through-said (->* (names) string)
  (lambda (ns)
    (if (null? ns) "" (string-append ", through " (names-said (reverse (each-once ns nil)))))))
(define each-once (->* (names names) names)
  (lambda (ns seen)
    (cond ((null? ns) seen)
          ((name-seen? (car ns) seen) (each-once (cdr ns) seen))
          (else (each-once (cdr ns) (cons (car ns) seen))))))
(define name-seen? (->* (symbol names) bool)
  (lambda (n ns) (and (not (null? ns)) (or (symbol=? n (car ns)) (name-seen? n (cdr ns))))))
(define names-said (->* (names) string)
  (lambda (ns)
    (if (null? (cdr ns))
        (string-append "`" (symbol->string (car ns)) "`")
        (string-append "`" (symbol->string (car ns)) "`, " (names-said (cdr ns))))))
;; `, inside `a`, `b``: the macros of the `k` innermost uses of `ls`.
(define inside-said (->* ((listof link acyclic) int string) string)
  (lambda (ls k out)
    (if (or (null? ls) (= k 0))
        out
        (inside-said (cdr ls) (- k 1)
                     (string-append out (if (string=? out "") ", inside " ", ") "`"
                                    (symbol->string (extract (car ls) 1)) "`")))))
;; How many parts syntax `s` has, each list, pair's tail and atom one.
(define syn-size (->* (syn) int)
  (lambda (s)
    (tagcase s
      (lst (items d a b x) (+ 1 (sizes items)))
      (dotted (items tail d a b x) (+ 1 (+ (sizes items) (syn-size tail))))
      (else y 1))))
(define sizes (->* (syns-a) int)
  (lambda (xs) (if (null? xs) 0 (+ (syn-size (car xs)) (sizes (cdr xs))))))
