;;; Typed hygienic macros, in FX-26: what the expander (`macros.fx`) reads
;;; of the files whose macros `import-with-syntax` brings, and of the forms
;;; ahead, that holds no state of its own: a file's macros and the names
;;; its module shows (`Checker::import_file_macros`, `names_shown`), the
;;; load definitions, `only` and `except`, and where a later form makes a
;;; name a macro (`Macros::defined_before`). Loaded by `macros.fx`, which
;;; takes `exports-module` and `align-module`, this file's instances of
;;; `macros-exports.fx` and `macros-align.fx`, from it, so that the
;;; expander's parts are one.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define facts-module ((proj (load-module "fx26:macros-facts.fx") rs re rm rc rp)))
(define exports-module (with facts-module exports-module))
(import facts-module contract? elaborated)
(define align-module (with exports-module align-module))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol len nth datatype?
        mk-list mk-symbol expand-datatype syn-string? (type syns-a names loaded-file)
        (effect parses))
(import types-module fail-at split syn-nil? reserved? reserved-syn? read-sty kind-of syn-keyword?
        keyword-name show-syn marks mark-count no-trailmark proper-items s-export bind-rib
        path-usage syntax-sig-of (type fails sty entries))
(import align-module nnodes node-syn node-core node-kids k-pvar defined mark-now syntax-read!
        syntax-sig-read (type clauses macro-env))

;; The name the importer has macro `n` by, of `m`'s, in a list of one.
(define internal-of
  (->* (symbol (listof (tupleof symbol symbol) acyclic)) (listof symbol acyclic))
  (lambda (n m)
    (cond ((null? m) nil)
          ((symbol=? n (extract (car m) 1)) (list (extract (car m) 2)))
          (else (internal-of n (cdr m))))))
(define proper (->* (syn) syns-a)
  (lambda (s) (tagcase s (lst (items d a b x) items) (else y nil))))
(define name-in? (->* (symbol names) bool)
  (lambda (n ns) (and (not (null? ns)) (or (symbol=? n (car ns)) (name-in? n (cdr ns))))))
;; Whether `s` is a `define-syntax` or a `define-syntax-rec`.
(define defines-syntax? (->* (syn) bool)
  (lambda (s)
    (let ((items (proper s)))
      (and (not (null? items)) (syn-symbol? (car items))
           (or (string=? (syn-name (car items)) "define-syntax")
               (string=? (syn-name (car items)) "define-syntax-rec"))))))
;; Whether `s` is a `begin-for-syntax`, phase 1's forms (`macros-procedural.fx`).
(define for-syntax? (->* (syn) bool)
  (lambda (s)
    (let ((items (proper s)))
      (and (not (null? items)) (syn-symbol? (car items))
           (string=? (syn-name (car items)) "begin-for-syntax")))))
;; The macros `s`, a `define-syntax` or a `define-syntax-rec`, defines.
(define syntax-names (->* (syn) names)
  (lambda (s)
    (let ((items (proper s)))
      (cond ((not (defines-syntax? s)) nil)
            ((string=? (syn-name (car items)) "define-syntax")
             (if (and (> (len items) 1) (syn-symbol? (nth items 1)))
                 (list (syn-symbol (nth items 1)))
                 nil))
            (else (member-names (cdr items)))))))
(define member-names (->* (syns-a) names)
  (lambda (ms)
    (cond ((null? ms) nil)
          ((and (not (null? (proper (car ms)))) (syn-symbol? (car (proper (car ms)))))
           (cons (syn-symbol (car (proper (car ms)))) (member-names (cdr ms))))
          (else (member-names (cdr ms))))))
;; Each top-level `(define name (load-module "path"))` so far, the last
;; first: the files `import-with-syntax` of `name` reads.
(define-type load-defs (listof (tupleof symbol string) acyclic))
;; `withs`: the places of the `with` forms whose bodies `s` is in.
(define-type places (listof (tupleof int int) acyclic))
(define-type files (listof loaded-file acyclic))
(define-type mades (listof (tupleof symbol bool) acyclic))
;; The name at the head of list `s`; "" if none.
(define head-name (->* (syn) string)
  (lambda (s)
    (let ((items (proper s)))
      (if (and (not (null? items)) (syn-symbol? (car items))) (syn-name (car items)) ""))))
;; `(load-module "path")`'s path, in a list of one.
(define load-path (->* (syn) (listof string acyclic))
  (lambda (s)
    (let ((items (proper s)))
      (if (and (= (len items) 2) (syn-symbol? (car items))
               (string=? (syn-name (car items)) "load-module"))
          (tagcase (nth items 1) (atom (d a b x) (if (string? d) (list d) nil)) (else y nil))
          nil))))
;; An instance's, `((proj (load-module "path") arg …))`, in a list of one
;; (`binding-shapes.md`, step 4 (c); `Checker::load_def_of`).
(define instance-path (->* (syn) (listof string acyclic))
  (lambda (s)
    (let* ((items (proper s)) (applied (if (= (len items) 1) (proper (car items)) nil)))
      (if (and (>= (len applied) 2) (syn-symbol? (car applied))
               (string=? (syn-name (car applied)) "proj"))
          (load-path (nth applied 1))
          nil))))
;; A load's or an instance's path, in a list of one.
(define def-path (->* (syn) (listof string acyclic))
  (lambda (s) (let ((p (load-path s))) (if (null? p) (instance-path s) p))))
(define without-load (->* (symbol load-defs) load-defs)
  (lambda (n ls)
    (cond ((null? ls) nil)
          ((symbol=? n (extract (car ls) 1)) (without-load n (cdr ls)))
          (else (cons (car ls) (without-load n (cdr ls)))))))
(define load-of (->* (symbol load-defs) (listof string acyclic))
  (lambda (n ls)
    (cond ((null? ls) nil)
          ((symbol=? n (extract (car ls) 1)) (list (extract (car ls) 2)))
          (else (load-of n (cdr ls))))))
;; Whether `s` is an `import-with-syntax`.
(define imports-syntax? (->* (syn) bool)
  (lambda (s)
    (let ((items (proper s)))
      (and (not (null? items)) (syn-symbol? (car items))
           (string=? (syn-name (car items)) "import-with-syntax")))))
(define import-usage string
  (string-append "`(import-with-syntax name)`, the name a module loaded by `load-module`, or "
                 "`(import-with-syntax name (only name …))` or `(except name …)`"))
;; `(only name …)` or `(except name …)`: whether `only`, and the names, in a
;; list of one; none if there is none.
(define-type filter (tupleof bool syns-a))
(define name-filter (->* (fails syn) filter)
  (lambda (fail f)
    (let* ((items (proper f)) (head (if (and (not (null? items)) (syn-symbol? (car items)))
                                       (syn-name (car items))
                                       "")))
      (if (or (string=? head "only") (string=? head "except"))
          (begin (all-names fail (cdr items)) (tuple (string=? head "only") (cdr items)))
          (begin (fail-at fail import-usage f) (tuple #t (the syns-a nil)))))))
(define all-names (->* (fails syns-a) unit)
  (lambda (fail xs)
    (cond ((null? xs) #u)
          ((syn-symbol? (car xs)) (all-names fail (cdr xs)))
          (else (fail-at fail import-usage (car xs))))))
(define listed? (->* (symbol syns-a) bool)
  (lambda (n xs)
    (and (not (null? xs)) (or (symbol=? n (syn-symbol (car xs))) (listed? n (cdr xs))))))
(define not-macros (->* (syns-a names) syns-a)
  (lambda (xs ms)
    (cond ((null? xs) nil)
          ((name-in? (syn-symbol (car xs)) ms) (not-macros (cdr xs) ms))
          (else (cons (car xs) (not-macros (cdr xs) ms))))))
;; The file read from `path`, in a list of one.
(define loaded-path (->* (string files) files)
  (lambda (path fs)
    (cond ((null? fs) nil)
          ((and (string=? (extract (car fs) 4) path) (> (extract (car fs) 2) 0))
           (the files (list (car fs))))
          (else (loaded-path path (cdr fs))))))
;; A file's macros, each with whether it is hidden, in order; and its
;; `begin-for-syntax`es among them, in force for the macros after each.
(define-type file-macro (tupleof syn bool))
(define file-syntax (->* (syns-a) (listof file-macro acyclic))
  (lambda (forms)
    (cond ((null? forms) nil)
          ((or (defines-syntax? (car forms)) (for-syntax? (car forms)))
           (cons (tuple (car forms) #f) (file-syntax (cdr forms))))
          ((hide-form? (car forms))
           (append (hidden-syntax (cdr (proper (car forms)))) (file-syntax (cdr forms))))
          (else (file-syntax (cdr forms))))))
(define hidden-syntax (->* (syns-a) (listof file-macro acyclic))
  (lambda (xs)
    (cond ((null? xs) nil)
          ((defines-syntax? (car xs)) (cons (tuple (car xs) #t) (hidden-syntax (cdr xs))))
          (else (hidden-syntax (cdr xs))))))
(define hide-form? (->* (syn) bool)
  (lambda (s)
    (let ((items (proper s)))
      (string=? (head-name s) "hide"))))
;; The file's forms its module shows: neither macros nor hidden.
(define file-items (->* (syns-a) syns-a)
  (lambda (forms)
    (cond ((null? forms) nil)
          ((or (defines-syntax? (car forms)) (for-syntax? (car forms)) (hide-form? (car forms)))
           (file-items (cdr forms)))
          ((datatype? (car forms))
           (append (expand-datatype (car forms)) (file-items (cdr forms))))
          (else (cons (car forms) (file-items (cdr forms)))))))
;; The values and the types and effects `forms` define, onto `vs` and `ts`:
;; what the module shows. An `include`'s are known only once it is
;; checked: none (`Checker::names_shown`).
(define names-shown (->* (syns-a names names) (tupleof names names))
  (lambda (forms vs ts)
    (if (null? forms)
        (tuple vs ts)
        (let* ((items (proper (car forms)))
               (head (head-name (car forms)))
               (named (if (< (len items) 2) nil (defined-name (nth items 1)))))
          (cond
            ((or (string=? head "define") (string=? head "define*"))
             (names-shown (cdr forms) (append named vs) ts))
            ((string=? head "define-rec")
             (names-shown (cdr forms) (append (rec-names (cdr items)) vs) ts))
            ((string=? head "define-generative")
             (names-shown (cdr forms) (append (generative-values named (drop-n items 3)) vs)
                          (append named ts)))
            ((or (string=? head "define-type") (string=? head "define-effect"))
             (names-shown (cdr forms) vs (append named ts)))
            (else (names-shown (cdr forms) vs ts)))))))
;; A definition's name: `name`, or `(name …)`'s.
(define defined-name (->* (syn) names)
  (lambda (s)
    (cond ((syn-symbol? s) (list (syn-symbol s)))
          ((and (not (null? (proper s))) (syn-symbol? (car (proper s))))
           (list (syn-symbol (car (proper s)))))
          (else nil))))
;; A module file's frame (`Checker::frame_text`, `TODO.md` §300), of its
;; forms `forms`: the last of them, if it is one, `(define %frame:F (let
;; (…) (module (define x %fr:x) …)))`, as its name and the values it
;; holds; else `'-` and none.
(define frame-of (->* (syns-a) (tupleof symbol names names))
  (lambda (forms)
    (cond ((null? forms) (tuple '- (the names nil) (the names nil)))
          ((not (null? (cdr forms))) (frame-of (cdr forms)))
          (else
           (let* ((items (proper (car forms)))
                  (named (if (< (len items) 3) nil (defined-name (nth items 1))))
                  (s (if (null? named) "" (symbol->string (car named)))))
             (if (and (string=? (head-name (car forms)) "define") (> (string-length s) 7)
                      (string=? (substring s 0 7) "%frame:"))
                 (let ((inner (proper (nth items 2))))
                   (if (< (len inner) 3)
                       (tuple (car named) (the names nil) (the names nil))
                       (tuple (car named) (frame-held (proper (nth inner 2)) "define")
                              (frame-descs (proper (nth inner 2))))))
                 (tuple '- (the names nil) (the names nil))))))))
;; The values `(module (define x …) …)`, `xs`'s, defines.
(define frame-held (->* (syns-a string) names)
  (lambda (xs head)
    (cond ((null? xs) nil)
          ((string=? (head-name (car xs)) head)
           (let ((items (proper (car xs))))
             (append (if (< (len items) 2) nil (defined-name (nth items 1)))
                     (frame-held (cdr xs) head))))
          (else (frame-held (cdr xs) head)))))
;; The descriptions the frame's module items `xs` alias, each by its own
;; name: `(define-type %ft:t t)`'s `t`, `(define-effect (%ft:e …) …)`'s `e`.
(define frame-descs (->* (syns-a) names)
  (lambda (xs)
    (unaliased (append (frame-held xs "define-type") (frame-held xs "define-effect")))))
(define unaliased (->* (names) names)
  (lambda (ns)
    (if (null? ns)
        nil
        (let ((s (symbol->string (car ns))))
          (if (and (> (string-length s) 4) (string=? (substring s 0 4) "%ft:"))
              (cons (string->symbol (substring s 4 (string-length s))) (unaliased (cdr ns)))
              (unaliased (cdr ns)))))))
(define rec-names (->* (syns-a) names)
  (lambda (bs)
    (cond ((null? bs) nil)
          ((and (not (null? (proper (car bs)))) (syn-symbol? (car (proper (car bs)))))
           (cons (syn-symbol (car (proper (car bs)))) (rec-names (cdr bs))))
          (else (rec-names (cdr bs))))))
;; A generative type's conversions: the names `rest`, its form's parts
;; after its type, give (`#:seal mk #:unseal get`; the parser's
;; `generative-conversions` says what is wrong with them).
(define generative-values (->* (names syns-a) names)
  (lambda (ns rest) (if (null? ns) nil (given-conversions rest))))
(define given-conversions (->* (syns-a) names)
  (lambda (rest)
    (if (or (null? rest) (null? (cdr rest)))
        nil
        (let ((more (given-conversions (cdr (cdr rest)))))
          (if (syn-symbol? (car (cdr rest))) (cons (syn-symbol (car (cdr rest))) more) more)))))
(define drop-n (->* (syns-a int) syns-a)
  (lambda (xs k) (if (or (= k 0) (null? xs)) xs (drop-n (cdr xs) (- k 1)))))
(define macro-names (->* ((listof file-macro acyclic)) names)
  (lambda (ms)
    (if (null? ms)
        nil
        (append (syntax-names (extract (car ms) 1)) (macro-names (cdr ms))))))
;; Each macro's name the importer has it by, which no program writes.
(define internal-names (->* (string names) (listof (tupleof symbol symbol) acyclic))
  (lambda (key ns)
    (if (null? ns)
        nil
        (cons (tuple (car ns) (string->symbol (string-append "%syntax:" key ":"
                                                             (symbol->string (car ns)))))
              (internal-names key (cdr ns))))))
(define taken? (->* (symbol (listof filter acyclic)) bool)
  (lambda (n filter)
    (or (null? filter)
        (if (extract (car filter) 1)
            (listed? n (extract (car filter) 2))
            (not (listed? n (extract (car filter) 2)))))))
(define shown-names (->* (mades) names)
  (lambda (made)
    (cond ((null? made) nil)
          ((extract (car made) 2) (shown-names (cdr made)))
          (else (cons (extract (car made) 1) (shown-names (cdr made)))))))
(define macro-sites (->* (symbol syns-a files load-defs places) places)
  (lambda (n xs fs ls found)
    (if (null? xs)
        found
        (let* ((x (car xs))
               (here (cond ((defines-syntax? x) (name-in? n (syntax-names x)))
                           ((imports-syntax? x) (brings? n x fs ls))
                           (else #f)))
               (found2 (if here (the places (list (tuple (syn-start x) (syn-end x)))) found)))
          (macro-sites n (cdr xs) fs (load-noted x ls) found2)))))
;; `ls` with what form `x` says of a load definition (`note-load-def!`).
(define load-noted (->* (syn load-defs) load-defs)
  (lambda (x ls)
    (let ((items (proper x)))
      (if (and (>= (len items) 3) (string=? (head-name x) "define") (syn-symbol? (nth items 1)))
          (let* ((n (syn-symbol (nth items 1)))
                 (path (def-path (nth items (- (len items) 1))))
                 (kept (without-load n ls)))
            (if (and (not (null? path)) (<= (len items) 4)) (cons (tuple n (car path)) kept) kept))
          ls))))
;; Whether `(import-with-syntax lib …)`, `x`, gives macro `n` its name.
(define brings? (->* (symbol syn files load-defs) bool)
  (lambda (n x fs ls)
    (let* ((items (proper x))
           (path (if (and (>= (len items) 2) (syn-symbol? (nth items 1)))
                     (load-of (syn-symbol (nth items 1)) ls)
                     nil))
           (f (if (null? path) nil (loaded-path (car path) fs))))
      (and (not (null? f))
           (forms-give? n (extract (car f) 5) fs nil #f)
           (or (= (len items) 2) (taken? n (list (lenient-filter (nth items 2)))))))))
;; Whether a file's forms, `xs`, as read (`fs` the files read, their forms
;; as read: `macros-imports.fx`'s `raw-loaded`), give macro `n` by its name:
;; a `define-syntax` of it, or an import that brings it, not hidden (`h`).
;; `ls`: the file's loads so far, each by where it starts. A macro its uses
;; make is not seen (`TODO.md` §287).
(define forms-give? (->* (symbol syns-a files (listof (tupleof symbol int) acyclic) bool) bool)
  (lambda (n xs fs ls h)
    (if (null? xs)
        #f
        (let* ((x (car xs))
               (items (proper x))
               (ls2 (if (and (>= (len items) 3) (string=? (head-name x) "define")
                             (syn-symbol? (nth items 1))
                             (not (null? (load-path (nth items (- (len items) 1))))))
                        (cons (tuple (syn-symbol (nth items 1))
                                     (syn-start (nth items (- (len items) 1))))
                              ls)
                        ls)))
          (or (cond ((hide-form? x) (and (not h) (forms-give? n (cdr items) fs ls2 #t)))
                    (h #f)
                    ((defines-syntax? x) (name-in? n (syntax-names x)))
                    ((imports-syntax? x)
                     (let ((f (if (and (>= (len items) 2) (syn-symbol? (nth items 1)))
                                  (file-load-read (syn-symbol (nth items 1)) ls2 fs)
                                  nil)))
                       (and (not (null? f))
                            (or (= (len items) 2) (taken? n (list (lenient-filter (nth items 2)))))
                            (forms-give? n (extract (car f) 5) fs nil #f))))
                    (else #f))
              (forms-give? n (cdr xs) fs ls2 h))))))
;; The file the load named `lib` of `ls` read, in a list of one.
(define file-load-read (->* (symbol (listof (tupleof symbol int) acyclic) files) files)
  (lambda (lib ls fs)
    (cond ((null? ls) nil)
          ((symbol=? lib (extract (car ls) 1)) (read-at (extract (car ls) 2) fs))
          (else (file-load-read lib (cdr ls) fs)))))
;; The file the load at `at` read; one a form before made, which the
;; driver reads too at no form's place, by its key (`syn.rs`'s
;; `supply_loaded_in`).
(define read-at (->* (int files) files)
  (lambda (at fs) (read-in at fs fs)))
(define read-in (->* (int files files) files)
  (lambda (at xs fs)
    (cond ((null? xs) nil)
          ((= (extract (car xs) 1) at)
           (if (> (extract (car xs) 2) 0)
               (the files (list (car xs)))
               (keyed (extract (car xs) 7) fs)))
          (else (read-in at (cdr xs) fs)))))
(define keyed (->* (string files) files)
  (lambda (key fs)
    (cond ((null? fs) nil)
          ((and (string=? (extract (car fs) 7) key) (> (extract (car fs) 2) 0))
           (the files (list (car fs))))
          (else (keyed key (cdr fs))))))
(define shown-syntax (->* ((listof file-macro acyclic)) (listof file-macro acyclic))
  (lambda (ms)
    (cond ((null? ms) nil)
          ((extract (car ms) 2) (shown-syntax (cdr ms)))
          (else (cons (car ms) (shown-syntax (cdr ms)))))))
;; `(only name …)` or `(except name …)`, its names those that are names.
(define lenient-filter (->* (syn) filter)
  (lambda (f)
    (tuple (string=? (head-name f) "only") (names-only (cdr (proper f))))))
(define names-only (->* (syns-a) syns-a)
  (lambda (xs)
    (cond ((null? xs) nil)
          ((syn-symbol? (car xs)) (cons (car xs) (names-only (cdr xs))))
          (else (names-only (cdr xs))))))

;;; ------------------------------------------------------------ a macro written

;; A `syntax-rules`' trailmarks, `lits`, each a name the signature writes,
;; `(trailmark name)`, where the pattern has it; and no other: of the
;; pattern's nodes from `i`.
(define literals-said (->* (fails names int) unit)
  (lambda (fail lits i)
    (if (= i (get nnodes))
        #u
        (let ((s (node-syn i)))
          (begin
            (if (syn-symbol? s)
                (let* ((k (kind-of (node-core i))) (lit (or (= k 7) (= k 15)))
                       (n (syn-symbol s)))
                  (cond
                    ((and (= k 15) (not (name-in? n lits)))
                     (fail-at fail (string-append "`" (syn-name s) "` is the trailmark the "
                                                  "signature writes here, `(trailmark " (syn-name s)
                                                  ")`, and is not among the `syntax-rules`' "
                                                  "`#:trailmarks`")
                              s))
                    ((and (not lit) (tagcase (node-kids i) (k-pvar (m) #t) (else y #f))
                          (name-in? n lits))
                     (fail-at fail (string-append "`" (syn-name s) "` is among the `syntax-rules`' "
                                                  "`#:trailmarks`, and the signature has a part "
                                                  "here, not `(trailmark " (syn-name s) ")`")
                              s))
                    (else #u)))
                #u)
            (literals-said fail lits (+ i 1)))))))
;; A macro's definition as written (`macros.rs`'s `written`).
(define define-usage string
  (string-append "`(define-syntax name [signature] (syntax-rules [#:trailmarks (name …)] "
                 "((_ . pattern) template) …))`"))
(define rec-usage string
  "`(define-syntax-rec (name [signature] (syntax-rules [#:trailmarks (name …)] clause …)) …)`")
(define rules-usage string
  "`(syntax-rules [#:trailmarks (name …)] ((_ . pattern) template) …)`")
;; A macro as its `define-syntax` writes it: its name, its signature if
;; written (none or one), its `syntax-rules`' literals and clauses, and the
;; form (or `define-syntax-rec`'s member) it is in.
(define-type written (tupleof symbol syns-a names syns-a syn))
(define-type writtens (listof written acyclic))
(define written-of (->* (fails syn) writtens)
  (lambda (fail form)
    (let ((items (proper form)))
      (cond
        ((< (len items) 2)
         (begin (fail-at fail (if (string=? (head-name form) "define-syntax-rec") rec-usage
                                  define-usage)
                         form)
                nil))
        ((string=? (head-name form) "define-syntax-rec") (written-members fail (cdr items) nil))
        (else (list (written-one fail (nth items 1) (cdr (cdr items)) form define-usage)))))))
(define written-members (->* (fails syns-a writtens) writtens)
  (lambda (fail ms out)
    (if (null? ms)
        (reverse out)
        (let ((parts (proper (car ms))))
          (if (null? parts)
              (begin (fail-at fail rec-usage (car ms)) nil)
              (let ((w (written-one fail (car parts) (cdr parts) (car ms) rec-usage)))
                (if (written-in? (extract w 1) out)
                    (begin (fail-at fail (string-append "`" (symbol->string (extract w 1))
                                                        "` is defined twice in this "
                                                        "`define-syntax-rec`")
                                    (car parts))
                           nil)
                    (written-members fail (cdr ms) (cons w out)))))))))
(define written-in? (->* (symbol writtens) bool)
  (lambda (n ws)
   (and (not (null? ws)) (or (symbol=? n (extract (car ws) 1)) (written-in? n (cdr ws))))))
(define rules? (->* (syn) bool) (lambda (s) (string=? (head-name s) "syntax-rules")))
(define written-one (->* (fails syn syns-a syn string) written)
  (lambda (fail name rest at usage)
    (let ((none (tuple (string->symbol "") (the syns-a nil) (the names nil) (the syns-a nil) at)))
      (cond
        ((or (not (syn-symbol? name)) (reserved-syn? name))
         (begin (fail-at fail (string-append usage ": a macro's name, not a form's") name) none))
        ((and (= (len rest) 1) (trailmark? (car rest)))
         (begin (fail-at fail "a trailmark is defined alone, by `define-syntax`" at) none))
        ((and (= (len rest) 1) (rules? (car rest)))
         (rules-written fail (syn-symbol name) nil (car rest) at))
        ((and (= (len rest) 2) (rules? (nth rest 1)))
         (rules-written fail (syn-symbol name) (list (car rest)) (nth rest 1) at))
        ((and (>= (len rest) 2) (= (len (proper (nth rest 1))) 2))
         (begin (fail-at fail (string-append "a macro's clauses are a transformer's: "
                                             rules-usage ", after its signature if it is written")
                         (nth rest 1))
                none))
        (else (begin (fail-at fail usage at) none))))))
(define rules-written (->* (fails symbol syns-a syn syn) written)
  (lambda (fail n sig rules at)
    (let* ((rp (rules-parts fail (cdr (proper rules)) rules)) (lits (extract rp 1))
           (unbound (names-only-unmarked lits)))
      (begin
        ;; Each of its `#:trailmarks` bound to one where it is defined.
        (if (null? unbound)
            #u
            (fail-at fail (no-trailmark (symbol->string (car unbound))) at))
        (tuple n sig lits (extract rp 2) at)))))
(define names-only-unmarked (->* (names) names)
  (lambda (ns)
    (cond ((null? ns) nil)
          ((= (mark-now (car ns)) 0) (list (car ns)))
          (else (names-only-unmarked (cdr ns))))))
;; A `syntax-rules`' parts after its head: the names its `#:trailmarks (name
;; …)` lists, if it has one, and its clauses; a `()` or a list of names
;; first, R7RS's literals, refused, saying how it is written now
;; (`macros.rs`'s `rules_parts`).
(define rules-parts (->* (fails syns-a syn) (tupleof names syns-a))
  (lambda (fail parts rules)
    (let ((none (tuple (the names nil) (the syns-a nil))))
      (cond
        ((null? parts) (begin (fail-at fail rules-usage rules) none))
        ((and (syn-keyword? (car parts)) (string=? (keyword-name (car parts)) "trailmarks")
              (not (null? (cdr parts))))
         (let ((ns (proper (nth parts 1))))
           (if (and (not (null? ns)) (all-names? ns))
               (tuple (names-of-syns ns) (cdr (cdr parts)))
               (begin (fail-at fail (string-append "a `syntax-rules`' `#:trailmarks` are a list "
                                                   "of names, one or more")
                               (nth parts 1))
                      none))))
        ((syn-keyword? (car parts)) (begin (fail-at fail rules-usage (car parts)) none))
        ((syn-nil? (car parts))
         (begin (fail-at fail (string-append "a `syntax-rules` has no list of literals: drop the "
                                             "`()` (names its patterns match are written "
                                             "`#:trailmarks (name …)`)")
                         (car parts))
                none))
        ((and (not (null? (proper (car parts)))) (all-names? (proper (car parts))))
         (begin (fail-at fail (string-append "a `syntax-rules`' names its patterns match are its "
                                             "trailmarks: `#:trailmarks " (show-syn (car parts))
                                             "`, each defined `(define-syntax name (trailmark))`")
                         (car parts))
                none))
        (else (tuple (the names nil) parts))))))
;; A trailmark's definition, `(define-syntax name (trailmark ["where it
;; belongs"]))`: its transformer, in a list of one (`macros.rs`'s `Mark`).
(define trailmark? (->* (syn) bool)
  (lambda (t)
    (let ((items (proper t)))
      (and (not (null? items)) (syn-symbol? (car items))
           (string=? (syn-name (car items)) "trailmark")))))
(define trailmark-form (->* (syn) syns-a)
  (lambda (form)
    (let ((items (proper form)))
      (if (and (= (len items) 3) (string=? (head-name form) "define-syntax")
               (trailmark? (nth items 2)))
          (list (nth items 2))
          nil))))
;; Trailmark `form` defined, apart from the macros, which no longer have its
;; name: its name.
(define define-trailmark (->* (fails syn) names)
  (lambda (fail form)
    (let* ((name (nth (proper form) 1)) (t (nth (proper form) 2)) (said (cdr (proper t))))
      (cond
        ((or (not (syn-symbol? name)) (reserved-syn? name))
         (begin (fail-at fail (string-append define-usage ": a macro's name, not a form's") name)
                nil))
        ((not (or (null? said) (and (null? (cdr said)) (syn-string? (car said)))))
         (begin (fail-at fail "`(trailmark)`, or `(trailmark \"where it belongs\")`" t) nil))
        (else
         (begin
           (set defined (macros-but (syn-symbol name) (get defined)))
           (set mark-count (+ (get mark-count) 1))
           (set marks (cons (tuple (syn-symbol name) (get mark-count)) (get marks)))
           (list (syn-symbol name))))))))
(define macros-but (->* (symbol macro-env) macro-env)
  (lambda (n ms)
    (cond ((null? ms) nil)
          ((symbol=? n (extract (car ms) 1)) (macros-but n (cdr ms)))
          (else (cons (car ms) (macros-but n (cdr ms)))))))
;; Macros `ns` defined: a trailmark of a name of theirs no longer is one.
(define hide-marks! (->* (names) unit)
  (lambda (ns)
    (if (null? ns)
        #u
        (begin (set marks (cons (tuple (car ns) 0) (get marks))) (hide-marks! (cdr ns))))))
(define all-names? (->* (syns-a) bool)
  (lambda (xs) (or (null? xs) (and (syn-symbol? (car xs)) (all-names? (cdr xs))))))
(define names-of-syns (->* (syns-a) names)
  (lambda (xs) (if (null? xs) nil (cons (syn-symbol (car xs)) (names-of-syns (cdr xs))))))
;; A signature as written: the binders of its `(poly (binder …) σ)`, the
;; syntax type, and what it makes (0 an expression, 1 definitions, 2 a
;; description).
(define-type signed (tupleof syns-a sty int))
(define signature-of (->* (fails syn) signed)
  (lambda (fail s0)
    (let* ((poly0 (signature-poly fail s0))
           ;; In shapes and facts: elaborated to Herman's form, which is read.
           (poly (if (contract? (extract poly0 2))
                     (tuple (extract poly0 1) (elaborated fail (extract poly0 2)))
                     poly0))
           (sig (extract poly 2)) (sigs (proper-items sig))
           (lettered (if (and (pair? sigs) (syn-symbol? (car sigs))
                              (string=? (syn-name (car sigs)) "macro/addressed"))
                         (lettered-in sig)
                         nil))
           (said (if (null? lettered)
                     #u
                     (fail-at fail (string-append "`" (show-syn (car lettered)) "` is an address "
                                                  "in Herman's letters: " path-usage)
                              (car lettered))))
           (made (signature-made fail (extract poly 2)))
           (t (read-sty fail (extract made 1) nil nil)))
      (begin
        ;; Each macro it says a use defines, its signature read now.
        (tagcase t
          (s-export (b x) (tagcase x (bind-rib (es) (syntax-sigs-read! fail es)) (else y #u)))
          (else y #u))
        (tuple (extract poly 1) t (extract made 2))))))
(define syntax-sigs-read! (->* (fails entries) unit)
  (lambda (fail es)
    (cond ((null? es) #u)
          ((and (>= (extract (car es) 2) 100) (null? (syntax-sig-read (extract (car es) 2))))
           (let ((r (signature-of fail (syntax-sig-of (extract (car es) 2)))))
             (begin (if (null? (extract r 1))
                        (syntax-read! (extract (car es) 2) (extract r 2) (extract r 3))
                        (fail-at fail "a `(macro σ made)` entry's signature has no `poly`, not yet"
                                 (syntax-sig-of (extract (car es) 2))))
                    (syntax-sigs-read! fail (cdr es)))))
          (else (syntax-sigs-read! fail (cdr es))))))
(define written-names (->* (writtens) names)
  (lambda (ws) (if (null? ws) nil (cons (extract (car ws) 1) (written-names (cdr ws))))))
;; A signature's `(poly ((name kind) …) σ)`: its binders and `σ`; else none
;; and itself.
(define signature-poly (->* (fails syn) (tupleof syns-a syn))
  (lambda (fail s)
    (let ((items (proper s)))
      (if (and (= (len items) 3) (syn-symbol? (car items)) (string=? (syn-name (car items)) "poly"))
          (if (or (syn-nil? (nth items 1)) (not (null? (proper (nth items 1)))))
              (tuple (proper (nth items 1)) (nth items 2))
              (begin (fail-at fail "a signature's `(poly ((name kind) …) σ)`" (nth items 1))
                     (tuple (the syns-a nil) s)))
          (tuple (the syns-a nil) s)))))
;; The names `poly`'s binders bind.
(define binder-names (->* (syns-a) names)
  (lambda (bs)
    (cond ((null? bs) nil)
          ((and (not (null? (proper (car bs)))) (syn-symbol? (car (proper (car bs)))))
           (cons (syn-symbol (car (proper (car bs)))) (binder-names (cdr bs))))
          (else (binder-names (cdr bs))))))
;; Whether syntax `s` names one of `ns`.
(define names-any? (->* (syn names) bool)
  (lambda (s ns)
    (cond ((syn-symbol? s) (name-in? (syn-symbol s) ns))
          ((null? (split s)) #f)
          (else (or (names-any? (car (split s)) ns) (names-any? (nth (split s) 1) ns))))))
(define-type signed-opt (listof signed acyclic))
(define signed-each (->* (fails writtens) (listof signed-opt acyclic))
  (lambda (fail ws)
    (if (null? ws)
        nil
        (let ((w (car ws)))
          (if (null? (extract w 2))
              (cons (the signed-opt nil) (signed-each fail (cdr ws)))
              (let ((s (signature-of fail (car (extract w 2)))))
                (begin
                  (set defined (cons (tuple (extract w 1) (tuple (extract s 2) (the clauses nil)
                                                                 (extract s 1) (extract s 3)))
                                     (get defined)))
                  (cons (the signed-opt (list s)) (signed-each fail (cdr ws))))))))))
;; Operands `body` of a signature whose result is `made`, `(defn entry …)`:
;; `body`, defining `entries`, `(export body (rho entry …))`.
(define defined-in (->* (fails syn syn syns-a) syn)
  (lambda (fail body made entries)
    (let ((bs (proper-items body)) (a (syn-start made)) (b (syn-end made)))
      (cond ((null? entries) body)
            ((and (pair? bs) (syn-symbol? (car bs)) (string=? (syn-name (car bs)) "export"))
             (begin (fail-at fail (string-append "what a use defines is said once, in what it "
                                                 "makes, `(defn (ℓ δ) …)`, not by an `export` "
                                                 "around its parts too")
                             body)
                    body))
            (else (let ((rho (mk-list (cons (mk-symbol "rho" a b) entries) a b)))
                    (mk-list (list (mk-symbol "export" a b) body rho) a b)))))))
;; An address of signature `s` written as Herman's letters, `AAD`, in a list
;; of one: the kernel's own signatures keep them, a program's write `(path
;; …)` (`macros.rs`'s `lettered`).
(define lettered-in (->* (syn) syns-a)
  (lambda (s)
    (let* ((items (proper-items s))
           (head (if (and (pair? items) (syn-symbol? (car items))) (syn-name (car items)) ""))
           (here (cond ((or (string=? head "rho") (string=? head "defn"))
                        (lettered-entries (cdr items)))
                       ((and (or (string=? head "at") (string=? head "shape")) (= (len items) 2)
                             (letters? (nth items 1)))
                        (list (nth items 1)))
                       (else nil))))
      (if (null? here) (lettered-each items) here))))
(define lettered-each (->* (syns-a) syns-a)
  (lambda (xs)
    (if (null? xs)
        nil
        (let ((r (lettered-in (car xs)))) (if (null? r) (lettered-each (cdr xs)) r)))))
(define lettered-entries (->* (syns-a) syns-a)
  (lambda (es)
    (cond ((null? es) nil)
          ((and (pair? (proper-items (car es))) (letters? (car (proper-items (car es)))))
           (list (car (proper-items (car es)))))
          (else (lettered-entries (cdr es))))))
(define letters? (->* (syn) bool)
  (lambda (a) (and (syn-symbol? a) (letters-from? (syn-name a) 0))))
(define letters-from? (->* (string int) bool)
  (lambda (n i)
    (or (= i (string-length n))
        (and (or (char=? (string-ref n i) #\A) (char=? (string-ref n i) #\D))
             (letters-from? n (+ i 1))))))
;; How macro `n`'s refusal is said, its signature inferred, `shown`, not
;; fitting its clauses: refused, said so on a line of its own, then what was
;; inferred and how one is written (`macros.rs`'s `refused_inferred`).
(define said-fail (->* (fails string string) fails)
  (lambda (fail n shown)
    (lambda ((m string) (a int) (b int))
      (fail (string-append "`" n "` is refused: no signature is written, and the one inferred "
                           "from its clauses does not fit them: " m "\n  inferred: " shown
                           "\n  write one: (define-syntax " n " SIGNATURE (syntax-rules …))")
            a b))))
;; A signature in Herman's form, `(macro/addressed σ made)`, as one in shapes
;; and facts is elaborated to: `σ`, and what it makes, 0 an expression,
;; `expr`, 1 definitions, `defn`, 2 a description, `desc`. `(macro/addressed
;; σ (defn (ℓ δ) …))`: definitions, `(export σ (rho (ℓ δ) …))`
;; (`macros.rs`'s `signature`).
(define signature-made (->* (fails syn) (tupleof syn int))
  (lambda (fail s)
    (let ((items (proper-items s)))
      (if (and (= (len items) 3) (syn-symbol? (car items))
               (string=? (syn-name (car items)) "macro/addressed"))
          (let* ((m (nth items 2)) (ms (proper-items m))
                 (made (cond ((syn-symbol? m) (syn-name m))
                             ((and (pair? ms) (syn-symbol? (car ms))
                                   (string=? (syn-name (car ms)) "defn"))
                              "(defn")
                             (else ""))))
            (cond ((and (string=? made "defn") (old-defn-export? (nth items 1)))
                   (begin
                     (fail-at fail
                              (string-append "what a use defines is said in what it makes, "
                                             "`(macro/addressed σ (defn (ℓ δ) …))`, not by "
                                             "`(export σ (rho (ℓ δ) …))` around its parts: the "
                                             "`rho`'s entries go in the `defn`")
                              (nth items 1))
                     (tuple (nth items 1) 1)))
                  ((string=? made "defn") (tuple (nth items 1) 1))
                  ((string=? made "(defn") (tuple (defined-in fail (nth items 1) m (cdr ms)) 1))
                  ((string=? made "desc") (tuple (nth items 1) 2))
                  ((string=? made "expr") (tuple (nth items 1) 0))
                  (else (begin (fail-at fail (string-append "what a signature's uses make is "
                                                            "`expr`, `defn`, `(defn D …)` or "
                                                            "`desc`")
                                        (nth items 2))
                               (tuple s 0)))))
          (let ((h (if (and (pair? items) (syn-symbol? (car items))) (syn-name (car items)) "")))
            (begin (fail-at fail (cond ((string=? h "->")
                                        (string-append "a macro's signature is `(macro (_ part …) "
                                                       "made fact …)`: `->` is a procedure's type"))
                                       ((string=? h "macro")
                                        (string-append "a signature in shapes and facts is `(macro "
                                                       "(_ part …) made fact …)`; Herman's, "
                                                       "`(macro/addressed σ made)`"))
                                       (else
                                        (string-append "a signature is `(macro (_ part …) made "
                                                       "fact …)`, what its uses make written: "
                                                       "`expr`, `defn`, `(defn D …)` or `desc`")))
                            s)
                   (tuple s 0)))))))
;; Whether `body`, operands a signature's uses make definitions of, is the
;; old `(export σ (rho (ℓ δ) …))`, taken out (`TODO.md` §288), now `σ` with
;; `(defn (ℓ δ) …)` (`macros.rs`'s `old_defn_export`).
(define old-defn-export? (->* (syn) bool)
  (lambda (body)
    (let ((bs (proper-items body)))
      (and (= (len bs) 3) (syn-symbol? (car bs)) (string=? (syn-name (car bs)) "export")
           (let ((r (proper-items (nth bs 2))))
             (and (pair? r) (syn-symbol? (car r)) (string=? (syn-name (car r)) "rho")))))))
