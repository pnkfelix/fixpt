;;; Typed hygienic macros, in FX-26: a file's macros, which
;;; `import-with-syntax` brings (`macros.rs`'s `define_file`,
;;; `Checker::import_file_macros`), defined by the expander (`macros.fx`),
;;; each meaning what it meant in its file. Loaded by `parser-top.fx`; loads
;;; `macros-templates.fx`, and gives it on (`templates-module`), so that the
;;; parser's instances of the expander's parts are one.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define templates-module ((proj (load-module "fx26:macros-templates.fx") rs re rm rc rp)))
(define macros-module (with templates-module macros-module))
(import macros-module atom define-macro defined fail-at file-items file-syntax
        head-name import-usage in-loaded-as internal-names internal-of len load-base load-of
        load-path loaded-path loads macro-names macro-of macro? mk-list mk-symbol name-filter
        names-shown not-macros nth proper shown-names syn-end syn-start syn-symbol syn-symbol?
        taken? without-load marks for-syntax? for-syntax!
        (type fails file-macro files filter macro macro-env mades names scope syn syns-a marked))
(define procedural-module (with macros-module procedural-module))
(import procedural-module phase1-forms-now phase1-forms! def-env-is def-env-now!)
(define fresh-module (with macros-module fresh-module))
(import fresh-module file-prefix instance-prefix file-keys-begin! file-keys-end! use-begin! use-end!
        form-begin!)
(import macros-module expand-top made-syntax-taken! makes-top-defns? imports-syntax? hide-form?
        defines-syntax? name-in?)
(define files-module (with macros-module files-module))
(import files-module read-at def-path instance-path)
(define parser-module (with macros-module parser-module))
(import parser-module (type loaded-file))

;; Notes a top-level `(define name (load-module "path"))`, the file
;; `import-with-syntax` of `name` reads, or `(define name ((proj (load-module
;; "path") arg …)))`, an instance of it, which `instances` notes; any other
;; definition of `name` forgets it (`Checker::note_load_def`).
(define note-load-def! (->* (syn) unit)
  (lambda (form)
    (let ((items (proper form)))
      (if (and (>= (len items) 3) (string=? (head-name form) "define") (syn-symbol? (nth items 1)))
          (let* ((n (syn-symbol (nth items 1)))
                 (init (nth items (- (len items) 1)))
                 (path (def-path init))
                 (kept (without-load n (get loads)))
                 (ok (and (not (null? path)) (<= (len items) 4))))
            (begin
              (set loads (if ok (cons (tuple n (car path)) kept) kept))
              (set instances (if (and ok (not (null? (instance-path init))))
                                 (cons n (without-name n (get instances)))
                                 (without-name n (get instances))))))
          #u))))
(define instances (ref names rs) (new nil))
(define without-name (->* (symbol names) names)
  (lambda (n ns)
    (cond ((null? ns) nil)
          ((symbol=? n (car ns)) (without-name n (cdr ns)))
          (else (cons (car ns) (without-name n (cdr ns)))))))

;; The standard bindings' names, which a file's macro may name: what the
;; driver says, as the Rust checker has them (`standard-names!`).
(define standard-names (ref names rs) (new nil))
(define standard-names! (->* (names) unit) (lambda (ns) (set standard-names ns)))


;; The forms the files whose own macros' uses were expanded were read as, by
;; base (`parser-top.fx`'s `loaded-own-expanded!`): what an importer reads
;; of each, as the Rust checker reads its text again (`file_macros_at`).
(define-type raw (listof (tupleof int syns-a) acyclic))
(define raw-files (ref raw rs) (new nil))
(define raw-files! (->* (raw) unit) (lambda (r) (set raw-files r)))
(define raw-forms (->* (loaded-file) syns-a)
  (lambda (f) (raw-at (extract f 2) (get raw-files) (extract f 5))))
;; The files read, `fs`, each with its forms as read.
(define raw-loaded (->* (files) files)
  (lambda (fs)
    (if (null? fs)
        nil
        (let ((f (car fs)))
          (cons (product (1 (extract f 1)) (2 (extract f 2)) (3 (extract f 3)) (4 (extract f 4))
                         (5 (raw-forms f)) (6 (extract f 6)) (7 (extract f 7)) (8 (extract f 8)))
                (raw-loaded (cdr fs)))))))
(define raw-at (->* (int raw syns-a) syns-a)
  (lambda (base r forms)
    (cond ((null? r) forms)
          ((= base (extract (car r) 1)) (extract (car r) 2))
          (else (raw-at base (cdr r) forms)))))

;; `(import-with-syntax lib)`, `lib` a name defined as `(load-module
;; "path")`: the file's macros defined, each as the file means it, and the
;; rest of what it gives as `(include lib)` gives it: that `include`'s form,
;; in a list of one; none if `(only …)` names macros alone. Of `fs`, the
;; files the driver read (`Checker::import_file_macros`).
(define import-file-macros (->* (fails syn files) syns-a)
  (lambda (fail form fs)
    (let* ((items (proper form)) (a (syn-start form)) (b (syn-end form)))
      (if (not (and (or (= (len items) 2) (= (len items) 3)) (syn-symbol? (nth items 1))))
          (begin (fail-at fail import-usage form) nil)
          (let* ((lib (syn-symbol (nth items 1)))
                 (filter (if (= (len items) 3)
                             (the (listof filter acyclic) (list (name-filter fail (nth items 2))))
                             nil))
                 (path (load-of lib (get loads))))
            (if (null? path)
                (begin (fail-at fail (not-load lib) form) nil)
                (let ((f (loaded-path (car path) fs)))
                  (if (null? f)
                      (begin (fail-at fail (string-append "cannot read `" (car path) "`") form) nil)
                      (let* ((inst (if (name-in? lib (get instances)) (list lib) nil))
                             (g (given-names (file-macros-of fail form (car f) filter fs inst))))
                        (begin (set imported (taken-names g filter))
                               (include-of (mk-symbol (symbol->string lib) a b) filter g
                                           a b)))))))))))
;; The macros the last `import-file-macros` defined by their names, which
;; the parser holds to the globals (`top-made`).
(define imported (ref names rs) (new nil))
(define imported-names (->* () names) (lambda () (get imported)))
(define taken-names (->* (names (listof filter acyclic)) names)
  (lambda (ns filter)
    (cond ((null? ns) nil)
          ((taken? (car ns) filter) (cons (car ns) (taken-names (cdr ns) filter)))
          (else (taken-names (cdr ns) filter)))))
(define not-load (->* (symbol) string)
  (lambda (lib)
    (string-append "`import-with-syntax` takes a name defined as `(load-module \"path\")`, "
                   "and `" (symbol->string lib) "` is not one")))
;; An `import-with-syntax`, `form`, in a module file, of loads `ls`, the
;; file's so far (`file-loads`): its file's macros defined, each as the
;; file means it, and the rest the `include` of the hidden global every
;; load of `lib`'s file is, which `lib` is too, by its name, a module's
;; `include` being made before its items (`Checker::file_own_expanded_syn`).
(define import-in-file (->* (fails syn file-loads files) syns-a)
  (lambda (fail form ls fs)
    (let* ((items (proper form)) (a (syn-start form)) (b (syn-end form)))
      (if (not (and (or (= (len items) 2) (= (len items) 3)) (syn-symbol? (nth items 1))))
          (begin (fail-at fail import-usage form) nil)
          (let* ((filter (if (= (len items) 3)
                             (the (listof filter acyclic) (list (name-filter fail (nth items 2))))
                             nil))
                 (load (load-of-file (syn-symbol (nth items 1)) ls))
                 (f (if (null? load) nil (read-at (syn-start (car load)) fs))))
            (cond
              ((not (null? (instance-loaded (syn-symbol (nth items 1)) ls)))
               (begin (fail-at fail (instance-in-file (syn-symbol (nth items 1))) form) nil))
              ((null? f) (begin (fail-at fail (not-load (syn-symbol (nth items 1))) form) nil))
              (else
               (include-of (mk-symbol (string-append "%shared:" (extract (car f) 7)) a b) filter
                           (given-names (file-macros-of fail form (car f) filter fs nil))
                           a b))))))))
;; Whether a module file's `lib`, of its loads `ls`, is an instance of a file
;; with module parameters, whose macros a module file cannot import: its
;; values' `include` would be of an item (`Checker::load_in_file`). Its
;; load, in a list of one.
(define instance-loaded (->* (symbol file-loads) syns-a)
  (lambda (lib ls)
    (let ((l (load-of-file lib ls)))
      (if (and (not (null? l)) (not (null? (instance-path (car l))))) l nil))))
(define instance-in-file (->* (symbol) string)
  (lambda (lib)
    (string-append "`" (symbol->string lib) "` is an instance of a file with module parameters: "
                   "a module file cannot import its macros, not yet")))
;; A module file's `(define name (load-module "path"))`s so far, the last
;; first, each with its load, which the driver read it by where it starts.
(define-type file-loads (listof (tupleof symbol syn) acyclic))
(define file-load-noted (->* (syn file-loads) file-loads)
  (lambda (x ls)
    (let ((items (proper x)))
      (if (and (>= (len items) 3) (string=? (head-name x) "define") (syn-symbol? (nth items 1)))
          (let ((n (syn-symbol (nth items 1))) (init (nth items (- (len items) 1))))
            (if (and (not (null? (def-path init))) (<= (len items) 4))
                (cons (tuple n init) (without-file-load n ls))
                (without-file-load n ls)))
          ls))))
(define without-file-load (->* (symbol file-loads) file-loads)
  (lambda (n ls)
    (cond ((null? ls) nil)
          ((symbol=? n (extract (car ls) 1)) (without-file-load n (cdr ls)))
          (else (cons (car ls) (without-file-load n (cdr ls)))))))
;; The load `lib` names, of loads `ls`, in a list of one; and the file it
;; read.
(define load-of-file (->* (symbol file-loads) syns-a)
  (lambda (lib ls)
    (cond ((null? ls) nil)
          ((symbol=? lib (extract (car ls) 1)) (list (extract (car ls) 2)))
          (else (load-of-file lib (cdr ls))))))
(define file-of (->* (symbol file-loads files) files)
  (lambda (lib ls fs)
    (let ((load (load-of-file lib ls))) (if (null? load) nil (read-at (syn-start (car load)) fs)))))

;; The `include` that gives the rest, of module `lib`: of the names `filter`
;; lists, those not macros.
(define include-of (->* (syn (listof filter acyclic) names int int) syns-a)
  (lambda (lib filter exported a b)
    (let ((head (list (mk-symbol "include" a b) lib)))
      (if (null? filter)
          (list (mk-list head a b))
          (let ((rest (not-macros (extract (car filter) 2) exported)))
            (if (and (extract (car filter) 1) (null? rest))
                nil
                (list (mk-list (append head
                                       (list (mk-list (cons (mk-symbol (if (extract (car filter) 1)
                                                                           "only"
                                                                           "except")
                                                                       a b)
                                                            rest)
                                                      a b)))
                               a b))))))))

;; Each macro a file gives, with the name the importer has it by.
(define-type given (listof (tupleof symbol symbol) acyclic))
(define given-names (->* (given) names)
  (lambda (g) (if (null? g) nil (cons (extract (car g) 1) (given-names (cdr g))))))

;; The macros of the file read as `f`, which `form` imports: each defined
;; as the file means it (`define-file`); the macros it gives
;; (`Checker::file_macros_at`). `inst`: the instance of it imported, if any,
;; in a list of one (`binding-shapes.md`, step 4 (c)).
(define file-macros-of (->* (fails syn loaded-file (listof filter acyclic) files names) given)
  (lambda (fail form f filter fs inst)
    (let ((forms (raw-forms f)) (path (extract f 4)))
      (if (and (null? inst) (not (null? forms))
               (string=? (head-name (car forms)) "module-parameters"))
          (begin (fail-at fail (string-append "`" path "` takes module parameters: import the "
                                              "macros of an instance of it, `(define name ((proj "
                                              "(load-module \"" path "\") arg …)))`")
                          form)
                 nil)
          (let* ((key (extract f 7)) (base (extract f 2))
                 ;; An error in the file, said in it, where the form starts.
                 (in-file (lambda ((m string) (x int) (y int))
                            (if (and (>= x base) (< x (+ base load-base)))
                                (let ((at (syn-start form)))
                                  (fail (in-loaded-as fs base path m x) at at))
                                (fail m x y))))
                 (ms (file-syntax forms))
                 (shown (names-shown (file-items forms) nil nil))
                 ;; An instance's macros by names of their own, and its uses'
                 ;; keys (`instance-prefix`), so that two instances' are apart.
                 (ikey (if (null? inst) key (string-append key "@" (symbol->string (car inst)))))
                 (prefix (if (null? inst)
                             (file-prefix key #t)
                             (instance-prefix (file-prefix key #t) (car inst))))
                 (internal (internal-names ikey (macro-names ms)))
                 (shared (if (null? inst)
                             (string->symbol (string-append "%shared:" key))
                             (car inst)))
                 (scope (tuple shared (extract shown 1) (extract shown 2) internal
                               (get standard-names))))
            (define-file in-file forms scope filter fs ikey prefix (if (null? inst) 1 3)
                         (if (null? ms) form (extract (car ms) 1))))))))

;; A file's macros, of its forms `forms`, defined as the file means them
;; (`scope`): among themselves first, by their names in it, as its
;; templates name them, with the macros of the files it imports and those
;; its top-level uses make (`TODO.md` §287), each use expanded as a form of
;; its own, its key of the file's (`file-prefix`), where the file's items
;; are as its importer has them; then each by the name the importer has it
;; by, and each it gives (not hidden, nor of a hidden import) that `filter`
;; takes by its own name too (`Macros::define_file`). The macros it gives.
(define define-file
  (->* (fails syns-a scope (listof filter acyclic) files string string int syn) given)
  (lambda (fail forms scope filter fs key prefix kind first)
    (let ((program (get defined)) (program-marks (get marks)) (program-phase1 (phase1-forms-now))
          (program-env (def-env-is)) (keys (file-keys-begin! prefix)))
      (begin
        (set defined nil)
        (set marks nil)
        ;; The file's phase-1 forms its own, for its macros alone.
        (phase1-forms! nil)
        (def-env-now! (tuple kind (extract scope 1) (extract scope 2)))
        (let* ((st (define-forms fail forms #f scope fs key (tuple (extract scope 4) nil nil)))
               (own (get defined)) (own-marks (get marks)))
          (begin
            (set defined program)
            (set marks program-marks)
            (phase1-forms! program-phase1)
            (def-env-now! program-env)
            (file-keys-end! keys)
            ;; Every macro of the file's by the name the importer has it by,
            ;; hidden or not, which those it gives may expand to.
            (set defined (append (internal-macros own) (get defined)))
            (set marks (append (internal-marks own-marks) (get marks)))
            (give-each fail (reverse-mades (extract st 2) nil) own own-marks (extract st 1) filter
                       first nil)))))))
;; What a file's forms defined so far: the name the importer has each of its
;; macros by, the macros it gives, each with whether it is hidden, the last
;; first, and its load definitions.
(define-type file-state (tupleof (listof (tupleof symbol symbol) acyclic) mades file-loads))
(define define-forms (->* (fails syns-a bool scope files string file-state) file-state)
  (lambda (fail xs h scope fs key st)
    (if (null? xs)
        st
        (let* ((x (car xs))
               (st2 (tuple (extract st 1) (extract st 2) (file-load-noted x (extract st 3)))))
          (define-forms fail (cdr xs) h scope fs key (define-form fail x h scope fs key st2))))))
(define define-form (->* (fails syn bool scope files string file-state) file-state)
  (lambda (fail x h scope fs key st)
    (let ((internal (extract st 1)) (made (extract st 2)) (ls (extract st 3)))
      (cond
        ((and (not h) (hide-form? x)) (define-forms fail (cdr (proper x)) #t scope fs key st))
        ;; The file's phase-1 forms, in force for its macros after them.
        ((for-syntax? x) (begin (for-syntax! fail x) st))
        ((defines-syntax? x)
         (let ((ns (define-macro fail x (list (tuple (extract scope 1) (extract scope 2)
                                                    (extract scope 3) internal
                                                    (extract scope 5))))))
           (begin (by-internal-each ns internal)
                  (tuple internal (onto-mades ns h made) ls))))
        ((imports-syntax? x)
         (let* ((items (proper x))
                (filter (if (= (len items) 3)
                            (the (listof filter acyclic) (list (name-filter fail (nth items 2))))
                            nil))
                (f (if (and (>= (len items) 2) (syn-symbol? (nth items 1)))
                       (file-of (syn-symbol (nth items 1)) ls fs)
                       nil)))
           (if (null? f)
               (begin (fail-at fail (cond ((not (and (>= (len items) 2)
                                                     (syn-symbol? (nth items 1))))
                                           import-usage)
                                          ((not (null? (instance-loaded (syn-symbol (nth items 1))
                                                                        ls)))
                                           (instance-in-file (syn-symbol (nth items 1))))
                                          (else (not-load (syn-symbol (nth items 1)))))
                               x)
                      st)
               (let ((g (taken-given (file-macros-of fail x (car f) filter fs nil) filter)))
                 (tuple (append g internal) (onto-mades (given-names g) h made) ls)))))
        ;; A use of a macro that makes definitions, which may make macros.
        ((let ((items (proper x)))
           (and (not (null? items)) (syn-symbol? (car items))
                (makes-top-defns? (syn-symbol (car items)))))
         (let* ((s (use-begin!))
                (ns (begin (form-begin! x) (expand-top fail x) (made-syntax-taken!)))
                (back (use-end! s))
                (more (internal-names key ns)))
           (begin (by-internal-each ns more)
                  (tuple (append more internal) (onto-mades ns h made) ls))))
        (else st)))))
(define taken-given (->* (given (listof filter acyclic)) given)
  (lambda (g filter)
    (cond ((null? g) nil)
          ((taken? (extract (car g) 1) filter) (cons (car g) (taken-given (cdr g) filter)))
          (else (taken-given (cdr g) filter)))))
(define onto-mades (->* (names bool mades) mades)
  (lambda (ns h made) (if (null? ns) made (onto-mades (cdr ns) h (cons (tuple (car ns) h) made)))))
(define reverse-mades (->* (mades mades) mades)
  (lambda (xs acc) (if (null? xs) acc (reverse-mades (cdr xs) (cons (car xs) acc)))))
;; Each of macros `ns` of the file's by the name the importer has it by too,
;; for the file's uses that expand to it.
(define by-internal-each (->* (names (listof (tupleof symbol symbol) acyclic)) unit)
  (lambda (ns internal)
    (if (null? ns)
        #u
        (let ((i (internal-of (car ns) internal)) (k (own-mark (car ns) (get marks)))
              (m (macro-of (car ns) (get defined))))
          (begin
            (cond ((null? i) #u)
                  ((> k 0) (set marks (cons (tuple (car i) k) (get marks))))
                  ((not (null? m)) (set defined (cons (tuple (car i) (car m)) (get defined))))
                  (else #u))
            (by-internal-each (cdr ns) internal))))))
;; Of a file's macros, `own`, those by the name the importer has them by.
(define internal-name? (->* (symbol) bool)
  (lambda (n)
    (let ((s (symbol->string n)))
      (and (> (string-length s) 8) (string=? (substring s 0 8) "%syntax:")))))
(define internal-macros (->* (macro-env) macro-env)
  (lambda (own)
    (cond ((null? own) nil)
          ((internal-name? (extract (car own) 1)) (cons (car own) (internal-macros (cdr own))))
          (else (internal-macros (cdr own))))))
(define internal-marks (->* (marked) marked)
  (lambda (ms)
    (cond ((null? ms) nil)
          ((internal-name? (extract (car ms) 1)) (cons (car ms) (internal-marks (cdr ms))))
          (else (internal-marks (cdr ms))))))
(define give-each
  (->* (fails mades macro-env marked (listof (tupleof symbol symbol) acyclic)
        (listof filter acyclic) syn names)
       given)
  (lambda (fail made own own-marks internal filter first seen)
    (if (null? made)
        nil
        (let* ((n (extract (car made) 1))
               (twice (if (name-in? n seen)
                          (fail-at fail (string-append "`" (symbol->string n) "` is a macro this "
                                                       "file gives twice")
                                   first)
                          #u))
               (one (if (extract (car made) 2) nil (give-one fail n own own-marks internal filter
                                                             first))))
          (append one (give-each fail (cdr made) own own-marks internal filter first
                                 (cons n seen)))))))
;; Macro `n`, which the file gives, by its own name if `filter` takes it:
;; with the name the importer has it by, in a list of one.
(define give-one
  (->* (fails symbol macro-env marked (listof (tupleof symbol symbol) acyclic)
        (listof filter acyclic) syn)
       given)
  (lambda (fail n own own-marks internal filter first)
    (let ((k (own-mark n own-marks)))
      (begin
        (if (taken? n filter)
            (if (> k 0)
                ;; A trailmark of the file's: bound as its macros are.
                (if (or (macro? n) (> (own-mark n (get marks)) 0))
                    (fail-at fail (string-append "`" (symbol->string n) "` is defined already: "
                                                 "a file's trailmark may not be defined again")
                             first)
                    (set marks (cons (tuple n k) (get marks))))
                (if (macro? n)
                    (fail-at fail (string-append "`" (symbol->string n) "` is a macro defined "
                                                 "already: a file's may not be defined again")
                             first)
                    (set defined (cons (tuple n (car (macro-of n own))) (get defined)))))
            #u)
        (list (tuple n (car (internal-of n internal))))))))
;; The trailmark `n` is in `ms`, defined there, or 0.
(define own-mark (->* (symbol marked) int)
  (lambda (n ms)
    (cond ((null? ms) 0)
          ((symbol=? n (extract (car ms) 1)) (extract (car ms) 2))
          (else (own-mark n (cdr ms))))))

