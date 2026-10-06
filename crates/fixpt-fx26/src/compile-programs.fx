;;; The compiler written in FX-26: inlining, and programs. After
;;; `compile-exps.fx`.

;;; ------------------------------------------------------------- inlining

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define compile-programs-module (module
;; The most parser-tree nodes a body may have to be inlined
;; (`c-inline-room`).
(define c-inline-limit int 20)

(define c-inlines (ref c-inlinables @k) (new nil))

;; The globals whose bodies are being inlined, which are not again.
(define c-inlining (ref syms @k) (new nil))

;; `xs` without `n`'s.
(define c-drop-inline (subr c-builds (c-inlinables symbol) c-inlinables)
  (lambda (xs n)
    (cond ((null? xs) xs)
          ((symbol=? (extract (car xs) 1) n) (c-drop-inline (cdr xs) n))
          (else (the c-inlinables (cons (car xs) (c-drop-inline (cdr xs) n)))))))

;; The most a procedure's body may have to be specialized at a lambda
;; (`c-inline-room`).
(define c-special-limit int 60)

;; A global procedure whose parameter (6) is only called, with (7)
;; arguments, or passed as itself to a call of the procedure: a call with a
;; lambda there may run a copy of the procedure made for that lambda, the
;; lambda's body inlined where the parameter is called (`regcode.fx`'s
;; `r-specialize`). Its name, word, parameters, body and globals, as for
;; `c-inline`.
(define-type c-special
  (productof (1 symbol) (2 tword) (3 c-params) (4 exp) (5 int) (6 int) (7 int)))

(define-type c-specializables (listof c-special acyclic))

(define c-specials (ref c-specializables @k) (new nil))

;; `xs` without `n`'s.
(define c-drop-special (subr c-builds (c-specializables symbol) c-specializables)
  (lambda (xs n)
    (cond ((null? xs) xs)
          ((symbol=? (extract (car xs) 1) n) (c-drop-special (cdr xs) n))
          (else (the c-specializables (cons (car xs) (c-drop-special (cdr xs) n)))))))

;; A procedure being specialized at a lambda: its global's name, cell and
;; word; the parameter's place and name; how many parameters; the lambda's
;; arity, parameters and body, the names its closure captures in order, and
;; the globals it sees.
(define-type c-spec
  (productof (1 symbol) (2 wglobal) (3 tword) (4 int) (5 symbol) (6 int) (7 int)
             (8 c-params) (9 exp) (10 syms) (11 int)))

(define c-spec-now (ref (listof c-spec @k) @k) (new nil))

;; Two arities found: the same one, or -2 if they differ or either failed;
;; -1 is none found yet.
(define c-arity-merge (subr pure (int int) int)
  (lambda (a b) (cond ((or (= a -2) (= b -2)) -2) ((= a -1) b) ((= b -1) a) ((= a b) a) (else -2))))

;; Whether `ns` has `n`.
(define c-names-have? (subr (read @globals) (names symbol) bool)
  (lambda (ns n) (and (not (null? ns)) (or (symbol=? (car ns) n) (c-names-have? (cdr ns) n)))))

;; Whether `x` is `p` or `f`.
(define c-either? (subr (read @globals) (symbol symbol symbol) bool)
  (lambda (x p f) (or (symbol=? x p) (symbol=? x f))))

;; Whether `x` is the variable `p`.
(define c-var-is? (subr (read @globals) (exp symbol) bool)
  (lambda (x p) (tagcase x (e-var (q qa qb) (symbol=? q p)) (else y #f))))

;; The `k`th of `es`.
(define c-nth (subr (read @globals) (exps int) exp)
  (lambda (es k) (if (= k 0) (car es) (c-nth (cdr es) (- k 1)))))

;; How many of `n` parser-tree nodes are left once `x`'s are counted, as the
;; Rust compiler's `inline_room` counts them: negative, and counted no
;; further, once they run out, or at a form that makes a closure, which an
;; inlined body would have to capture its slots in.
(define-rec
  (c-inline-room (subr (maxeff (read @globals) spin) (exp int) int)
    (lambda (x n0)
      (let ((n (- n0 1)))
        (if (< n 0)
            n
            (tagcase x
              (e-lambda (ps body a b) -1)
              (e-rlambda (r l a b) -1)
              (e-letrec (bs body a b) -1)
              (e-prompt (t body h a b) -1)
              (e-module (items a b) -1)
              (e-with (m body a b) -1)
              (e-app (f args a b) (c-inline-room-all args (c-inline-room f n)))
              (e-plambda (d body a b) (c-inline-room body n))
              (e-proj (body ds a b) (c-inline-room body n))
              (e-the (d body a b) (c-inline-room body n))
              (e-convention (cnv body a b) (c-inline-room body n))
              (e-letregion (k r i body a b) (c-inline-room body n))
              (e-if (t th el a b) (c-inline-room-if el (c-inline-room-if th (c-inline-room t n))))
              (e-let (bs body a b) (c-inline-room-if body (c-inline-room-let bs n)))
              (e-begin (es a b) (c-inline-room-all es n))
              (e-bloblet (op i args a b) (c-inline-room-all args n))
              (e-product (fs a b) (c-inline-room-let fs n))
              (e-extract (p l a b) (c-inline-room p n))
              (e-sum (t v a b) (c-inline-room v n))
              (e-tagcase (s arms els a b)
                (c-inline-room-else els (c-inline-room-arms arms (c-inline-room s n))))
              (else y n))))))
  ;; `x`'s nodes counted from `n`, unless none are left.
  (c-inline-room-if (subr (maxeff (read @globals) spin) (exp int) int)
    (lambda (x n) (if (< n 0) n (c-inline-room x n))))
  (c-inline-room-all (subr (maxeff (read @globals) spin) (exps int) int)
    (lambda (es n)
      (if (or (null? es) (< n 0)) n (c-inline-room-all (cdr es) (c-inline-room (car es) n)))))
  (c-inline-room-let (subr (maxeff (read @globals) spin) (c-binds int) int)
    (lambda (bs n)
      (if (or (null? bs) (< n 0))
          n
          (c-inline-room-let (cdr bs) (c-inline-room (extract (car bs) 2) n)))))
  (c-inline-room-arms (subr (maxeff (read @globals) spin) (c-cases int) int)
    (lambda (arms n)
      (if (or (null? arms) (< n 0))
          n
          (c-inline-room-arms (cdr arms) (c-inline-room (extract (car arms) 4) n)))))
  (c-inline-room-else (subr (maxeff (read @globals) spin) (c-binds int) int)
    (lambda (els n) (if (or (null? els) (< n 0)) n (c-inline-room (extract (car els) 2) n)))))

;; Whether `p` is, in `x`, only called, or passed as itself as argument `k`
;; of `n` to a call of `f`, nothing binding either name again, as the Rust
;; compiler's `call_only` says: the arity it is called with (every call the
;; same), -1 if it is not called, or -2 if not so.
(define-rec
  (c-call-only (subr (maxeff (read @globals) spin) (exp symbol symbol int int) int)
    (lambda (x p f k n)
      (tagcase x
        (e-var (m a b) (if (symbol=? m p) -2 -1))
        (e-app (fun args a b)
          (cond ((c-var-is? fun p)
                 (c-arity-merge (c-count-exps args) (c-call-only-all args p f k n)))
                ((and (c-var-is? fun f) (= (c-count-exps args) n) (c-var-is? (c-nth args k) p))
                 (c-call-only-but args p f k n 0))
                (else (c-arity-merge (c-call-only fun p f k n) (c-call-only-all args p f k n)))))
        (e-plambda (d body a b) (c-call-only body p f k n))
        (e-proj (body ds a b) (c-call-only body p f k n))
        (e-the (d body a b) (c-call-only body p f k n))
        (e-convention (cnv body a b) (c-call-only body p f k n))
        (e-letregion (kind r i body a b) (if (c-either? r p f) -2 (c-call-only body p f k n)))
        (e-if (t th el a b)
          (c-arity-merge (c-call-only t p f k n)
                         (c-arity-merge (c-call-only th p f k n) (c-call-only el p f k n))))
        (e-let (bs body a b)
          (c-arity-merge (c-call-only-let bs p f k n) (c-call-only body p f k n)))
        (e-begin (es a b) (c-call-only-all es p f k n))
        (e-bloblet (op i args a b) (c-call-only-all args p f k n))
        (e-product (fs a b) (c-call-only-fields fs p f k n))
        (e-extract (e l a b) (c-call-only e p f k n))
        (e-sum (t v a b) (c-call-only v p f k n))
        (e-tagcase (s arms els a b)
          (c-arity-merge (c-call-only s p f k n)
                         (c-arity-merge (c-call-only-arms arms p f k n)
                                        (c-call-only-else els p f k n))))
        (e-lambda (ps body a b) -2)
        (e-rlambda (r l a b) -2)
        (e-letrec (bs body a b) -2)
        (e-prompt (t body h a b) -2)
        (e-module (items a b) -2)
        (e-with (m body a b) -2)
        (else y -1))))
  (c-call-only-all (subr (maxeff (read @globals) spin) (exps symbol symbol int int) int)
    (lambda (es p f k n)
      (if (null? es)
          -1
          (c-arity-merge (c-call-only (car es) p f k n) (c-call-only-all (cdr es) p f k n)))))
  ;; Every argument but the `k`th; `i` counts.
  (c-call-only-but (subr (maxeff (read @globals) spin) (exps symbol symbol int int int) int)
    (lambda (es p f k n i)
      (cond ((null? es) -1)
            ((= i k) (c-call-only-but (cdr es) p f k n (+ i 1)))
            (else (c-arity-merge (c-call-only (car es) p f k n)
                                 (c-call-only-but (cdr es) p f k n (+ i 1)))))))
  (c-call-only-let (subr (maxeff (read @globals) spin) (c-binds symbol symbol int int) int)
    (lambda (bs p f k n)
      (cond ((null? bs) -1)
            ((c-either? (extract (car bs) 1) p f) -2)
            (else (c-arity-merge (c-call-only (extract (car bs) 2) p f k n)
                                 (c-call-only-let (cdr bs) p f k n))))))
  (c-call-only-fields (subr (maxeff (read @globals) spin) (c-binds symbol symbol int int) int)
    (lambda (fs p f k n)
      (if (null? fs)
          -1
          (c-arity-merge (c-call-only (extract (car fs) 2) p f k n)
                         (c-call-only-fields (cdr fs) p f k n)))))
  (c-call-only-arms
    (subr (maxeff (read @globals) spin) (c-cases symbol symbol int int) int)
    (lambda (arms p f k n)
      (cond ((null? arms) -1)
            ((or (c-names-have? (extract (car arms) 3) p) (c-names-have? (extract (car arms) 3) f))
             -2)
            (else (c-arity-merge (c-call-only (extract (car arms) 4) p f k n)
                                 (c-call-only-arms (cdr arms) p f k n))))))
  (c-call-only-else (subr (maxeff (read @globals) spin) (c-binds symbol symbol int int) int)
    (lambda (els p f k n)
      (cond ((null? els) -1)
            ((c-either? (extract (car els) 1) p f) -2)
            (else (c-call-only (extract (car els) 2) p f k n))))))

;; The first parameter from the `k`th of `ps` that `body` only calls, as
;; `c-call-only` says, and its arity; none if none is.
(define c-first-call-only
  (subr (maxeff (read @globals) (alloc @k) spin) (c-params exp symbol int int)
        (listof (pairof int int @k) @k))
  (lambda (ps body f k n)
    (if (null? ps)
        nil
        (let ((a (c-call-only body (extract (car ps) 1) f k n)))
          (if (>= a 0)
              (the (listof (pairof int int @k) @k) (cons (cons k a) nil))
              (c-first-call-only (cdr ps) body f (+ k 1) n))))))

;; `x`, each `extract` in it that the checker's facts give a field made the
;; `bloblet-ref` of that field, which compiles as it would: for a body kept
;; to be inlined or specialized in a later form, whose facts, keyed by
;; position in its own form's text, are gone by then.
(define-rec
  (c-resolve-extracts (subr c-walks (exp) exp)
    (lambda (x)
      (tagcase x
        (e-lambda (ps body a b) (e-lambda ps (c-resolve-extracts body) a b))
        (e-app (f args a b) (e-app (c-resolve-extracts f) (c-resolve-all args) a b))
        (e-plambda (d body a b) (e-plambda d (c-resolve-extracts body) a b))
        (e-proj (body ds a b) (e-proj (c-resolve-extracts body) ds a b))
        (e-if (t c el a b)
          (e-if (c-resolve-extracts t) (c-resolve-extracts c) (c-resolve-extracts el) a b))
        (e-letrec (bs body a b) (e-letrec (c-resolve-letrec bs) (c-resolve-extracts body) a b))
        (e-let (bs body a b) (e-let (c-resolve-named bs) (c-resolve-extracts body) a b))
        (e-begin (es a b) (e-begin (c-resolve-all es) a b))
        (e-prompt (t body h a b)
          (e-prompt (c-resolve-extracts t) (c-resolve-extracts body) (c-resolve-extracts h) a b))
        (e-letregion (k r p body a b) (e-letregion k r p (c-resolve-extracts body) a b))
        (e-rlambda (r l a b) (e-rlambda (c-resolve-extracts r) (c-resolve-extracts l) a b))
        (e-the (t body a b) (e-the t (c-resolve-extracts body) a b))
        (e-convention (cv body a b) (e-convention cv (c-resolve-extracts body) a b))
        (e-bloblet (op i args a b) (e-bloblet op i (c-resolve-all args) a b))
        (e-product (fs a b) (e-product (c-resolve-named fs) a b))
        (e-extract (p l a b)
          (let ((i (c-field-at a b)) (q (c-resolve-extracts p)))
            (if (< i 0)
                (e-extract q l a b)
                (e-bloblet 'bloblet-ref i (the exps (cons q nil)) a b))))
        (e-sum (t v a b) (e-sum t (c-resolve-extracts v) a b))
        (e-tagcase (s arms els a b)
          (e-tagcase (c-resolve-extracts s) (c-resolve-arms arms) (c-resolve-named els) a b))
        (else y x))))
  (c-resolve-all (subr c-walks (exps) exps)
    (lambda (es)
      (if (null? es) es (the exps (cons (c-resolve-extracts (car es)) (c-resolve-all (cdr es)))))))
  (c-resolve-named (subr c-walks (c-binds) c-binds)
    (lambda (bs)
      (if (null? bs)
          bs
          (let ((x (c-resolve-extracts (extract (car bs) 2))))
            (the c-binds
              (cons (product (1 (extract (car bs) 1)) (2 x)) (c-resolve-named (cdr bs))))))))
  (c-resolve-letrec (subr c-walks (c-recs) c-recs)
    (lambda (bs)
      (if (null? bs)
          bs
          (let ((x (c-resolve-extracts (extract (car bs) 3))))
            (the c-recs
              (cons (product (1 (extract (car bs) 1)) (2 (extract (car bs) 2)) (3 x))
                    (c-resolve-letrec (cdr bs))))))))
  (c-resolve-arms (subr c-walks (c-cases) c-cases)
    (lambda (arms)
      (if (null? arms)
          arms
          (let ((arm (car arms)) (x (c-resolve-extracts (extract (car arms) 4))))
            (the c-cases
              (cons (product (1 (extract arm 1)) (2 (extract arm 2)) (3 (extract arm 3)) (4 x))
                    (c-resolve-arms (cdr arms)))))))))

;; `n`'s definition, of `ps` and `body`, the word compiled last: to be
;; inlined, as it sees the globals seen now.
(define c-inline-of (subr c-builds (symbol c-params exp) c-inline)
  (lambda (n ps body) (product (1 n) (2 (car (get c-last-word))) (3 ps) (4 body) (5 (c-genv-now)))))

;; The same, to be specialized: `found` is the place of the parameter it
;; only calls, and its arity.
(define c-special-of (subr c-builds (symbol c-params exp (pairof int int @k)) c-special)
  (lambda (n ps body found)
    (product (1 n) (2 (car (get c-last-word))) (3 ps) (4 body) (5 (c-genv-now))
             (6 (car found)) (7 (cdr found)))))

;; A definition of `n` as a lambda just compiled: inlined where it is
;; called, if small enough and not calling itself; else, with a parameter it
;; only calls, specialized where it is called with a lambda there. Neither
;; if it calls `stay-cellular`.
(define c-record-inline
  (subr (maxeff c-emits spin) (symbol c-params exp) unit)
  (lambda (n ps unresolved)
    (let ((body (c-resolve-extracts unresolved)))
      (cond ((null? (get c-last-word)) #u)
            ;; Not one that stays cellular, which would make its callers so.
            ((c-mentions? body 'stay-cellular) #u)
            ((and (>= (c-inline-room body c-inline-limit) 0) (not (c-mentions? body n)))
             (set c-inlines (the c-inlinables (cons (c-inline-of n ps body) (get c-inlines)))))
            ((>= (c-inline-room body c-special-limit) 0)
             (let ((found (c-first-call-only ps body n 0 (c-count-params ps))))
               (if (null? found)
                   #u
                   (set c-specials
                        (the c-specializables
                          (cons (c-special-of n ps body (car found)) (get c-specials)))))))
            (else #u)))))

;; The expression compiled last, in a list (for `compile-note-inline!`).
(define c-last-exp (ref (listof exp @k) @k) (new nil))

;; For a driver that computes a definition's value itself (the REPL, in the
;; native convention), right after compiling `(lambda () init)`: if `init`
;; is a lambda, `n`'s definition as `c-tops` would note it, to be inlined
;; where it is called. Its word is the one compiled before the thunk's.
(define compile-note-inline! (subr (maxeff c-emits spin) (symbol) unit)
  (lambda (n)
    (let ((x (get c-last-exp)) (w (get c-prev-word)))
      (if (null? x)
          #u
          (tagcase (car x)
            (e-lambda (ps0 thunk a b)
              (let ((l (c-lambda-of thunk)))
                (if (null? l)
                    #u
                    (tagcase (car l)
                      (e-lambda (ps body la lb)
                        (begin (set c-inlines (c-drop-inline (get c-inlines) n))
                               (set c-specials (c-drop-special (get c-specials) n))
                               (set c-last-word w)
                               (c-record-inline n ps body)))
                      (else y #u)))))
            (else y #u))))))

;; Globals kept for their names' next definitions: a redefinition of a type
;; the old one's users can take, for which the REPL asks
;; (`compile-keep-global!`).
(define-type c-kept-globals (listof (pairof symbol wglobal acyclic) acyclic))

(define c-reuse (ref c-kept-globals @k) (new nil))
;; For a driver: a whole program from here, which sees none of the globals
;; made before it, as its checker begins again.
(define compile-forget-globals!
  (subr (maxeff (read (globals c-genv-index c-reuse make-table symbol-hash)) (write @k) (alloc @k))
        () unit)
  (lambda ()
    (begin (set c-genv-index (make-table symbol-hash symbol=?)) (set c-reuse nil))))

;; The global kept for `n`, if any.
(define c-kept (subr (read @globals) (c-kept-globals symbol) (listof wglobal acyclic))
  (lambda (ks n)
    (cond ((null? ks) nil)
          ((symbol=? (car (car ks)) n) (the (listof wglobal acyclic) (cons (cdr (car ks)) nil)))
          (else (c-kept (cdr ks) n)))))

;; `ks` without `n`'s.
(define c-unkeep (subr (read @globals) (c-kept-globals symbol) c-kept-globals)
  (lambda (ks n)
    (cond ((null? ks) ks)
          ((symbol=? (car (car ks)) n) (c-unkeep (cdr ks) n))
          (else (the c-kept-globals (cons (car ks) (c-unkeep (cdr ks) n)))))))

;; The counts of globals the bodies that may yet be inlined (`xs`), or
;; specialized (`ys`), saw when they were written: the limits a lookup of a
;; global may be made at (`c-global-find`) as definitions are made, when no
;; inlining or specialization is under way.
(define c-inline-limits (subr c-builds (c-inlinables) (listof int acyclic))
  (lambda (xs) (if (null? xs) nil (cons (extract (car xs) 5) (c-inline-limits (cdr xs))))))
(define c-special-limits (subr c-builds (c-specializables) (listof int acyclic))
  (lambda (ys) (if (null? ys) nil (cons (extract (car ys) 5) (c-special-limits (cdr ys))))))
;; `xs` before `ys`.
(define c-ints-onto (subr c-builds ((listof int acyclic) (listof int acyclic)) (listof int acyclic))
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (c-ints-onto (cdr xs) ys)))))
(define c-genv-limits (subr c-builds () (listof int acyclic))
  (lambda () (c-ints-onto (c-inline-limits (get c-inlines)) (c-special-limits (get c-specials)))))
;; Whether one of `limits` is past `lo` and no more than `hi`.
(define c-limit-in? (subr c-builds ((listof int acyclic) int int) bool)
  (lambda (limits lo hi)
    (and (not (null? limits))
         (or (and (< lo (car limits)) (<= (car limits) hi)) (c-limit-in? (cdr limits) lo hi)))))
;; Of `es`, a name's globals, newest first, each older than the one made
;; `upper`th: those a lookup at one of `limits` still finds. A lookup at
;; limit L finds the newest made before L, so a global made `i`th is found
;; only by a limit past `i` and no more than the next newer one's: kept,
;; any other would hold its value, and what that reaches, for good.
(define c-genv-needed (subr c-builds (c-globals-made int (listof int acyclic)) c-globals-made)
  (lambda (es upper limits)
    (if (null? es)
        nil
        (let ((i (car (car es))) (rest (c-genv-needed (cdr es) (car (car es)) limits)))
          (if (c-limit-in? limits i upper) (the c-globals-made (cons (car es) rest)) rest)))))
;; `n`'s globals, before its `i`th is made: those no lookup can find let go.
(define c-genv-prune! (subr c-emits (symbol int) unit)
  (lambda (n i)
    (let ((made (table-ref (get c-genv-index) n nil)))
      (table-set! (get c-genv-index) n (c-genv-needed made i (c-genv-limits))))))
;; `n`'s global for a definition of it: the one kept for it, if one was;
;; else a new one, which later uses of `n` refer to.
(define c-push-global (subr c-emits (symbol) wglobal)
  (lambda (n)
    (let ((kept (begin (set c-inlines (c-drop-inline (get c-inlines) n))
                       (set c-specials (c-drop-special (get c-specials) n))
                       (c-kept (get c-reuse) n))))
      (if (null? kept)
          (let ((g (make-global n)) (i (get c-genv-count)))
            (begin (c-genv-prune! n i)
                   (c-genv-push! n i g)
                   (set c-genv-count (+ i 1))
                   g))
          (begin (set c-reuse (c-unkeep (get c-reuse) n)) (car kept))))))

;; For a driver: `n`'s next definition keeps the global `n` has now, so
;; that every use of `n`, before it and after, sees the new value.
(define compile-keep-global! (subr (maxeff c-emits spin) (symbol) unit)
  (lambda (n)
    (let ((l (c-global-find n -1)))
      (if (null? l)
          #u
          (tagcase (car l)
            (at-global (g) (set c-reuse (the c-kept-globals (cons (cons n g) (get c-reuse)))))
            (else y #u))))))

;; For a driver that computes a definition's value itself (the REPL, in the
;; native convention): `n`'s global from now on, made, for the driver to
;; fill.
(define compile-new-global (subr c-emits (symbol) wglobal)
  (lambda (n) (c-push-global n)))

;; For a driver that makes a global's value native code (the REPL, in the
;; native convention): `n`'s global, in a list, if it is one.
(define compile-global-cell (subr c-walks (symbol) (listof wglobal @k))
  (lambda (n)
    (let ((l (c-global-find n -1)))
      (if (null? l)
          nil
          (tagcase (car l)
            (at-global (g) (cons g nil))
            (else y nil))))))

;;; ------------------------------------------------------------- programs

(define c-rec-globals (subr c-emits (c-recs) (listof wglobal @k))
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((g (c-push-global (extract (car bs) 1)))) (cons g (c-rec-globals (cdr bs)))))))

;; The next lambda's word named for global `n`.
(define c-name-word! (subr c-emits (symbol) unit)
  (lambda (n) (set c-word-name (the (listof string @k) (cons (symbol->string n) nil)))))
;; The next lambda's word named for global `n`, when `x`, its definition, is
;; a lambda, rather than for where its body starts: so that a profile, a
;; disassembly or a fault says which procedure. As the Rust compiler's
;; `name_word_for`.
(define c-name-for! (subr c-emits (symbol exp) unit)
  (lambda (n x)
    (let ((l (c-lambda-of x)))
      (if (null? l)
          #u
          (tagcase (car l)
            (e-lambda (ps body a b) (c-name-word! n))
            (else y #u))))))
(define c-rec-fill (subr (maxeff compiles spin) (c-recs (listof wglobal @k) code) unit)
  (lambda (bs gs c)
    (if (null? bs)
        #u
        (begin (c-name-for! (extract (car bs) 1) (extract (car bs) 3))
               (c-plan-top (extract (car bs) 3))
               (c-exp (extract (car bs) 3) (the cenv nil) 0 c #f)
               (c-op1 c routine-global! (wcell-global (car gs)))
               (c-rec-fill (cdr bs) (cdr gs) c)))))

;; The lambda of `ps` and `body` that top-level definition `n` is, made at
;; the top level, and noted to be inlined or specialized.
(define c-define-lambda (subr (maxeff compiles spin) (symbol c-params exp code) unit)
  (lambda (n ps body c)
    (begin (set c-defining (the (listof symbol @k) (cons n nil)))
           (c-name-word! n)
           (c-lambda ps body (the cenv nil) 0 c (the syms nil) (the c-region nil))
           (set c-defining (the (listof symbol @k) nil))
           (c-record-inline n ps body))))

;; Each top-level module's members noted (`c-module-members`), by its
;; global, as the Rust compiler's `modules` (`TODO.md` §38).
(define-type c-module-list (listof (productof (1 symbol) (2 c-inlinables)) acyclic))
(define c-modules (ref c-module-list @k) (new nil))
(define c-modules-without (subr c-builds (c-module-list symbol) c-module-list)
  (lambda (ms m)
    (cond ((null? ms) ms)
          ((symbol=? (extract (car ms) 1) m) (c-modules-without (cdr ms) m))
          (else (the c-module-list (cons (car ms) (c-modules-without (cdr ms) m)))))))
;; Whether `x` is a `module` form.
(define c-module? (subr (read @globals) (exp) bool)
  (lambda (x) (tagcase x (e-module (items a b) #t) (else y #f))))
;; After `(define m (module …))` is compiled: its members noted, kept by `m`.
(define c-keep-module! (subr c-emits (symbol) unit)
  (lambda (m)
    (let ((ms (get c-module-members)))
      (begin (set c-module-members nil)
             (if (null? ms)
                 #u
                 (let ((entry (product (1 m) (2 (car ms)))))
                   (set c-modules (the c-module-list (cons entry (get c-modules))))))))))
;; The members `m`, a top-level module, has noted, or none.
(define c-members-of (subr c-builds (c-module-list symbol) c-inlinables)
  (lambda (ms m)
    (cond ((null? ms) nil)
          ((symbol=? (extract (car ms) 1) m) (extract (car ms) 2))
          (else (c-members-of (cdr ms) m)))))
;; `n`, a re-export of member `f` of `ms`: inlined where called as `f` is,
;; if small, not calling itself and not staying cellular.
(define c-alias-inline! (subr (maxeff c-emits spin) (symbol symbol c-inlinables) unit)
  (lambda (n f ms)
    (cond ((null? ms) #u)
          ((symbol=? (extract (car ms) 1) f)
           (let* ((it (car ms)) (body (c-resolve-extracts (extract it 4))))
             (if (and (not (c-mentions? body 'stay-cellular))
                      (>= (c-inline-room body c-inline-limit) 0)
                      (not (c-mentions? body f)))
                 (let ((alias (product (1 n) (2 (extract it 2)) (3 (extract it 3)) (4 body)
                                       (5 (extract it 5)))))
                   (set c-inlines (the c-inlinables (cons alias (get c-inlines)))))
                 #u)))
          (else (c-alias-inline! n f (cdr ms))))))
;; `(define n (with m f))`, `m` a top-level module whose member `f` is a
;; lambda naming no other member: `n` inlined where called, as the Rust
;; compiler's `reexport_inline`.
(define c-reexport-inline! (subr (maxeff c-emits spin) (symbol exp) unit)
  (lambda (n x)
    (tagcase x
      (e-with (m body a b)
        (tagcase body
          (e-var (f fa fb) (c-alias-inline! n f (c-members-of (get c-modules) m)))
          (else y #u)))
      (else y #u))))
;; Each form in turn; the last expression's value is left on the stack.
(define c-tops (subr (maxeff compiles spin) ((listof top acyclic) code bool) bool)
  (lambda (ts c has-value)
    (if (null? ts)
        has-value
        (tagcase (car ts)
          (t-define (n ty x a b)
            (begin
              (if has-value (c-op c routine-drop) #u)
              ;; A module defined again no longer says what its re-exports are.
              (set c-modules (c-modules-without (get c-modules) n))
              (c-plan-top x)
              (if (or (null? ty) (null? (c-lambda-of x)))
                  (begin (if (c-module? x)
                             (set c-module-members (the (listof c-inlinables @k) (list nil)))
                             #u)
                         (c-exp x (the cenv nil) 0 c #f)
                         (if (c-module? x) (c-keep-module! n) #u)
                         ;; After its global, which forgets what `n` was.
                         (let ((g (c-push-global n)))
                           (begin (c-reexport-inline! n x)
                                  (c-op1 c routine-global! (wcell-global g)))))
                  ;; A lambda: its global first, so that it can call itself,
                  ;; through the global, as any use of it does
                  ;; (`docs/fx26.md`, "Redefinition").
                  (let ((g (c-push-global n)))
                    (begin (tagcase (car (c-lambda-of x))
                             (e-lambda (ps body la lb) (c-define-lambda n ps body c))
                             (else y (c-exp x (the cenv nil) 0 c #f)))
                           (c-op1 c routine-global! (wcell-global g)))))
              (c-tops (cdr ts) c #f)))
          ;; Every name's global first; then each lambda, which runs nothing.
          (t-define-rec (bs a b)
            (begin
              (if has-value (c-op c routine-drop) #u)
              (c-rec-fill bs (c-rec-globals bs) c)
              (c-tops (cdr ts) c #f)))
          (t-exp (x)
            (begin (if has-value (c-op c routine-drop) #u)
                   (set c-last-exp (the (listof exp @k) (cons x nil)))
                   (c-plan-top x)
                   (c-exp x (the cenv nil) 0 c #f)
                   (c-tops (cdr ts) c #t)))
          (else y (c-tops (cdr ts) c has-value))))))

;; Each of `bs`' names' next definition keeps the global it has.
(define c-keep-rec-names (subr (maxeff c-emits spin) (c-recs) unit)
  (lambda (bs)
    (if (null? bs)
        #u
        (begin (compile-keep-global! (extract (car bs) 1)) (c-keep-rec-names (cdr bs))))))

;; Before a run that assigns its names' globals (`checked-tops`): each
;; name's next definition keeps the global it has.
(define c-keep-names (subr (maxeff c-emits spin) (top) unit)
  (lambda (t)
    (tagcase t
      (t-define (n ty x a b) (compile-keep-global! n))
      (t-define-rec (bs a b) (c-keep-rec-names bs))
      (else y #u))))

;; What a checked program runs (`checked-tops`), each in turn: whether the
;; last was an expression, whose value stays.
(define c-runs (subr (maxeff compiles spin) ((listof k-run acyclic) code bool) bool)
  (lambda (rs c has-value)
    (if (null? rs)
        has-value
        (let* ((r (car rs)) (tops (the (listof top acyclic) (cons (extract r 1) nil))))
          (begin (if (extract r 2) (c-keep-names (extract r 1)) #u)
                 (c-runs (cdr rs) c (c-tops tops c has-value)))))))

;; A program's one word, which runs it and leaves the value of its last
;; expression (unit, if it has none): what `forms` compiles onto the code
;; it is given, saying whether the last form was an expression; `facts`,
;; what checking found.
(define c-program
  (subr (maxeff compiles (comefrom @y) spin) ((subr (maxeff compiles spin) (code) bool) k-facts)
        cresult)
  (lambda (forms facts)
    (prompt c-tag
      (let ((c (the code (new nil))))
        (begin
          (c-set-facts! facts)
          (set c-this-params -1)
          ;; The lambdas made so far are the last program's: let them go.
          (set c-made-now (the (listof c-made @k) nil))
          (set c-made-reuse (the (listof c-made @k) nil))
          (if (forms c) #u (c-lit c (wcell-unit)))
          (c-op c routine-exit)
          (c-ok (c-assemble c (string->symbol "program")))))
      (lambda (r) r))))

;; The entry point for a program the checker written in FX-26 checked: what
;; it runs (`checked-tops`, under redefinition), and what checking found.
(define compile-checked
  (subr (maxeff compiles (comefrom @y) spin) ((listof k-run acyclic) k-facts) cresult)
  (lambda (runs facts) (c-program (lambda (c) (c-runs runs c #f)) facts)))

;; The entry point: a checked program's trees, and what checking found.
(define compile-program
  (subr (maxeff compiles (comefrom @y) spin) ((listof top acyclic) k-facts) cresult)
  (lambda (tops facts) (c-program (lambda (c) (c-tops tops c #f)) facts)))))

(define c-inline-limit (with compile-programs-module c-inline-limit))
(define c-inlines (with compile-programs-module c-inlines))
(define c-inlining (with compile-programs-module c-inlining))
(define-type c-special (select compile-programs-module c-special))
(define c-specials (with compile-programs-module c-specials))
(define-type c-spec (select compile-programs-module c-spec))
(define c-spec-now (with compile-programs-module c-spec-now))
(define c-nth (with compile-programs-module c-nth))
(define c-inline-room (with compile-programs-module c-inline-room))
(define compile-note-inline! (with compile-programs-module compile-note-inline!))
(define compile-forget-globals! (with compile-programs-module compile-forget-globals!))
(define compile-keep-global! (with compile-programs-module compile-keep-global!))
(define compile-new-global (with compile-programs-module compile-new-global))
(define compile-global-cell (with compile-programs-module compile-global-cell))
(define compile-checked (with compile-programs-module compile-checked))
(define compile-program (with compile-programs-module compile-program))
