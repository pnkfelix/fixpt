;;; The compiler written in FX-26: inlining, what it knows of each global
;;; procedure small enough to inline, or to specialize at known arguments.
;;; After `compile-exps.fx` and `compile-plan.fx`; `compile-programs.fx`
;;; uses it (split from that file, `TODO.md` §68).

;;; ------------------------------------------------------------- inlining

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define compile-inline-module (module
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

;; `x`, each `(with #%fx n)` in it that the checker found the plain `n`
;; (the fact -502) made that `n`, at the `with`'s place: what the Rust
;; checker gives its compilers (`Arena::replace`, `TODO.md` §46). Only the
;; forms of a program that has such a fact are walked.
(define-rec
  (c-plain-fx (subr c-walks (exp) exp)
    (lambda (x)
      (tagcase x
        (e-with (m body a b)
          (tagcase body
            (e-var (n c d) (if (c-plain-fx-at a b) (e-var n a b) x))
            (else y (e-with m (c-plain-fx body) a b))))
        (e-module (items a b) (e-module (c-plain-items items) a b))
        (e-lambda (ps body a b) (e-lambda ps (c-plain-fx body) a b))
        (e-app (f args a b) (e-app (c-plain-fx f) (c-plain-all args) a b))
        (e-plambda (d body a b) (e-plambda d (c-plain-fx body) a b))
        (e-proj (body ds a b) (e-proj (c-plain-fx body) ds a b))
        (e-if (t c el a b) (e-if (c-plain-fx t) (c-plain-fx c) (c-plain-fx el) a b))
        (e-letrec (bs body a b) (e-letrec (c-plain-recs bs) (c-plain-fx body) a b))
        (e-let (bs body a b) (e-let (c-plain-named bs) (c-plain-fx body) a b))
        (e-begin (es a b) (e-begin (c-plain-all es) a b))
        (e-prompt (t body h a b) (e-prompt (c-plain-fx t) (c-plain-fx body) (c-plain-fx h) a b))
        (e-letregion (k r p body a b) (e-letregion k r p (c-plain-fx body) a b))
        (e-rlambda (r l a b) (e-rlambda (c-plain-fx r) (c-plain-fx l) a b))
        (e-the (t body a b) (e-the t (c-plain-fx body) a b))
        (e-convention (cv body a b) (e-convention cv (c-plain-fx body) a b))
        (e-bloblet (op i args a b) (e-bloblet op i (c-plain-all args) a b))
        (e-product (fs a b) (e-product (c-plain-named fs) a b))
        (e-extract (p l a b) (e-extract (c-plain-fx p) l a b))
        (e-sum (t v a b) (e-sum t (c-plain-fx v) a b))
        (e-tagcase (s arms els a b)
          (e-tagcase (c-plain-fx s) (c-plain-arms arms) (c-plain-named els) a b))
        (else y x))))
  (c-plain-all (subr c-walks (exps) exps)
    (lambda (es)
      (if (null? es) es (the exps (cons (c-plain-fx (car es)) (c-plain-all (cdr es)))))))
  (c-plain-named (subr c-walks (c-binds) c-binds)
    (lambda (bs)
      (if (null? bs)
          bs
          (let ((x (c-plain-fx (extract (car bs) 2))))
            (the c-binds
              (cons (product (1 (extract (car bs) 1)) (2 x)) (c-plain-named (cdr bs))))))))
  (c-plain-recs (subr c-walks (c-recs) c-recs)
    (lambda (bs)
      (if (null? bs)
          bs
          (let ((b (car bs)))
            (the c-recs
              (cons (product (1 (extract b 1)) (2 (extract b 2)) (3 (c-plain-fx (extract b 3))))
                    (c-plain-recs (cdr bs))))))))
  (c-plain-items (subr c-walks (mod-items) mod-items)
    (lambda (items)
      (if (null? items)
          items
          (let ((it (car items)))
            (the mod-items
              (cons (product (1 (extract it 1)) (2 (extract it 2)) (3 (extract it 3))
                             (4 (c-plain-all (extract it 4))))
                    (c-plain-items (cdr items))))))))
  (c-plain-arms (subr c-walks (c-cases) c-cases)
    (lambda (arms)
      (if (null? arms)
          arms
          (let ((arm (car arms)))
            (the c-cases
              (cons (product (1 (extract arm 1)) (2 (extract arm 2)) (3 (extract arm 3))
                             (4 (c-plain-fx (extract arm 4))))
                    (c-plain-arms (cdr arms)))))))))

;; A top-level form, as `c-plain-fx` makes its expressions.
(define c-plain-top (subr c-walks (top) top)
  (lambda (t)
    (if (= (table-count (get c-plain-table)) 0)
        t
        (tagcase t
          (t-define (n ty x a b) (t-define n ty (c-plain-fx x) a b))
          (t-define-rec (bs a b) (t-define-rec (c-plain-recs bs) a b))
          (t-exp (x) (t-exp (c-plain-fx x)))
          (else y t)))))

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
             (c-note-inline! (c-inline-of n ps body)))
            ((>= (c-inline-room body c-special-limit) 0)
             (let ((found (c-first-call-only ps body n 0 (c-count-params ps))))
               (if (null? found)
                   #u
                   (set c-specials
                        (the c-specializables
                          (cons (c-special-of n ps body (car found)) (get c-specials)))))))
            (else #u))
      (c-note-unroll! n ps body))))
;; Small and calling itself: unrolled where called with a constant list, as
;; the Rust compiler's `unrolls` (`TODO.md` §44).
(define c-note-unroll! (subr (maxeff c-emits spin) (symbol c-params exp) unit)
  (lambda (n ps body)
    (if (and (not (null? (get c-last-word)))
             (and (c-mentions? body n)
                  (and (>= (c-inline-room body c-inline-limit) 0)
                       (not (c-mentions? body 'stay-cellular)))))
        (table-set! (get c-unrolls) n
                    (the c-inlinables (cons (c-inline-of n ps body) (c-unrolls-of n))))
        #u)))

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
                        (begin (c-forget-inline! n)
                               (table-set! (get c-unrolls) n nil)
                               (set c-specials (c-drop-special (get c-specials) n))
                               (set c-last-word w)
                               (c-record-inline n ps body)))
                      (else y #u)))))
            (else y #u))))))))

(define c-last-exp (with compile-inline-module c-last-exp))
(define c-plain-top (with compile-inline-module c-plain-top))
(define c-record-inline (with compile-inline-module c-record-inline))
(define c-resolve-extracts (with compile-inline-module c-resolve-extracts))
(define compile-note-inline! (with compile-inline-module compile-note-inline!))
