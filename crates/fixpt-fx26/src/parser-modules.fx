;;; The FX-26 parser, in FX-26: a module's typed lambda definitions see
;;; their own names (`TODO.md` §37), as a typed `define` of a lambda does at
;;; the top level, as the Rust parser's `module_own_names` (`modorder.rs`)
;;; makes them, step for step: each one whose value names itself becomes a
;;; `define-rec` of one, which everything after the parser knows. Otherwise
;;; a module's definitions are in order, each seeing those before it. After
;;; `parser-load.fx`; it sets `module-own-names`, which `parser.fx` and
;;; `parser-load.fx` call.

(define-effect orders (maxeff parses spin))
;; The parts of trees the walk goes through.
(define-type mo-exps (listof exp acyclic))
(define-type mo-recs (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic))
(define-type mo-lets (listof (productof (1 symbol) (2 exp)) acyclic))
(define-type mo-arms (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic))
(define-type mo-params (listof (productof (1 symbol) (2 syns-a)) acyclic))

;;; ------------------------------------------------------------ free names

(define mo-has? (subr (read @globals) (names symbol) bool)
  (lambda (ns n) (and (not (null? ns)) (or (symbol=? (car ns) n) (mo-has? (cdr ns) n)))))
;; `out` (newest first) with `n`, if it is neither bound nor there.
(define mo-note (subr tree-builds (symbol names names) names)
  (lambda (n bound out) (if (or (mo-has? bound n) (mo-has? out n)) out (the names (cons n out)))))
(define mo-onto (subr tree-builds (names names) names)
  (lambda (xs ys) (if (null? xs) ys (mo-onto (cdr xs) (the names (cons (car xs) ys))))))
;; A module's items' names, a generative type's conversions among them.
(define mo-item-names (subr orders (mod-item) names)
  (lambda (it)
    (let ((k (extract it 1)) (ns (extract it 2)))
      (cond ((= k 0)
             (let ((s (symbol->string (car ns))))
               (the names (list (string->symbol (string-append "up-" s))
                                (string->symbol (string-append "down-" s))))))
            ((or (= k 2) (= k 3)) ns)
            (else nil)))))
(define mo-items-names (subr orders (mod-items) names)
  (lambda (items)
    (if (null? items) nil (mo-onto (mo-item-names (car items)) (mo-items-names (cdr items))))))

(define mo-param-names (subr tree-builds (mo-params names) names)
  (lambda (ps bound)
    (if (null? ps) bound (mo-param-names (cdr ps) (the names (cons (extract (car ps) 1) bound))))))
(define mo-letrec-names (subr tree-builds (mo-recs names) names)
  (lambda (bs bound)
    (if (null? bs) bound (mo-letrec-names (cdr bs) (the names (cons (extract (car bs) 1) bound))))))
(define mo-let-names (subr tree-builds (mo-lets names) names)
  (lambda (bs bound)
    (if (null? bs) bound (mo-let-names (cdr bs) (the names (cons (extract (car bs) 1) bound))))))
;; The names free in `x`, newest first, syntactically, as `free_names`: a
;; `lambda`, `let`, `letrec` and `tagcase` arm bind theirs; a `with` binds
;; none, its module's name one of them; a module inside binds its items'.
(define-rec
  (mo-free (subr orders (exp names names) names)
    (lambda (x bound out)
      (tagcase x
        (e-var (n a b) (mo-note n bound out))
        (e-lambda (ps body a b) (mo-free body (mo-param-names ps bound) out))
        (e-app (f args a b) (mo-free-all args bound (mo-free f bound out)))
        (e-plambda (d body a b) (mo-free body bound out))
        (e-proj (body ds a b) (mo-free body bound out))
        (e-letregion (k r i body a b) (mo-free body bound out))
        (e-the (d body a b) (mo-free body bound out))
        (e-convention (cnv body a b) (mo-free body bound out))
        (e-rlambda (r l a b) (mo-free l bound (mo-free r bound out)))
        (e-if (t th el a b) (mo-free el bound (mo-free th bound (mo-free t bound out))))
        (e-letrec (bs body a b)
          (let ((inner (mo-letrec-names bs bound)))
            (mo-free body inner (mo-free-letrec bs inner out))))
        (e-let (bs body a b)
          (mo-free body (mo-let-names bs bound) (mo-free-let bs bound out)))
        (e-begin (es a b) (mo-free-all es bound out))
        (e-prompt (t body h a b) (mo-free h bound (mo-free body bound (mo-free t bound out))))
        (e-bloblet (op i args a b) (mo-free-all args bound out))
        (e-product (fs a b) (mo-free-let fs bound out))
        (e-extract (p l a b) (mo-free p bound out))
        (e-sum (t v a b) (mo-free v bound out))
        (e-tagcase (s arms els a b)
          (mo-free-else els bound (mo-free-arms arms bound (mo-free s bound out))))
        (e-module (items a b)
          (mo-free-items items (mo-onto (mo-items-names items) bound) out))
        (e-with (m body a b) (mo-free body bound (mo-note m bound out)))
        (else y out))))
  (mo-free-all (subr orders (mo-exps names names) names)
    (lambda (xs bound out)
      (if (null? xs) out (mo-free-all (cdr xs) bound (mo-free (car xs) bound out)))))
  (mo-free-letrec (subr orders (mo-recs names names) names)
    (lambda (bs bound out)
      (if (null? bs) out (mo-free-letrec (cdr bs) bound (mo-free (extract (car bs) 3) bound out)))))
  (mo-free-let (subr orders (mo-lets names names) names)
    (lambda (bs bound out)
      (if (null? bs) out (mo-free-let (cdr bs) bound (mo-free (extract (car bs) 2) bound out)))))
  (mo-free-arms (subr orders (mo-arms names names) names)
    (lambda (arms bound out)
      (if (null? arms)
          out
          (let ((arm (car arms)))
            (mo-free-arms (cdr arms) bound
                          (mo-free (extract arm 4) (mo-onto (extract arm 3) bound) out))))))
  (mo-free-else (subr orders (mo-lets names names) names)
    (lambda (els bound out)
      (if (null? els)
          out
          (mo-free (extract (car els) 2) (the names (cons (extract (car els) 1) bound)) out))))
  (mo-free-items (subr orders (mod-items names names) names)
    (lambda (items bound out)
      (if (null? items)
          out
          (let ((k (extract (car items) 1)))
            (mo-free-items (cdr items) bound
                           (if (or (= k 0) (= k 2) (= k 3))
                               (mo-free-all (extract (car items) 4) bound out)
                               out)))))))
;; The names free in `x`, in the order first met.
(define mo-names-of (subr orders (exp) names)
  (lambda (x) (reverse (mo-free x nil nil))))
;; Whether `x` is a lambda, under `plambda` and `the`: the checker's
;; `is_lambda`, what a `define-rec`'s members must be.
(define mo-lambda? (subr (read @globals) (exp) bool)
  (lambda (x)
    (tagcase x
      (e-plambda (d body a b) (mo-lambda? body))
      (e-the (d body a b) (mo-lambda? body))
      (e-lambda (ps body a b) #t)
      (e-rlambda (r l a b) #t)
      (else y #f))))
;; `it`, a typed lambda definition naming itself, a `define-rec` of one;
;; anything else as it is.
(define mo-own-name (subr orders (mod-item) mod-item)
  (lambda (it)
    (if (and (= (extract it 1) 2)
             (not (null? (extract it 3)))
             (mo-lambda? (car (extract it 4)))
             (mo-has? (mo-names-of (car (extract it 4))) (car (extract it 2))))
        (product (1 3) (2 (extract it 2)) (3 (extract it 3)) (4 (extract it 4)))
        it)))
(define mo-own-names (subr orders (mod-items) mod-items)
  (lambda (items)
    (if (null? items)
        nil
        (the mod-items (cons (mo-own-name (car items)) (mo-own-names (cdr items)))))))
(set module-own-names mo-own-names)
