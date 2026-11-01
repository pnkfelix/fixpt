;;; The FX-26 evaluator proper: the parser's trees, run. After
;;; `eval-values.fx`, `eval-prims.fx` and `eval-bloblets.fx`.
;;;
;;; An environment is a list of each name and the cell that holds its value,
;;; newest first; a closure is a procedure of the host's, closing over the
;;; environment it was made in, globals included: a top-level form runs in
;;; the global environment as it stands then, so a second `define` of a name
;;; shadows the first, and code before it keeps the first, as the lowering
;;; to Scheme does (`lower::Globals`). Descriptions are not needed to run a
;;; program, so they are passed over.
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor (`conductor.fx`) applies to the evaluator's
;;; values and primitives, and the checker's environment and resolution.

;; Its types, and the signatures of what it is given (`eval-types.fx`).
(let* ((eval-types (load-module "fx26:eval-types.fx"))
       ;; The types of the trees it runs, and of what the checker says of them.
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx")))
  ;; What it is given: the evaluator's values and primitives, and the
  ;; checker's environment (`check-env.fx`) and resolution (`check-resolve.fx`).
  ;; And the reader's and the parser's entries, for `stage` (`ev-stage`).
  (lambda ((values (select eval-types eval-values-sig))
           (prims (select eval-types eval-prims-sig))
           (bloblets (select eval-types eval-bloblets-sig))
           (env (select check-env-types check-env-sig))
           (resolve (select check-resolve-types check-resolve-sig))
           (read-text (subr (select eval-types evals) (string int)
                            (listof (listof (select parser-types syn) acyclic) acyclic)))
           (parse (subr (select eval-types evals) ((listof (select parser-types syn) acyclic))
                        (select parser-types presult))))
    (module
(hide (include eval-types) (include parser-types) (include check-env-types)
      (include check-resolve-types) (include check-types-types) (include check-subst-types))
;; What it uses of the modules it is given.
(import values apply-val apply1 ev-poll as-bool as-fields as-other as-str as-tag efail
        efail-expected ev-eq? eval-tag show-val the-unit)
(import prims prim! standard)
(import bloblets ev-bloblet ev-bref ev-blobref ev-flat-tag ev-label-is?)
;; What it uses of the modules it is given: all of each, hidden.
(hide (include env) (include resolve))

;; The global environment, newest first.
(define genv (ref env @v) (new nil))

(define cell (->* (val) vcell) (lambda (v) (new v)))

;;; ------------------------------------------------------------------- stage
;; `stage` (`docs/research/eval.md`), which this runs itself: the code, a
;; datum the program made, written out and checked by the checker written
;; in Rust (`%stage-check`) against what the checker noted at it
;; (`n-staged`); then read, parsed and run here, in no environment but the
;; standard one, and the procedure it makes given the module (`ev-stage`).

;; What the checker noted at the code at `a` `b` `k`: `fresh` or "" (a
;; `reify-region`'s of a region of its own), the names of the variables
;; whose evidence it is given, and what the code is checked as (or a
;; `reify-…` makes evidence of), as a rep (or `#f`), in a list of one;
;; none if nothing.
(define ev-staged-in
  (->* (k-facts int int int) (listof (productof (1 string) (2 string) (3 wcell)) acyclic))
  (lambda (fs a b k)
    (cond ((null? fs) nil)
          ((ev-at-is? (extract (car fs) 1) a b k)
           (tagcase (extract (car fs) 2)
             (n-staged (fr ns rp) (cons (product (1 fr) (2 ns) (3 rp)) nil))
             (else y (ev-staged-in (cdr fs) a b k))))
          (else (ev-staged-in (cdr fs) a b k)))))

;; Datum `v` written as the reader reads it, pieces in reverse onto `acc`;
;; or not, if it is not code (a procedure, say).
(define-type ev-code (sumof (text (listof string acyclic)) (not-code unit)))
(define ev-code-pieces (->* (val (listof string acyclic)) ev-code)
  (lambda (v acc)
    (typecase v
      (int n (sum text (cons (int->string n) acc)))
      (bool b (sum text (cons (if b "#t" "#f") acc)))
      (string s (sum text (cons (ev-string-text s) acc)))
      (char c (sum text (cons (string-append "#\\x" (ev-hex (char->integer c))) acc)))
      (symbol s (sum text (cons (symbol->string s) acc)))
      (keyword k (sum text (cons (string-append "#:" (symbol->string (keyword->symbol k))) acc)))
      (nil z (sum text (cons "()" acc)))
      (f64 x (sum text (cons (f64->string x) acc)))
      (pair p (ev-code-list p (cons "(" acc)))
      (else y (sum not-code #u)))))
(define ev-code-list (->* ((pairof val val @v) (listof string acyclic)) ev-code)
  (lambda (p acc)
    (tagcase (ev-code-pieces (car p) acc)
      (text acc
        (let ((tail (cdr p)))
          (typecase tail
            (nil z (sum text (cons ")" acc)))
            (pair q (ev-code-list q (cons " " acc)))
            (else y (tagcase (ev-code-pieces tail (cons " . " acc))
                      (text acc (sum text (cons ")" acc)))
                      (not-code u (sum not-code #u)))))))
      (not-code u (sum not-code #u)))))
(define ev-string-text (->* (string) string)
  (lambda (s)
    (letrec ((go (subr spin (int (listof string acyclic)) (listof string acyclic))
               (lambda (i acc)
                 (if (= i (string-length s))
                     acc
                     (let ((c (string-ref s i)))
                       (go (+ i 1)
                           (cons (cond ((char=? c #\") "\\\"")
                                       ((char=? c #\\) "\\\\")
                                       ((char=? c (integer->char 10)) "\\n")
                                       (else (char->string c)))
                                 acc)))))))
      (string-append "\"" (ev-joined (go 0 nil) "") "\""))))
(define ev-joined (->* ((listof string acyclic) string) string)
  (lambda (rev acc) (if (null? rev) acc (ev-joined (cdr rev) (string-append (car rev) acc)))))
(define ev-hex (->* (int) string)
  (lambda (n)
    (let ((d (char->string (string-ref "0123456789abcdef" (remainder n 16)))))
      (if (< n 16) d (string-append (ev-hex (quotient n 16)) d)))))

;; A `stage-failure` as the program sees it, a product of its kind, its
;; message and its place.
(define ev-stage-failure
  (->* ((productof (kind (sumof (unread unit) (malformed unit) (refused unit) (stale unit)))
                   (message string) (start int) (end int)))
       val)
  (lambda (f)
    (let ((kind (tagcase (extract f kind)
                  (unread u 'unread) (malformed u 'malformed) (refused u 'refused)
                  (stale u 'stale))))
      (the val (o-sum 'failed
                      (the val (o-product (list (cons 'kind (the val (o-sum kind the-unit)))
                                                (cons 'message (the val (extract f message)))
                                                (cons 'start (the val (extract f start)))
                                                (cons 'end (the val (extract f end)))))))))))
(define ev-stage-refused (->* (string) val)
  (lambda (m)
    (ev-stage-failure (product (kind (sum refused #u)) (message m) (start 0) (end 0)))))
;; Where the code `stage` runs is read from: past any place of a program's,
;; so that no fact of the program's is taken for one of it.
(define ev-stage-base int 1000000000000)
;; Whether `n` is bound in `e`, not the standard one.
(define ev-bound? (->* (env symbol) bool)
  (lambda (e n) (and (not (null? e)) (or (symbol=? (car (car e)) n) (ev-bound? (cdr e) n)))))
;; Whether `f`, in `e`, is `stage`'s operator, `(proj %stage E R)`, the
;; standard `%stage`; or `session-check`'s, of `%session-check`: `op`.
(define ev-stage-op? (->* (exp env symbol) bool)
  (lambda (f e op)
    (tagcase f
      (e-proj (body ds a b abk)
        (tagcase body
          (e-var (n c d cdk) (and (symbol=? n op) (not (ev-bound? e n))))
          (else y #f)))
      (else y #f))))

;; `e` with `n` bound to a new cell holding `v`.
(define bind1 (->* (symbol val env) env)
  (lambda (n v e) (cons (cons n (cell v)) e)))

(define lookup (->* (env symbol) val)
  (lambda (e name)
    (cond ((null? e) (standard name))
          ((symbol=? (car (car e)) name) (get (cdr (car e))))
          (else (lookup (cdr e) name)))))

(define find-cell (->* (env symbol) vcell)
  (lambda (e n)
    (cond ((null? e) (efail "no such local"))
          ((symbol=? (car (car e)) n) (cdr (car e)))
          (else (find-cell (cdr e) n)))))

;; A closure's parameters, bound to its arguments.
(define bind (->* (exp-params vals env) env)
  (lambda (ps xs e)
    (cond ((and (null? ps) (null? xs)) e)
          ((or (null? ps) (null? xs)) (efail "the wrong number of arguments"))
          (else (cons (cons (extract (car ps) 1) (cell (car xs))) (bind (cdr ps) (cdr xs) e))))))

(define field-of (->* (val symbol) val)
  (lambda (p l)
    (letrec ((find (subr (maxeff evals spin) (vfields) val)
               (lambda (fs)
                 (cond ((null? fs) (efail "no such label"))
                       ((symbol=? (car (car fs)) l) (cdr (car fs)))
                       (else (find (cdr fs)))))))
      (find (as-fields p "a product")))))

;; An arm's names, bound to a product's fields in order.
(define bind-fields (->* (names val env) env)
  (lambda (ns p e)
    (letrec ((go (subr evals (names vfields env) env)
               (lambda (ns fs e)
                 (cond ((and (null? ns) (null? fs)) e)
                       ((or (null? ns) (null? fs)) (efail "the wrong number of fields"))
                       (else (go (cdr ns) (cdr fs) (bind1 (car ns) (cdr (car fs)) e)))))))
      (go ns (as-fields p "a product") e))))

(define nth-field (->* (vfields int) (pairof symbol val @v))
  (lambda (fs i)
    (cond ((null? fs) (efail "no such field"))
          ((= i 0) (car fs))
          (else (nth-field (cdr fs) (- i 1))))))

;; `fs` reversed, onto `acc`.
(define reverse-fields (->* (vfields vfields) vfields)
  (lambda (fs acc) (if (null? fs) acc (reverse-fields (cdr fs) (cons (car fs) acc)))))

;; The modules to reshape (`k-reshapes`), as `run-checked` was given them.
(define ev-reshapes (ref k-reshape-list @v) (new nil))

;; Whether `at` is the expression `a` `b` `k` (`k-at`).
(define ev-at-is? (->* (k-at int int int) bool)
  (lambda (at a b k) (and (= (extract at 1) a) (= (extract at 2) b) (= (extract at 3) k))))

(define ev-reshape-in (->* (k-reshape-list int int int) ev-at)
  (lambda (rs a b k)
    (cond ((null? rs) nil)
          ((ev-at-is? (extract (car rs) 1) a b k) (the ev-at (cons (extract (car rs) 2) nil)))
          (else (ev-reshape-in (cdr rs) a b k)))))

;; Each `with` the checker saw (`k-with-vals`), as `run-checked` was given
;; them: which it is, and the module's values its body names, with their
;; positions.
(define ev-withs (ref k-with-list @v) (new nil))
;; What the checker found of each expression, as `run-checked` was given
;; it: a blobref's layouts, and offsets (`checked-extracts`).
(define ev-facts (ref k-facts @v) (new nil))
;; What an operation `a` `b` `k` takes (`n-datum`), in a list of one; none
;; if nothing.
(define ev-fact-in (->* (k-facts int int int) k-datums)
  (lambda (fs a b k)
    (cond ((null? fs) nil)
          ((ev-at-is? (extract (car fs) 1) a b k)
           (tagcase (extract (car fs) 2)
             (n-datum (d) (the k-datums (cons d nil)))
             (else y (ev-fact-in (cdr fs) a b k))))
          (else (ev-fact-in (cdr fs) a b k)))))
(define ev-fact-at (->* (int int int) k-datums)
  (lambda (a b k) (ev-fact-in (get ev-facts) a b k)))
;; `(extract v l)`, `a` `b` `k`: a product's field; or, of a blobref, one to
;; its field, at the offset the checker found.
(define ev-extract (->* (val symbol int int int) val)
  (lambda (v l a b k)
    (let ((d (ev-fact-at a b k)))
      (if (and (not (null? d)) (tagcase (car d) (datum-blobref-field (o) #t) (else y #f)))
          (tagcase (as-other v "a blobref")
            (o-bref (o at) (ev-bref o (+ at (k-datum-operand d))))
            (else y (efail-expected "a blobref")))
          (field-of v l)))))

(define ev-with-in (->* (k-with-list int int int) ev-with-at)
  (lambda (ws a b k)
    (cond ((null? ws) nil)
          ((ev-at-is? (extract (car ws) 1) a b k)
           (the ev-with-at (cons (product (1 (extract (car ws) 2)) (2 (extract (car ws) 3))) nil)))
          (else (ev-with-in (cdr ws) a b k)))))

;; The fields of `fs` at positions `ks`, in order.
;; The field `p` picks of `fs`: its `k`th, or the `j`th of the module that
;; is its `k`th.
(define pick-field (->* (vfields k-pick) (pairof symbol val @v))
  (lambda (fs p)
    (tagcase p
      (pick-value (k) (nth-field fs k))
      (pick-path (k j) (nth-field (as-fields (cdr (nth-field fs k)) "a module") j)))))
(define pick-fields (->* (vfields k-picks) vfields)
  (lambda (fs ks) (if (null? ks) nil (cons (pick-field fs (car ks)) (pick-fields fs (cdr ks))))))

;; Module `v` as `at` (in a list of one) reshapes it: its values at those
;; positions; as it is, if none.
(define reshape-val (->* (val ev-at) val)
  (lambda (v at)
    (if (null? at)
        v
        (let ((fs (as-fields v "a module")))
          (o-product (pick-fields fs (car at)))))))

;; `e` with each of module `m`'s values bound to its name, in order.
(define bind-module (->* (val env) env)
  (lambda (m e)
    (letrec ((go (subr (maxeff (read @v) (alloc @v) spin) (vfields env) env)
               (lambda (fs e)
                 (if (null? fs) e (go (cdr fs) (bind1 (car (car fs)) (cdr (car fs)) e))))))
      (go (as-fields m "a module") e))))

;; Module `m`'s values at positions `ps`, bound in `e` by names `ns`.
(define bind-module-at (->* (val k-names k-ids env) env)
  (lambda (m ns ps e)
    (let ((fs (as-fields m "a module")))
      (letrec ((go (subr (maxeff evals spin) (k-names k-ids env) env)
                 (lambda (ns ps e)
                   (if (or (null? ns) (null? ps))
                       e
                       (let ((v (cdr (nth-field fs (car ps)))))
                         (go (cdr ns) (cdr ps) (bind1 (car ns) v e)))))))
        (go ns ps e)))))

;; An abstract type `n`'s conversions' names.
(define conversion-names (->* (string) names)
  (lambda (n)
    (the names (list (string->symbol (string-append "up-" n))
                     (string->symbol (string-append "down-" n))))))

;; The names a module's items define, in order.
(define module-names (->* (mod-items) names)
  (lambda (items)
    (if (null? items)
        nil
        (let* ((it (car items)) (k (extract it 1)) (ns (extract it 2))
               (rest (module-names (cdr items))))
          (case k ((0) (append (conversion-names (symbol->string (car ns))) rest))
                  ((2 3) (append ns rest))
                  (else rest))))))

;; Each of `ns` bound in `e`, holding #u.
(define open-names (->* (names env) env)
  (lambda (ns e) (if (null? ns) e (open-names (cdr ns) (bind1 (car ns) the-unit e)))))

;; The values of `ns`, in `e`, onto `vs`, newest first.
(define rec-values (->* (names env vfields) vfields)
  (lambda (ns e vs)
    (if (null? ns)
        vs
        (rec-values (cdr ns) e (cons (cons (car ns) (get (find-cell e (car ns)))) vs)))))

;; A module's values, from `e`, onto `vs`, newest first: its definitions'.
(define module-values (->* (mod-items env vfields) vfields)
  (lambda (items e vs)
    (if (null? items)
        vs
        (let ((k (extract (car items) 1)))
          (module-values (cdr items) e
                         (if (or (= k 2) (= k 3)) (rec-values (extract (car items) 2) e vs) vs))))))

(define open-letrec (->* (exp-letrec-bs env) env)
  (lambda (bs e) (if (null? bs) e (open-letrec (cdr bs) (bind1 (extract (car bs) 1) the-unit e)))))

(define-rec
  (eval-all (->* ((listof exp acyclic) env) vals)
    (lambda (es e)
      (if (null? es)
          nil
          (let ((v (eval (car es) e)))
            (cons v (eval-all (cdr es) e))))))
  (eval-begin (->* ((listof exp acyclic) env) val)
    (lambda (es e)
      (cond ((null? es) the-unit)
            ((null? (cdr es)) (eval (car es) e))
            (else (begin (eval (car es) e) (eval-begin (cdr es) e))))))
  ;; `x`'s value; a module reshaped where the checker said so
  ;; (`k-reshape-at`), a product of the values its type wanted, by position.
  ;; With none to reshape, `eval-node` is called last, so that the
  ;; program's tail calls are the evaluator's, and a loop runs in constant
  ;; space.
  (eval (->* (exp env) val)
    (lambda (x e)
      (let ((rs (get ev-reshapes)))
        (if (null? rs)
            (eval-node x e)
            (reshape-val (eval-node x e)
                         (ev-reshape-in rs (exp-start x) (exp-end x) (exp-kth x)))))))
  (eval-node (->* (exp env) val)
    (lambda (x e)
      (tagcase x
        (e-var (n a b abk) (lookup e n))
        (e-int (n a b abk) n)
        (e-bool (v a b abk) v)
        (e-str (s a b abk) s)
        (e-char (c a b abk) c)
        (e-float (x a b abk) x)
        (e-sym (s a b abk) s)
        (e-unit (a b abk) the-unit)
        ;; A closure: the host's procedure of its arguments.
        (e-lambda (ps body a b abk) (lambda ((xs vals)) (eval body (bind ps xs e))))
        (e-app (f args a b abk)
          (cond ((ev-stage-op? f e '%stage) (ev-stage args e))
                ((ev-stage-op? f e '%session-check) (ev-session-check args e))
                ((ev-stage-op? f e '%reify-effect) (ev-reify #t args e))
                ((ev-stage-op? f e '%reify-region) (ev-reify #t args e))
                ((ev-stage-op? f e '%reify-type) (ev-reify #f args e))
                (else (let* ((fv (eval f e)) (xs (eval-all args e)))
                        (begin (ev-poll) (apply-val fv xs))))))
        (e-plambda (d body a b abk) (eval body e))
        ;; Regions and places are erased: a `letrena`'s or `letreap`'s
        ;; allocation is the heap's, and its name, the place as a value, is
        ;; unit.
        (e-letregion (k r i body a b abk) (eval body (bind1 r the-unit e)))
        (e-rlambda (r l a b abk) (eval l e))
        (e-proj (body ds a b abk) (eval body e))
        (e-the (d body a b abk) (eval body e))
        (e-convention (cnv body a b abk) (eval body e))
        (e-if (t th el a b abk) (if (as-bool (eval t e)) (eval th e) (eval el e)))
        (e-letrec (bs body a b abk) (eval-letrec bs body e))
        (e-let (bs body a b abk) (eval body (eval-let bs e e)))
        (e-begin (es a b abk) (eval-begin es e))
        (e-prompt (t body h a b abk)
          (let* ((tag (as-tag (eval t e))) (hv (eval h e)))
            (prompt tag (eval body e) (lambda (v) (apply1 hv v)))))
        ;; A blobref's read, write or index: its layout, as the checker found it.
        (e-bloblet (op i args got a b abk)
          (ev-bloblet op (if (< i 0) (k-datum-operand (ev-fact-at a b abk)) i) (eval-all args e)))
        (e-product (fs a b abk) (o-product (eval-fields fs e)))
        (e-extract (p l got a b abk) (ev-extract (eval p e) l a b abk))
        (e-sum (t v a b abk) (o-sum t (eval v e)))
        (e-tagcase (s arms els got a b abk)
          (eval-tagcase (eval s e) arms els e (k-datum-operand (ev-fact-at a b abk))))
        ;; A module: a product of its values, in order, each labelled by its
        ;; name; its abstract types' conversions the identity.
        (e-module (items a b abk) (eval-module items e))
        ;; `with`: the module's values its body names, by position, bound by
        ;; their names (all of them, if the checker did not say which).
        ;; `(with #%fx n)`: the standard `n`, whatever binds `n` here.
        (e-with (m body a b abk)
          (if (k-fx-module? m)
              (tagcase body (e-var (n c d cdk) (standard n)) (else y (efail "`(with #%fx name)`")))
              (let ((used (ev-with-in (get ev-withs) a b abk)))
                (eval body
                      (if (null? used)
                          (bind-module (lookup e m) e)
                          (bind-module-at (lookup e m) (extract (car used) 1) (extract (car used) 2)
                                          e)))))))))
  ;; A module's items, as a `letrec*`'s (`DONE.md` §37): every name first,
  ;; holding #u; then each item's values, in order, in the scope of all.
  ;; `stage`'s call, `((proj %stage E R) m code)` (`ev-staged-in`).
  (ev-stage (->* ((listof exp acyclic) env) val)
    (lambda (args e)
      (ev-staged args e
                 (lambda ((m val) (text string) (ns string)
                          (gr (listof (bytevectorof @v) acyclic)) (rp wcell))
                   (tagcase (%stage-check text ns rp gr)
                     (failed f (ev-stage-failure f))
                     (checked w (ev-stage-run w m)))))))
  ;; A `reify-…`'s call, of the evidence it is given: what the checker
  ;; noted at it, the effect (or a region), or the type, given the evidence.
  (ev-reify (->* (bool (listof exp acyclic) env) val)
    (lambda (effect args e)
      (let* ((x (car args))
             (noted (ev-staged-in (get ev-facts) (exp-start x) (exp-end x) (exp-kth x))))
        (if (null? noted)
            (efail "evidence: what it is of is not known")
            ;; Its rep, filled by the reps of the evidence given
            ;; (`docs/research/heap-types.md`, step 6): its binary form,
            ;; empty if none.
            (let* ((n (car noted)) (given (eval x e)))
              (the val (o-bytes (%reify-rep (extract n 1) (extract n 3) (extract n 2)
                                            (ev-given-reps given)))))))))
  ;; Evidence given, a product of pieces of it, as their reps: each its
  ;; rep's binary form, empty if it has none.
  (ev-given-reps (->* (val) (listof (bytevectorof @v) acyclic))
    (lambda (v)
      (letrec ((go (subr (maxeff evals spin) (vfields) (listof (bytevectorof @v) acyclic))
                 (lambda (fs)
                   (if (null? fs) nil (cons (ev-piece-rep (cdr (car fs))) (go (cdr fs)))))))
        (go (as-fields v "evidence")))))
  (ev-piece-rep (->* (val) (bytevectorof @v))
    (lambda (v)
      (tagcase (as-other v "evidence")
        (o-bytes (b) b)
        (else y (the (bytevectorof @v) (make-bytevector 0 0))))))
  ;; `stage`'s or `session-check`'s call, `(op m code)`: what `k` makes of
  ;; `m`'s value, what the checker noted at the code (`ev-staged-in`) and
  ;; the code, written out; or the refusal.
  (ev-staged (->* ((listof exp acyclic) env
                   (subr (maxeff evals spin)
                         (val string string (listof (bytevectorof @v) acyclic) wcell)
                         val))
                  val)
    (lambda (args e k)
      (let* ((m (eval (car args) e))
             (code (car (cdr args)))
             (noted (ev-staged-in (get ev-facts) (exp-start code) (exp-end code) (exp-kth code)))
             (v (eval code e)))
        (if (null? noted)
            (ev-stage-refused
             "this machine cannot stage code: what it is checked against is not known")
            (tagcase (ev-code-pieces v nil)
              (not-code u (ev-stage-refused "the code is not a datum"))
              (text rev
                (let ((n (car noted)))
                  (let ((given (eval (car (cdr (cdr args))) e)))
                    (k m (ev-joined rev "") (extract n 2) (ev-given-reps given)
                       (extract n 3))))))))))
  ;; `session-check`'s call: checked by the session's checker
  ;; (`%session-eval-check`); an expression's forms run in the session,
  ;; the last's value its procedure; a definition, pending.
  (ev-session-check (->* ((listof exp acyclic) env) val)
    (lambda (args e)
      (ev-staged args e
                 (lambda ((s val) (text string) (ns string)
                          (gr (listof (bytevectorof @v) acyclic)) (rp wcell))
                   (tagcase (%session-eval-check (ev-host s) text ns rp gr)
                     (run ts (ev-sum2 'ok 'expression (ev-session-run s ts)))
                     (ok d (tagcase d
                             (definition p (ev-sum2 'ok 'definition (the val (o-host p))))))
                     (failed f (ev-stage-failure f)))))))
  ;; The code as checked, `w`, read, parsed and run in no environment but
  ;; the standard one: the procedure of the module it makes, given `m`.
  (ev-stage-run (->* (string val) val)
    (lambda (w m)
      (let ((read (read-text w ev-stage-base)))
        (if (null? read)
            (ev-stage-refused "the code as checked does not read")
            (tagcase (parse (car read))
              (p-err (msg a b) (ev-stage-refused msg))
              (p-ok (tops)
                (if (null? tops)
                    (ev-stage-refused "the code as checked is no form")
                    (tagcase (car tops)
                      (t-exp (x) (the val (o-sum 'ok (apply1 (eval x (the env nil)) m))))
                      (else y (ev-stage-refused "the code as checked is not an expression"))))))))))
  (eval-module (->* (mod-items env) val)
    (lambda (items e)
      (let ((inner (open-names (module-names items) e)))
        (begin (fill-module items inner)
               (o-product (reverse-fields (module-values items inner nil) nil))))))
  (fill-module (->* (mod-items env) unit)
    (lambda (items e)
      (if (null? items)
          #u
          (let* ((it (car items)) (k (extract it 1)) (ns (extract it 2)) (xs (extract it 4)))
            (begin
              (case k ((0) (fill-cells (conversion-names (symbol->string (car ns))) xs e))
                      ((2 3) (fill-cells ns xs e))
                      (else #u))
              (fill-module (cdr items) e))))))
  ;; Each value of `xs`, into its name's cell in `e`.
  (fill-cells (->* (names exp-list env) unit)
    (lambda (ns xs e)
      (if (null? ns)
          #u
          (begin (set (find-cell e (car ns)) (eval (car xs) e))
                 (fill-cells (cdr ns) (cdr xs) e)))))
  (eval-let (->* (exp-let-bs env env) env)
    (lambda (bs outer e)
      (if (null? bs)
          e
          (let ((v (eval (extract (car bs) 2) outer)))
            (eval-let (cdr bs) outer (bind1 (extract (car bs) 1) v e))))))
  ;; Every name first, holding #u; then each value, in the scope of all.
  (eval-letrec (->* (exp-letrec-bs exp env) val)
    (lambda (bs body e)
      (let ((inner (open-letrec bs e)))
        (begin (fill-letrec bs inner) (eval body inner)))))
  ;; Each binding's value, into its name's cell in `inner`.
  (fill-letrec (->* (exp-letrec-bs env) unit)
    (lambda (bs inner)
      (if (null? bs)
          #u
          (let ((c (find-cell inner (extract (car bs) 1))))
            (begin (set c (eval (extract (car bs) 3) inner))
                   (fill-letrec (cdr bs) inner))))))
  (eval-fields (->* (exp-let-bs env) vfields)
    (lambda (fs e)
      (if (null? fs)
          nil
          (let ((v (eval (extract (car fs) 2) e)))
            (cons (cons (extract (car fs) 1) v) (eval-fields (cdr fs) e))))))
  ;; The arm for sum `s`'s tag, its fields bound; else the `else`.
  (eval-tagcase (->* (val exp-arms exp-let-bs env int) val)
    (lambda (s arms els e k)
      (if (>= k 0)
          (eval-flat-tagcase s (ev-flat-tag s k) arms els e k)
      (tagcase (as-other s "a sum")
        (o-sum (tag v)
          (letrec ((try (subr (maxeff evals spin) (exp-arms) val)
                     (lambda (as)
                       (cond ((null? as)
                              (if (null? els)
                                  (efail "no arm for this value")
                                  (eval (extract (car els) 2) (bind1 (extract (car els) 1) s e))))
                             ((symbol=? (extract (car as) 1) tag)
                              (eval (extract (car as) 4)
                                    (if (extract (car as) 2)
                                        (bind-fields (extract (car as) 3) v e)
                                        (bind1 (car (extract (car as) 3)) v e))))
                             (else (try (cdr as)))))))
            (try arms)))
        (else y (efail-expected "a sum"))))))
  ;; On a blobref to a flat sum, of layout `k` (`TODO.md` §77): the arm for
  ;; its tag, `t`, given a blobref to the variant; else the `else`.
  (eval-flat-tagcase (->* (val val exp-arms exp-let-bs env int) val)
    (lambda (s t arms els e k)
      (cond ((null? arms)
             (if (null? els)
                 (efail "tagcase: no arm for this flat sum's tag")
                 (eval (extract (car els) 2) (bind1 (extract (car els) 1) s e))))
            ((ev-label-is? t (extract (car arms) 1) k)
             (eval (extract (car arms) 4)
                   (bind1 (car (extract (car arms) 3))
                          (ev-blobref 'blobref+ 0 (list s (quotient k 256))) e)))
            (else (eval-flat-tagcase s t (cdr arms) els e k))))))

;; Names whose next definition keeps the cell they have: definitions that
;; assign their globals (`checked-tops`, under redefinition).
(define ev-keep (ref (listof symbol acyclic) @v) (new nil))

(define ev-kept? (->* ((listof symbol acyclic) symbol) bool)
  (lambda (ks n) (and (not (null? ks)) (or (symbol=? (car ks) n) (ev-kept? (cdr ks) n)))))

(define ev-unkeep (->* ((listof symbol acyclic) symbol) (listof symbol acyclic))
  (lambda (ks n)
    (cond ((null? ks) ks)
          ((symbol=? (car ks) n) (ev-unkeep (cdr ks) n))
          (else (the (listof symbol acyclic) (cons (car ks) (ev-unkeep (cdr ks) n)))))))

;; Globals `g`: the program's (`genv`), or a session's (`ev-sessions`).
(define-type vglobals (ref env @v))

(define ev-new-global (->* (vglobals symbol) vcell)
  (lambda (g n) (let ((c (cell the-unit))) (begin (set g (cons (cons n c) (get g))) c))))

;; The cell global `n` has; a new one, if it has none.
(define ev-cell-of (->* (vglobals env symbol) vcell)
  (lambda (g e n)
    (cond ((null? e) (ev-new-global g n))
          ((symbol=? (car (car e)) n) (cdr (car e)))
          (else (ev-cell-of g (cdr e) n)))))

;; The cell a definition of `n` sets: the one it has, if kept; else new.
(define push-global (->* (vglobals symbol) vcell)
  (lambda (g n)
    (if (ev-kept? (get ev-keep) n)
        (begin (set ev-keep (ev-unkeep (get ev-keep) n)) (ev-cell-of g (get g) n))
        (ev-new-global g n))))

(define rec-cells (->* (vglobals exp-letrec-bs) vcells)
  (lambda (g bs)
    (if (null? bs)
        nil
        (let ((c (push-global g (extract (car bs) 1)))) (cons c (rec-cells g (cdr bs)))))))

(define rec-fill (->* (vglobals exp-letrec-bs vcells) unit)
  (lambda (g bs cells)
    (if (null? bs)
        #u
        (begin (set (car cells) (eval (extract (car bs) 3) (get g)))
               (rec-fill g (cdr bs) (cdr cells))))))

;; Whether `x` is a lambda, under any type abstractions and ascriptions.
(define lambda-exp? (->* (exp) bool)
  (lambda (x)
    (tagcase x
      (e-lambda (ps body a b abk) #t)
      (e-plambda (d body a b abk) (lambda-exp? body))
      (e-the (d body a b abk) (lambda-exp? body))
      (e-convention (cnv body a b abk) (lambda-exp? body))
      (else y #f))))

;; Defines `n` as `x`'s value, run in the scope before it.
(define ev-define (->* (vglobals symbol exp) val)
  (lambda (g n x) (let ((v (eval x (get g)))) (begin (set (push-global g n) v) the-unit))))

;; Top-level form `t` run in globals `g`.
(define eval-top-in (->* (vglobals top) val)
  (lambda (g t)
    (tagcase t
      (t-define (n ty x a b)
        (if (and (not (null? ty)) (lambda-exp? x))
            ;; A lambda: the cell first, so that it can call itself.
            (let ((c (push-global g n))) (begin (set c (eval x (get g))) the-unit))
            ;; Not recursive: the value first, in the scope before it.
            (ev-define g n x)))
      ;; Every name's cell first; then each lambda, which runs nothing.
      (t-define-rec (bs a b) (begin (rec-fill g bs (rec-cells g bs)) the-unit))
      (t-exp (x) (eval x (get g)))
      (else x the-unit))))

(define eval-top (->* (top) val) (lambda (t) (eval-top-in genv t)))

;; The value so far, after top-level form `t` gave `v`: `v` if `t` is an
;; expression, else `last`, as before.
(define ev-last (->* (top val val) val)
  (lambda (t v last) (tagcase t (t-exp (x) v) (else y last))))

;; The value of the last form, or the first error.
(define eval-program (->* ((listof top acyclic)) eresult)
  (lambda (tops)
    (prompt eval-tag
      (letrec ((go (subr (maxeff evals spin) ((listof top acyclic) val) val)
                 (lambda (ts last)
                   (if (null? ts)
                       last
                       (let ((v (eval-top (car ts)))) (go (cdr ts) (ev-last (car ts) v last)))))))
        (ev-ok (go tops the-unit)))
      (lambda (r) r))))

;; Name `n`, and a `define-rec`'s names, to keep their cells.
(define ev-keep! (->* (symbol) unit)
  (lambda (n) (set ev-keep (the (listof symbol acyclic) (cons n (get ev-keep))))))

(define ev-keep-all (->* (exp-letrec-bs) unit)
  (lambda (bs) (if (null? bs) #u (begin (ev-keep! (extract (car bs) 1)) (ev-keep-all (cdr bs))))))

;; Before a run that assigns its names' globals: each keeps its cell.
(define ev-keep-names (->* (top) unit)
  (lambda (t)
    (tagcase t
      (t-define (n ty x a b) (ev-keep! n))
      (t-define-rec (bs a b) (ev-keep-all bs))
      (else y #u))))

;; What a checked program runs (`checked-tops`), each in turn: the value of
;; the last expression, or the first error.
(define eval-runs (->* ((listof k-run acyclic)) eresult)
  (lambda (runs)
    (prompt eval-tag
      (letrec ((go (subr (maxeff evals spin) ((listof k-run acyclic) val) val)
                 (lambda (rs last)
                   (if (null? rs)
                       last
                       (let* ((r (car rs))
                              (kept (if (extract r 2) (ev-keep-names (extract r 1)) #u))
                              (v (eval-top (extract r 1))))
                         (go (cdr rs) (ev-last (extract r 1) v last)))))))
        (ev-ok (go runs the-unit)))
      (lambda (r) r))))

;;; ---------------------------------------------------------------- sessions
;; Sessions (`docs/research/eval.md`, "Sessions"), kept here: a session,
;; and a pending definition, are the runtime's, which the checker written
;; in Rust keeps the state of (`sessions.rs`, "evaluated"), given here as
;; arrays never looked in; a session's globals beside it, the module's
;; `stage-module`.
(define ev-sessions (ref (listof (pairof val vglobals @v) @v) @v) (new nil))

;; Session `s`'s globals.
(define ev-session-globals (->* (val) vglobals)
  (lambda (s)
    (letrec ((find (subr (maxeff evals spin) ((listof (pairof val vglobals @v) @v)) vglobals)
               (lambda (ss)
                 (cond ((null? ss) (efail "not a session"))
                       ((ev-eq? (car (car ss)) s) (cdr (car ss)))
                       (else (find (cdr ss)))))))
      (find (get ev-sessions)))))

;; A session, or a pending definition, as the runtime has it.
(define ev-host (->* (val) (arrayof val @v))
  (lambda (v)
    (tagcase (as-other v "a session") (o-host (h) h) (else y (efail-expected "a session")))))

;; `(sum t1 (sum t2 v))`.
(define ev-sum2 (->* (symbol symbol val) val)
  (lambda (t1 t2 v) (the val (o-sum t1 (the val (o-sum t2 v))))))

;; A session's form, as text, read and parsed.
(define ev-session-top (->* (string) top)
  (lambda (w)
    (let ((read (read-text w ev-stage-base)))
      (if (null? read)
          (efail "a session's form does not read")
          (tagcase (parse (car read))
            (p-err (msg a b) (efail msg))
            (p-ok (tops) (if (null? tops) (efail "a session's form is no form") (car tops))))))))

;; Forms `ts` run in session `s`, each in turn: the last's value.
(define ev-session-run (->* (val (listof string acyclic)) val)
  (lambda (s ts)
    (let ((g (ev-session-globals s)))
      (letrec ((go (subr (maxeff evals spin) ((listof string acyclic) val) val)
                 (lambda (ts last)
                   (if (null? ts)
                       last
                       (let ((t (ev-session-top (car ts))))
                         (go (cdr ts) (ev-last t (eval-top-in g t) last)))))))
        (go ts the-unit)))))

;; A commit's forms run in session `s`, each in turn, those that assign
;; keeping their globals' cells.
(define ev-session-commit (->* (val (listof (productof (text string) (keeps bool)) acyclic)) val)
  (lambda (s fs)
    (let ((g (ev-session-globals s)))
      (letrec ((go (subr (maxeff evals spin) ((listof (productof (text string) (keeps bool))
                                                       acyclic))
                         val)
                 (lambda (fs)
                   (if (null? fs)
                       the-unit
                       (let ((t (ev-session-top (extract (car fs) text))))
                         (begin (if (extract (car fs) keeps) (ev-keep-names t) #u)
                                (eval-top-in g t)
                                (go (cdr fs))))))))
        (go fs)))))

;; Strings `ns`, as the evaluator's list of them.
(define ev-string-vals (->* ((listof string acyclic)) val)
  (lambda (ns) (if (null? ns) nil (cons (the val (car ns)) (ev-string-vals (cdr ns))))))

;; The steps of a session but `session-check`'s (`ev-session-check`), made
;; primitives as a program begins.
(define ev-session-prims! (->* () unit)
  (lambda ()
   (begin
    ;; A session of module `m`.
    (prim! 'make-session
           (lambda (xs)
             (let* ((m (car xs))
                    (s (the val (o-host (%session-eval-make m)))))
               (begin (set ev-sessions
                           (cons (cons s
                                       (the vglobals (new (list (cons 'stage-module (cell m))))))
                                 (get ev-sessions)))
                      s))))
    (prim! 'session-redefines
           (lambda (xs)
             (tagcase (%session-eval-redefines (ev-host (car xs)) (ev-host (car (cdr xs))))
               (fresh u (the val (o-sum 'fresh the-unit)))
               (redefines r
                 (the val
                      (o-sum 'redefines
                             (the val
                                  (o-product
                                   (list (cons 'name (the val (extract r name)))
                                         (cons 'old (the val (extract r old)))
                                         (cons 'new (the val (extract r new)))
                                         (cons 'users (ev-string-vals (extract r users))))))))))))
    ;; Readied, given the decision: what the commit runs, run by `go`, the
    ;; program's, in the session.
    (prim! '%session-ready
           (lambda (xs)
             (let* ((s (car xs))
                    (tag (tagcase (as-other (car (cdr (cdr xs))) "a `session-decision`")
                           (o-sum (t v) (symbol->string t))
                           (else y ""))))
               (tagcase (%session-eval-ready (ev-host s) (ev-host (car (cdr xs))) tag)
                 (run fs (the val (o-sum 'go (the val (lambda ((ys vals))
                                                       (ev-session-commit s fs))))))
                 (failed f (ev-stage-failure f))))))
    (prim! '%session-committed!
           (lambda (xs)
             (tagcase (%session-eval-committed! (ev-host (car xs)) (ev-host (car (cdr xs))))
               (defined n (the val (o-sum 'defined (the val n))))
               (failed f (ev-stage-failure f))))))))

;; A whole program begins with no globals, and no names kept.
(define ev-begin! (->* (k-reshape-list k-with-list k-facts) unit)
  (lambda (rs ws fs)
    (begin (set genv nil) (set ev-keep nil) (set ev-reshapes rs) (set ev-withs ws)
           (set ev-facts fs) (set ev-sessions nil) (ev-session-prims!))))

;; The entry point for a program the checker written in FX-26 checked: what
;; it runs (`checked-tops`, under redefinition), run; its value shown, or
;; its error. A whole program, as each is.
(define run-checked (->* ((listof k-run acyclic)) string)
  (lambda (runs)
    (tagcase (begin (ev-begin! (get k-reshapes) (get k-with-vals) (get k-extracts))
                    (eval-runs runs))
      (ev-ok (v) (show-val v))
      (ev-err (m) (string-append "!! " m)))))

;; More of a program, form by form, as the REPL gives them (`check-more`):
;; what it runs, with the globals the forms before made, and what the
;; checker said of its places beside what it said of theirs (a closure made
;; before may run now). Each form's positions are past every one's before
;; (`syn::eval_more_with_fx26_evaluator`), so no two places are one.
(define run-checked-more (->* ((listof k-run acyclic)) string)
  (lambda (runs)
    (begin
      (set ev-reshapes (append (get k-reshapes) (get ev-reshapes)))
      (set ev-withs (append (get k-with-vals) (get ev-withs)))
      (set ev-facts (append (get k-extracts) (get ev-facts)))
      (tagcase (eval-runs runs)
        (ev-ok (v) (show-val v))
        (ev-err (m) (string-append "!! " m))))))

;; The entry point: a program's trees, run; its value shown, or its error.
(define run-program (->* ((listof top acyclic)) string)
  (lambda (tops)
    (tagcase (begin (ev-begin! nil nil nil) (eval-program tops))
      (ev-ok (v) (show-val v))
      (ev-err (m) (string-append "!! " m))))))))
