;;; KNUTH-BENDIX -- Knuth-Bendix completion of a set of equations (a
;;; geometry presentation), with rewriting, recursive path ordering and
;;; critical pairs.
;;;
;;; From the SML/NJ benchmark suite (after a CAML program).
;;; From MLton's benchmark suite (benchmark/tests/knuth-bendix.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. MLton's driver was not fetched; the
;;; iteration count, 1 completion, is this port's. MLton's `doit n`
;;; runs n completions.
;;; Answer: 24, the number of rules in the canonical set found (the
;;; original prints them, to a `print` that does nothing).
;;;
;;; What changed:
;;; - The exception Failure is an abort to one prompt tag, carrying the
;;;   message. A tag fixes what its prompts deliver, where each `handle` has
;;;   a type of its own, so a prompt's body delivers its value in a sum,
;;;   `caught`, whose variant says which type it is (`a-term`, `a-bool`, ...)
;;;   or that Failure was raised (`failure`); the handler's expression runs
;;;   after the prompt, as a `handle`'s does, outside it. `handle Failure
;;;   "find"` re-raises other messages.
;;; - SML's equality on terms (`M = N`) is `term=?`, structural; on ints
;;;   and strings, `=` and `string=?`. `mem` is used at ints and at
;;;   strings, and is written twice, `mem-int` and `mem-string`.
;;; - The polymorphic list procedures (`@`, `map`, `it_list`, ...) are
;;;   `poly`s; procedures that take their arguments one at a time or as a
;;;   tuple (`map f l`, `it_list f a l`, `order (M, N)`, `kbrec n rules
;;;   failures (k, l) eqs`, ...) take them all at once, and the functions
;;;   given to `it_list2` take the pair's two parts as two arguments.
;;;   `try_find`'s result is a term, the one type it is used at.
;;; - `length` is `len`, since FX-26 has a `length` of its own. Unused
;;;   procedures (`rev_append`, the first `union`, `fst`/`snd`, the
;;;   `Group_rules`) are left out.
;;; - `Group_rank` of a name it does not know raises Match in SML; here,
;;;   Failure (it never happens).

(define-datatype term (Var int) (Term string (listof term @heap)))
(define-datatype ordering (Greater) (Equal) (NotGE))
(define-type terms (listof term @heap))
(define-type ints (listof int @heap))
(define-type strings (listof string @heap))
(define-type binding (productof (1 int) (2 term)))
(define-type subst (listof binding @heap))
(define-type tpair (productof (1 term) (2 term)))
(define-type tpairs (listof tpair @heap))
(define-type numbered-pair (productof (1 int) (2 tpair)))
(define-type rule (productof (1 int) (2 numbered-pair)))
(define-type rules (listof rule @heap))
(define-type super-pair (productof (1 ints) (2 subst)))
(define-type supers (listof super-pair @heap))
(define-type diff (productof (1 terms) (2 terms)))

;; What completion does; Failure aborts to @z.
(define-effect kb-body (maxeff (read @heap) (alloc @heap) spin (read @globals)))
(define-effect kb (maxeff kb-body (goto @z)))

;; What a `handle` delivers: its body's value, by type, or the message of
;; the Failure raised.
(define-type caught
  (sumof (failure string) (a-term term) (a-bool bool) (a-terms terms)
         (a-diff diff) (a-supers supers) (a-rules rules)))
(define kb-tag (prompt-tag caught string kb-body @z) (make-continuation-prompt-tag))
(define* failwith (subr (goto @z) (string) void)
  (lambda (s) (abort-current-continuation kb-tag s)))
(define caught-failure (subr pure (string) caught) (lambda (s) (sum failure s)))

;;; ------------------------------------------------------- list procedures

(define len (poly ((a type)) (subr kb ((listof a @heap)) int))
  (plambda ((a type))
    (lambda ((l (listof a @heap)))
      (letrec ((j (subr kb (int (listof a @heap)) int)
                 (lambda (k l) (if (null? l) k (j (+ k 1) (cdr l))))))
        (j 0 l)))))

(define append (poly ((a type)) (subr kb ((listof a @heap) (listof a @heap)) (listof a @heap)))
  (plambda ((a type))
    (lambda ((xs (listof a @heap)) (l (listof a @heap)))
      (if (null? xs) l (cons (car xs) (append (cdr xs) l))))))

(define rev (poly ((a type)) (subr kb ((listof a @heap)) (listof a @heap)))
  (plambda ((a type))
    (lambda ((l (listof a @heap)))
      (letrec ((f (subr kb ((listof a @heap) (listof a @heap)) (listof a @heap))
                 (lambda (l h) (if (null? l) h (f (cdr l) (cons (car l) h))))))
        (f l nil)))))

(define app (poly ((a type)) (subr kb ((subr kb (a) unit) (listof a @heap)) unit))
  (plambda ((a type))
    (lambda ((f (subr kb (a) unit)) (l (listof a @heap)))
      (letrec ((app-rec (subr kb ((listof a @heap)) unit)
                 (lambda (l) (if (null? l) #u (begin (f (car l)) (app-rec (cdr l)))))))
        (app-rec l)))))

(define map (poly ((a type) (b type)) (subr kb ((subr kb (a) b) (listof a @heap)) (listof b @heap)))
  (plambda ((a type) (b type))
    (lambda ((f (subr kb (a) b)) (l (listof a @heap)))
      (letrec ((map-rec (subr kb ((listof a @heap)) (listof b @heap))
                 (lambda (l) (if (null? l) nil (cons (f (car l)) (map-rec (cdr l)))))))
        (map-rec l)))))

(define it-list (poly ((a type) (b type)) (subr kb ((subr kb (a b) a) a (listof b @heap)) a))
  (plambda ((a type) (b type))
    (lambda ((f (subr kb (a b) a)) (a0 a) (l (listof b @heap)))
      (letrec ((it-rec (subr kb (a (listof b @heap)) a)
                 (lambda (a l) (if (null? l) a (it-rec (f a (car l)) (cdr l))))))
        (it-rec a0 l)))))

(define it-list2 (poly ((a type) (b type) (c type)) (subr kb ((subr kb (a b c) a) a (listof b @heap) (listof c @heap)) a))
  (plambda ((a type) (b type) (c type))
    (lambda ((f (subr kb (a b c) a)) (a0 a) (l1 (listof b @heap)) (l2 (listof c @heap)))
      (letrec ((it-rec (subr kb (a (listof b @heap) (listof c @heap)) a)
                 (lambda (a l1 l2)
                   (if (null? l1)
                       (if (null? l2) a (failwith "it_list2"))
                       (if (null? l2)
                           (failwith "it_list2")
                           (it-rec (f a (car l1) (car l2)) (cdr l1) (cdr l2)))))))
        (it-rec a0 l1 l2)))))

(define exists (poly ((a type)) (subr kb ((subr kb (a) bool) (listof a @heap)) bool))
  (plambda ((a type))
    (lambda ((p (subr kb (a) bool)) (l (listof a @heap)))
      (letrec ((exists-rec (subr kb ((listof a @heap)) bool)
                 (lambda (l) (if (null? l) #f (or (p (car l)) (exists-rec (cdr l)))))))
        (exists-rec l)))))

(define for-all (poly ((a type)) (subr kb ((subr kb (a) bool) (listof a @heap)) bool))
  (plambda ((a type))
    (lambda ((p (subr kb (a) bool)) (l (listof a @heap)))
      (letrec ((for-all-rec (subr kb ((listof a @heap)) bool)
                 (lambda (l) (if (null? l) #t (and (p (car l)) (for-all-rec (cdr l)))))))
        (for-all-rec l)))))

(define try-find (poly ((a type)) (subr kb ((subr kb (a) term) (listof a @heap)) term))
  (plambda ((a type))
    (lambda ((f (subr kb (a) term)) (l (listof a @heap)))
      (letrec ((try-find-rec (subr kb ((listof a @heap)) term)
                 (lambda (l)
                   (if (null? l)
                       (failwith "try_find")
                       (tagcase (prompt kb-tag (sum a-term (f (car l))) caught-failure)
                         (a-term t t)
                         (else o (try-find-rec (cdr l))))))))
        (try-find-rec l)))))

(define partition (poly ((a type)) (subr kb ((subr kb (a) bool) (listof a @heap)) (productof (1 (listof a @heap)) (2 (listof a @heap)))))
  (plambda ((a type))
    (lambda ((p (subr kb (a) bool)) (l (listof a @heap)))
      (letrec ((part-rec (subr kb ((listof a @heap)) (productof (1 (listof a @heap)) (2 (listof a @heap))))
                 (lambda (l)
                   (if (null? l)
                       (product (1 (the (listof a @heap) nil)) (2 (the (listof a @heap) nil)))
                       (let* ((pn (part-rec (cdr l))) (pos (extract pn 1)) (neg (extract pn 2)))
                         (if (p (car l))
                             (product (1 (the (listof a @heap) (cons (car l) pos))) (2 neg))
                             (product (1 pos) (2 (the (listof a @heap) (cons (car l) neg))))))))))
        (part-rec l)))))

;;; 3- Les ensembles et les listes d'association

(define* mem-int (subr kb (int ints) bool)
  (lambda (a l)
    (letrec ((mem-rec (subr kb (ints) bool)
               (lambda (l) (if (null? l) #f (or (= a (car l)) (mem-rec (cdr l)))))))
      (mem-rec l))))

(define* mem-string (subr kb (string strings) bool)
  (lambda (a l)
    (letrec ((mem-rec (subr kb (strings) bool)
               (lambda (l) (if (null? l) #f (or (string=? a (car l)) (mem-rec (cdr l)))))))
      (mem-rec l))))

(define mem-assoc (poly ((b type)) (subr kb (int (listof (productof (1 int) (2 b)) @heap)) bool))
  (plambda ((b type))
    (lambda ((a int) (l (listof (productof (1 int) (2 b)) @heap)))
      (letrec ((mem-rec (subr kb ((listof (productof (1 int) (2 b)) @heap)) bool)
                 (lambda (l) (if (null? l) #f (or (= a (extract (car l) 1)) (mem-rec (cdr l)))))))
        (mem-rec l)))))

(define assoc (poly ((b type)) (subr kb (int (listof (productof (1 int) (2 b)) @heap)) b))
  (plambda ((b type))
    (lambda ((a int) (l (listof (productof (1 int) (2 b)) @heap)))
      (letrec ((assoc-rec (subr kb ((listof (productof (1 int) (2 b)) @heap)) b)
                 (lambda (l)
                   (if (null? l)
                       (failwith "find")
                       (if (= a (extract (car l) 1)) (extract (car l) 2) (assoc-rec (cdr l)))))))
        (assoc-rec l)))))

;;; 4- Les sorties

(define print (subr pure (string) unit) (lambda (s) #u))
(define* print-string (subr pure (string) unit) (lambda (s) (print s)))
(define* print-num (subr pure (int) unit) (lambda (n) (print (int->string n))))
(define* print-newline (subr pure () unit) (lambda () (print "\n")))
(define* message (subr pure (string) unit) (lambda (s) (begin (print s) (print "\n"))))

;;; 5- Les ensembles

(define* union (subr kb (ints ints) ints)
  (lambda (l1 l2)
    (letrec ((union-rec (subr kb (ints) ints)
               (lambda (l)
                 (if (null? l)
                     l1
                     (if (mem-int (car l) l1) (union-rec (cdr l)) (cons (car l) (union-rec (cdr l))))))))
      (union-rec l2))))

;;; ------------------------------------------------- Term manipulations

(define-rec
  (term=? (subr (maxeff (read @heap) spin (read @globals)) (term term) bool)
    (lambda (a b)
      (tagcase a
        (Var (m) (tagcase b (Var (n) (= m n)) (else o #f)))
        (Term (f l) (tagcase b (Term (g k) (and (string=? f g) (terms=? l k))) (else o #f))))))
  (terms=? (subr (maxeff (read @heap) spin (read @globals)) (terms terms) bool)
    (lambda (l k)
      (if (null? l)
          (null? k)
          (if (null? k) #f (and (term=? (car l) (car k)) (terms=? (cdr l) (cdr k))))))))

(define-rec
  (vars (subr kb (term) ints)
    (lambda (t) (tagcase t (Var (n) (the ints (cons n nil))) (Term (f l) (vars-of-list l)))))
  (vars-of-list (subr kb (terms) ints)
    (lambda (l) (if (null? l) nil (union (vars (car l)) (vars-of-list (cdr l)))))))

(define* substitute (subr kb (subst term) term)
  (lambda (subst t)
    (letrec ((subst-rec (subr kb (term) term)
               (lambda (t)
                 (tagcase t
                   (Term (oper sons) (Term oper (map subst-rec sons)))
                   (Var (n)
                     (tagcase (prompt kb-tag (sum a-term (assoc n subst)) caught-failure)
                       (a-term x x)
                       (else o t)))))))
      (subst-rec t))))

(define* change (subr kb ((subr kb (term) term) terms int) terms)
  (lambda (f l n)
    (letrec ((change-rec (subr kb (terms int) terms)
               (lambda (l n)
                 (if (null? l)
                     (failwith "change")
                     (if (= n 1)
                         (cons (f (car l)) (cdr l))
                         (cons (car l) (change-rec (cdr l) (- n 1))))))))
      (change-rec l n))))

;; Term replacement replace M u N => M[u<-N]
(define* replace (subr kb (term ints term) term)
  (lambda (M u N)
    (letrec ((reprec (subr kb (term ints) term)
               (lambda (P u)
                 (if (null? u)
                     N
                     (tagcase P
                       (Term (oper sons) (Term oper (change (lambda ((P term)) (reprec P (cdr u))) sons (car u))))
                       (else o (failwith "replace")))))))
      (reprec M u))))

;; matching = - : (term -> term -> subst)
(define* matching (subr kb (term term) subst)
  (lambda (term1 term2)
    (letrec ((match-rec (subr kb (subst term term) subst)
               (lambda (subst t1 M)
                 (tagcase t1
                   (Var (v)
                     (if (mem-assoc v subst)
                         (if (term=? M (assoc v subst)) subst (failwith "matching"))
                         (the subst (cons (product (1 v) (2 M)) subst))))
                   (Term (op1 sons1)
                     (tagcase M
                       (Term (op2 sons2)
                         (if (string=? op1 op2) (it-list2 match-rec subst sons1 sons2) (failwith "matching")))
                       (else o (failwith "matching"))))))))
      (match-rec (the subst nil) term1 term2))))

;; A naive unification algorithm

(define* compsubst (subr kb (subst subst) subst)
  (lambda (subst1 subst2)
    (append (map (lambda ((b binding)) (product (1 (extract b 1)) (2 (substitute subst1 (extract b 2))))) subst2)
            subst1)))

(define* occurs (subr kb (int term) bool)
  (lambda (n t)
    (letrec ((occur-rec (subr kb (term) bool)
               (lambda (t) (tagcase t (Var (m) (= m n)) (Term (f sons) (exists occur-rec sons))))))
      (occur-rec t))))

(define* unify (subr kb (term term) subst)
  (lambda (term1 term2)
    (tagcase term1
      (Var (n1)
        (if (term=? term1 term2)
            nil
            (if (occurs n1 term2) (failwith "unify") (cons (product (1 n1) (2 term2)) nil))))
      (Term (op1 sons1)
        (tagcase term2
          (Var (n2) (if (occurs n2 term1) (failwith "unify") (cons (product (1 n2) (2 term1)) nil)))
          (Term (op2 sons2)
            (if (string=? op1 op2)
                (it-list2 (lambda ((s subst) (t1 term) (t2 term))
                            (compsubst (unify (substitute s t1) (substitute s t2)) s))
                          (the subst nil) sons1 sons2)
                (failwith "unify"))))))))

;; We need to print terms with variables independently from input terms
;; obtained by parsing. We give arbitrary names v1,v2,... to their variables.

(define INFIXES strings (cons "+" (cons "*" nil)))

(define-rec
  (pretty-term (subr kb (term) unit)
    (lambda (t)
      (tagcase t
        (Var (n) (begin (print-string "v") (print-num n)))
        (Term (oper sons)
          (if (mem-string oper INFIXES)
              (if (and (not (null? sons)) (not (null? (cdr sons))) (null? (cdr (cdr sons))))
                  (begin (pretty-close (car sons)) (print-string oper) (pretty-close (car (cdr sons))))
                  (failwith "pretty_term : infix arity <> 2"))
              (begin
                (print-string oper)
                (if (null? sons)
                    #u
                    (begin
                      (print-string "(")
                      (pretty-term (car sons))
                      (app (lambda ((t term)) (begin (print-string ",") (pretty-term t))) (cdr sons))
                      (print-string ")")))))))))
  (pretty-close (subr kb (term) unit)
    (lambda (M)
      (tagcase M
        (Term (oper sons)
          (if (mem-string oper INFIXES)
              (begin (print-string "(") (pretty-term M) (print-string ")"))
              (pretty-term M)))
        (else o (pretty-term M))))))

;;; ---------------------------------------------- Equation manipulations

;; standardizes an equation so its variables are 1,2,...
(define* mk-rule (subr kb (term term) numbered-pair)
  (lambda (M N)
    (let* ((all-vars (union (vars M) (vars N)))
           (ks (it-list (lambda ((acc (productof (1 int) (2 subst))) (v int))
                          (let ((i (extract acc 1)))
                            (product (1 (+ i 1)) (2 (the subst (cons (product (1 v) (2 (Var i))) (extract acc 2)))))))
                        (product (1 1) (2 (the subst nil)))
                        all-vars))
           (k (extract ks 1))
           (subst (extract ks 2)))
      (product (1 (- k 1)) (2 (product (1 (substitute subst M)) (2 (substitute subst N))))))))

;; checks that rules are numbered in sequence and returns their number
(define* check-rules (subr kb (rules) int)
  (lambda (l)
    (it-list (lambda ((n int) (r rule)) (if (= (extract r 1) (+ n 1)) (extract r 1) (failwith "Rule numbers not in sequence")))
             0 l)))

(define* pretty-rule (subr kb (rule) unit)
  (lambda (r)
    (let ((p (extract (extract r 2) 2)))
      (begin
        (print-num (extract r 1)) (print-string " : ")
        (pretty-term (extract p 1)) (print-string " = ") (pretty-term (extract p 2))
        (print-newline)))))

(define* pretty-rules (subr kb (rules) unit) (lambda (l) (app pretty-rule l)))

;;; --------------------------------------------------------- Rewriting

;; Top-level rewriting. Let eq:L=R be an equation, M be a term such that
;; L<=M. With sigma = matching L M, we define the image of M by eq as
;; sigma(R)
(define* reduce (subr kb (term term term) term)
  (lambda (L M R) (substitute (matching L M) R)))

;; A more efficient version of can (rewrite1 (L,R)) for R arbitrary
(define* reducible (subr kb (term term) bool)
  (lambda (L M)
    (letrec ((redrec (subr kb (term) bool)
               (lambda (M)
                 (tagcase (prompt kb-tag (begin (matching L M) (sum a-bool #t)) caught-failure)
                   (a-bool b b)
                   (else o (tagcase M (Term (f sons) (exists redrec sons)) (else o #f)))))))
      (redrec M))))

;; mreduce : rules -> term -> term
(define* mreduce (subr kb (rules term) term)
  (lambda (rules M)
    (try-find (lambda ((r rule))
                (let ((p (extract (extract r 2) 2))) (reduce (extract p 1) M (extract p 2))))
              rules)))

;; One step of rewriting in leftmost-outermost strategy, with multiple
;; rules; fails if no redex is found
(define* mrewrite1 (subr kb (rules term) term)
  (lambda (rules M)
    (letrec ((rewrec (subr kb (term) term)
               (lambda (M)
                 (tagcase (prompt kb-tag (sum a-term (mreduce rules M)) caught-failure)
                   (a-term t t)
                   (else o
                     (letrec ((tryrec (subr kb (terms) terms)
                                (lambda (l)
                                  (if (null? l)
                                      (failwith "mrewrite1")
                                      (tagcase (prompt kb-tag (sum a-terms (the terms (cons (rewrec (car l)) (cdr l)))) caught-failure)
                                        (a-terms ts ts)
                                        (else o (cons (car l) (tryrec (cdr l)))))))))
                       (tagcase M
                         (Term (f sons) (Term f (tryrec sons)))
                         (else o (failwith "mrewrite1")))))))))
      (rewrec M))))

;; Iterating rewrite1. Returns a normal form. May loop forever
(define* mrewrite-all (subr kb (rules term) term)
  (lambda (rules M)
    (letrec ((rew-loop (subr kb (term) term)
               (lambda (M)
                 (tagcase (prompt kb-tag (sum a-term (rew-loop (mrewrite1 rules M))) caught-failure)
                   (a-term t t)
                   (else o M)))))
      (rew-loop M))))

;;; ------------------------------------------- Recursive Path Ordering

(define-type order (subr kb (term term) ordering))

(define ge-ord (subr kb (order term term) bool)
  (lambda (order a b) (tagcase (order a b) (NotGE () #f) (else o #t))))
(define gt-ord (subr kb (order term term) bool)
  (lambda (order a b) (tagcase (order a b) (Greater () #t) (else o #f))))
(define eq-ord (subr kb (order term term) bool)
  (lambda (order a b) (tagcase (order a b) (Equal () #t) (else o #f))))

(define* rem-eq (subr kb ((subr kb (term term) bool) term terms) terms)
  (lambda (equiv x l)
    (letrec ((remrec (subr kb (terms) terms)
               (lambda (l)
                 (if (null? l)
                     (failwith "rem_eq")
                     (if (equiv x (car l)) (cdr l) (cons (car l) (remrec (cdr l))))))))
      (remrec l))))

(define* diff-eq (subr kb ((subr kb (term term) bool) terms terms) diff)
  (lambda (equiv x y)
    (letrec ((diffrec (subr kb (terms terms) diff)
               (lambda (a b)
                 (if (null? a)
                     (product (1 a) (2 b))
                     (tagcase (prompt kb-tag (sum a-diff (diffrec (cdr a) (rem-eq equiv (car a) b))) caught-failure)
                       (a-diff d d)
                       (else o
                         (let ((d (diffrec (cdr a) b)))
                           (product (1 (the terms (cons (car a) (extract d 1)))) (2 (extract d 2))))))))))
      (if (> (len x) (len y)) (diffrec y x) (diffrec x y)))))

;; multiset extension of order
(define* mult-ext (subr kb (order term term) ordering)
  (lambda (order M N)
    (tagcase M
      (Term (f1 sons1)
        (tagcase N
          (Term (f2 sons2)
            (let* ((d (diff-eq (lambda ((a term) (b term)) (eq-ord order a b)) sons1 sons2))
                   (l1 (extract d 1))
                   (l2 (extract d 2)))
              (if (and (null? l1) (null? l2))
                  (Equal)
                  (if (for-all (lambda ((N term))
                                 (exists (lambda ((M term)) (tagcase (order M N) (Greater () #t) (else o #f))) l1))
                               l2)
                      (Greater)
                      (NotGE)))))
          (else o (failwith "mult_ext"))))
      (else o (failwith "mult_ext")))))

;; lexicographic extension of order
(define* lex-ext (subr kb (order term term) ordering)
  (lambda (order M N)
    (tagcase M
      (Term (f1 sons1)
        (tagcase N
          (Term (f2 sons2)
            (letrec ((lexrec (subr kb (terms terms) ordering)
                       (lambda (l1 l2)
                         (if (null? l1)
                             (if (null? l2) (Equal) (NotGE))
                             (if (null? l2)
                                 (Greater)
                                 (tagcase (order (car l1) (car l2))
                                   (Greater () (if (for-all (lambda ((N2 term)) (gt-ord order M N2)) (cdr l2)) (Greater) (NotGE)))
                                   (Equal () (lexrec (cdr l1) (cdr l2)))
                                   (NotGE () (if (exists (lambda ((M2 term)) (ge-ord order M2 N)) (cdr l1)) (Greater) (NotGE)))))))))
              (lexrec sons1 sons2)))
          (else o (failwith "lex_ext"))))
      (else o (failwith "lex_ext")))))

;; recursive path ordering
(define* rpo (subr kb ((subr kb (string string) ordering) (subr kb (order term term) ordering)) order)
  (lambda (op-order ext)
    (letrec ((rporec (subr kb (term term) ordering)
               (lambda (M N)
                 (if (term=? M N)
                     (Equal)
                     (tagcase M
                       (Var (m) (NotGE))
                       (Term (op1 sons1)
                         (tagcase N
                           (Var (n) (if (occurs n M) (Greater) (NotGE)))
                           (Term (op2 sons2)
                             (tagcase (op-order op1 op2)
                               (Greater () (if (for-all (lambda ((N2 term)) (gt-ord rporec M N2)) sons2) (Greater) (NotGE)))
                               (Equal () (ext rporec M N))
                               (NotGE () (if (exists (lambda ((M2 term)) (ge-ord rporec M2 N)) sons1) (Greater) (NotGE))))))))))))
      rporec)))

;;; ---------------------------------------------------- Critical pairs

;; All (u,sig) such that N/u (&var) unifies with M, with principal
;; unifier sig
(define* super (subr kb (term term) supers)
  (lambda (M N)
    (letrec ((suprec (subr kb (term) supers)
               (lambda (N)
                 (tagcase N
                   (Term (f sons)
                     (let* ((collate (lambda ((acc (productof (1 supers) (2 int))) (son term))
                                       (let ((n (extract acc 2)))
                                         (product (1 (append (extract acc 1)
                                                             (map (lambda ((us super-pair)) (product (1 (the ints (cons n (extract us 1)))) (2 (extract us 2))))
                                                                  (suprec son))))
                                                  (2 (+ n 1))))))
                            (insides (extract (it-list collate (product (1 (the supers nil)) (2 1)) sons) 1)))
                       (tagcase (prompt kb-tag (sum a-supers (the supers (cons (product (1 (the ints nil)) (2 (unify M N))) insides))) caught-failure)
                         (a-supers l l)
                         (else o insides))))
                   (else o (the supers nil))))))
      (suprec N))))

;; All (u,sigma), u&[], such that N/u unifies with M
(define* super-strict (subr kb (term term) supers)
  (lambda (M N)
    (tagcase N
      (Term (f sons)
        (let ((collate (lambda ((acc (productof (1 supers) (2 int))) (son term))
                         (let ((n (extract acc 2)))
                           (product (1 (append (extract acc 1)
                                               (map (lambda ((us super-pair)) (product (1 (the ints (cons n (extract us 1)))) (2 (extract us 2))))
                                                    (super M son))))
                                    (2 (+ n 1)))))))
          (extract (it-list collate (product (1 (the supers nil)) (2 1)) sons) 1)))
      (else o (the supers nil)))))

;; Critical pairs of L1=R1 with L2=R2
(define* critical-pairs (subr kb (tpair tpair) tpairs)
  (lambda (e1 e2)
    (let ((L1 (extract e1 1)) (R1 (extract e1 2)) (L2 (extract e2 1)) (R2 (extract e2 2)))
      (map (lambda ((us super-pair))
             (product (1 (substitute (extract us 2) (replace L2 (extract us 1) R1)))
                      (2 (substitute (extract us 2) R2))))
           (super L1 L2)))))

;; Strict critical pairs of L1=R1 with L2=R2
(define* strict-critical-pairs (subr kb (tpair tpair) tpairs)
  (lambda (e1 e2)
    (let ((L1 (extract e1 1)) (R1 (extract e1 2)) (L2 (extract e2 1)) (R2 (extract e2 2)))
      (map (lambda ((us super-pair))
             (product (1 (substitute (extract us 2) (replace L2 (extract us 1) R1)))
                      (2 (substitute (extract us 2) R2))))
           (super-strict L1 L2)))))

;; All critical pairs of eq1 with eq2
(define* mutual-critical-pairs (subr kb (tpair tpair) tpairs)
  (lambda (eq1 eq2) (append (strict-critical-pairs eq1 eq2) (critical-pairs eq2 eq1))))

;; Renaming of variables
(define* rename (subr kb (int tpair) tpair)
  (lambda (n p)
    (letrec ((ren-rec (subr kb (term) term)
               (lambda (t) (tagcase t (Var (k) (Var (+ k n))) (Term (oper sons) (Term oper (map ren-rec sons)))))))
      (product (1 (ren-rec (extract p 1))) (2 (ren-rec (extract p 2)))))))

;;; -------------------------------------------------------- Completion

(define* deletion-message (subr kb (rule) unit)
  (lambda (r) (begin (print-string "Rule ") (print-num (extract r 1)) (message " deleted"))))

;; Generate failure message
(define* non-orientable (subr kb (tpair) unit)
  (lambda (p) (begin (pretty-term (extract p 1)) (print-string " = ") (pretty-term (extract p 2)) (print-newline))))

;; Improved Knuth-Bendix completion procedure
(define* kbrec (subr kb ((subr kb (term term) bool) int rules tpairs int int tpairs) rules)
  (lambda (greater n rules failures k l eqs)
    (letrec ((normal-form (subr kb (term) term) (lambda (M) (mrewrite-all rules M)))
             (get-rule (subr kb (int) numbered-pair) (lambda (k) (assoc k rules)))
             (processkl (subr kb (tpairs int int tpairs) rules)
               (lambda (failures k l eqs)
                 (if (null? eqs)
                     (if (< k l)
                         (next-criticals failures (+ k 1) l)
                         (if (< l n)
                             (next-criticals failures 1 (+ l 1))
                             (if (null? failures)
                                 rules ; successful completion
                                 (begin
                                   (message "Non-orientable equations :")
                                   (app non-orientable failures)
                                   (failwith "kb_completion")))))
                     (let* ((M2 (normal-form (extract (car eqs) 1)))
                            (N2 (normal-form (extract (car eqs) 2)))
                            (eqs (cdr eqs))
                            (enter-rule
                              (lambda ((left term) (right term))
                                (let ((new-rule (product (1 (+ n 1)) (2 (mk-rule left right)))))
                                  (begin
                                    (pretty-rule new-rule)
                                    (let* ((left-reducible (lambda ((r rule)) (reducible left (extract (extract (extract r 2) 2) 1))))
                                           (rl (partition left-reducible rules))
                                           (redl (extract rl 1))
                                           (irredl (extract rl 2)))
                                      (begin
                                        (app deletion-message redl)
                                        (let* ((right-reduce
                                                 (lambda ((r rule))
                                                   (let ((p (extract (extract r 2) 2)))
                                                     (product (1 (extract r 1))
                                                              (2 (mk-rule (extract p 1) (mrewrite-all (the rules (cons new-rule rules)) (extract p 2))))))))
                                               (irreds (map right-reduce irredl))
                                               (eqs2 (map (lambda ((r rule)) (extract (extract r 2) 2)) redl)))
                                          (kbrec greater (+ n 1) (the rules (cons new-rule irreds)) (the tpairs nil) k l
                                                 (append eqs (append eqs2 failures)))))))))))
                       (if (term=? M2 N2)
                           (processkl failures k l eqs)
                           (if (greater M2 N2)
                               (enter-rule M2 N2)
                               (if (greater N2 M2)
                                   (enter-rule N2 M2)
                                   (processkl (the tpairs (cons (product (1 M2) (2 N2)) failures)) k l eqs))))))))
             (next-criticals (subr kb (tpairs int int) rules)
               (lambda (failures k l)
                 (tagcase
                   (prompt kb-tag
                     (sum a-rules
                       (let* ((vel (get-rule l)) (v (extract vel 1)) (el (extract vel 2)))
                         (if (= k l)
                             (processkl failures k l (strict-critical-pairs el (rename v el)))
                             (tagcase
                               (prompt kb-tag
                                 (sum a-rules
                                   (let ((ek (extract (get-rule k) 2)))
                                     (processkl failures k l (mutual-critical-pairs el (rename v ek)))))
                                 caught-failure)
                               (a-rules rs rs)
                               ;; rule k deleted
                               (failure s (if (string=? s "find") (next-criticals failures (+ k 1) l) (failwith s)))
                               (else o (failwith "impossible"))))))
                     caught-failure)
                   (a-rules rs rs)
                   ;; rule l deleted
                   (failure s (if (string=? s "find") (next-criticals failures 1 (+ l 1)) (failwith s)))
                   (else o (failwith "impossible"))))))
      (processkl failures k l eqs))))

(define* kb-complete (subr kb ((subr kb (term term) bool) rules rules) rules)
  (lambda (greater complete-rules rules)
    (let* ((n (check-rules complete-rules))
           (eqs (map (lambda ((r rule)) (extract (extract r 2) 2)) rules))
           (completed-rules (kbrec greater n complete-rules (the tpairs nil) n n eqs)))
      (begin
        (message "Canonical set found :")
        (pretty-rules (rev completed-rules))
        completed-rules))))

(define* r (subr (alloc @heap) (int int term term) rule)
  (lambda (k v M N) (product (1 k) (2 (product (1 v) (2 (product (1 M) (2 N))))))))
(define* t0 (subr (alloc @heap) (string) term) (lambda (f) (Term f nil)))
(define* t1 (subr (alloc @heap) (string term) term) (lambda (f a) (Term f (cons a nil))))
(define* t2 (subr (alloc @heap) (string term term) term) (lambda (f a b) (Term f (cons a (cons b nil)))))

(define Geom-rules rules
  (cons (r 1 1 (t2 "*" (t0 "U") (Var 1)) (Var 1))
  (cons (r 2 1 (t2 "*" (t1 "I" (Var 1)) (Var 1)) (t0 "U"))
  (cons (r 3 3 (t2 "*" (t2 "*" (Var 1) (Var 2)) (Var 3))
               (t2 "*" (Var 1) (t2 "*" (Var 2) (Var 3))))
  (cons (r 4 0 (t2 "*" (t0 "A") (t0 "B"))
               (t2 "*" (t0 "B") (t0 "A")))
  (cons (r 5 0 (t2 "*" (t0 "C") (t0 "C")) (t0 "U"))
  (cons (r 6 0 (t2 "*" (t0 "C") (t2 "*" (t0 "A") (t1 "I" (t0 "C"))))
               (t1 "I" (t0 "A")))
  (cons (r 7 0 (t2 "*" (t0 "C") (t2 "*" (t0 "B") (t1 "I" (t0 "C"))))
               (t0 "B"))
  nil))))))))

(define* Group-rank (subr kb (string) int)
  (lambda (s)
    (cond ((string=? s "U") 0)
          ((string=? s "*") 1)
          ((string=? s "I") 2)
          ((string=? s "B") 3)
          ((string=? s "C") 4)
          ((string=? s "A") 5)
          (else (failwith "Group_rank")))))

(define* Group-precedence (subr kb (string string) ordering)
  (lambda (op1 op2)
    (let ((r1 (Group-rank op1)) (r2 (Group-rank op2)))
      (if (= r1 r2) (Equal) (if (> r1 r2) (Greater) (NotGE))))))

(define Group-order order (rpo Group-precedence lex-ext))

(define* greater (subr kb (term term) bool)
  (lambda (M N) (tagcase (Group-order M N) (Greater () #t) (else o #f))))

(define* doit (subr kb () int)
  (lambda () (len (kb-complete greater (the rules nil) Geom-rules))))

;; The input, where no compiler can fold it: a global, which a later
;; definition may replace.
(define iterations int 1)

(define* run (subr kb (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (doit)))))
(run iterations 0)
