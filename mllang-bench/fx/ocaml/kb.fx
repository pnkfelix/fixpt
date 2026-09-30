;;; KB -- Knuth-Bendix completion of the axioms of a group (with some
;;; extra equations), under a recursive path ordering.
;;;
;;; From OCaml's classic test programs (testsuite/tests/misc-kb/: terms.ml,
;;; equations.ml, orderings.ml, kb.ml, kbmain.ml, ocaml commit
;;; 7da997d28b1a), ported to FX-26; the modules are plain definitions, in
;;; that order. The original completes `geom_rules` once, printing each
;;; rule as it is made, each rule deleted, and the canonical set found (the
;;; 273 lines of kbmain.reference). The port completes it `iterations` = 1
;;; time, as the original does (natively that already takes some seconds:
;;; see the note on prompts below), and where the original prints, it
;;; hashes: each character printed updates h := (h * 131 + code) mod
;;; 1000000007, from h = 0 at each completion. Answer: 242769383, which is that hash of the reference
;;; output's 6256 characters.
;;;
;;; What the port changes:
;;; - Exceptions, which the original uses for control throughout
;;;   (`failwith` for a match or unification that fails, `Not_found` for a
;;;   rule or variable not there): two prompt tags, `failure` and
;;;   `not-found`. A prompt tag has one answer type, and one `try` is at
;;;   type term, another at bool, and so on, so a prompt's body gives back
;;;   an `outcome`, a sum with a variant for each such type, and its handler
;;;   `(failed)`; the code after it takes the outcome apart. A `raise` is an
;;;   abort to the tag. `failwith`'s message is dropped: every handler here
;;;   is `Failure _`. Every procedure that may raise says `(goto @f)`, and
;;;   since those procedures are globals, no prompt masks it. The prompts
;;;   nest deep (`mrewrite_all` and `next_criticals` recur inside their
;;;   `try`s, as in the original), and natively an abort costs time in
;;;   proportion to the stack beneath it, so this port runs natively about
;;;   five times slower than lowered to Scheme.
;;; - Records and tuples are products; a tuple argument, as in
;;;   `kb_completion`'s (k,l), is two arguments where the procedure is
;;;   written out whole. `kb_completion`'s curried closures `kbrec` and
;;;   `process` take their arguments at once.
;;; - The `List` functions used are written here: `map`, `iter`,
;;;   `exists`, `for_all`, `rev`, `@`, `length`, `partition` polymorphically;
;;;   `mem`, `assoc` and `mem_assoc` at the types used. `map` applies its
;;;   function from the front, as OCaml's does. `fold_left2` stops at the
;;;   shorter list where OCaml's raises Invalid_argument: here the lists
;;;   are always as long as each other. Structural equality on terms is
;;;   `term=?`.
;;; - `assert false` in `group_rank` (an operator not in the rules) gives
;;;   -1: it never happens.

;;;; The effects: kb for what may raise, kb-body for a prompt's body.
(define-effect kb (maxeff (read @heap) (write @heap) (alloc @heap) spin (goto @f) (read @globals)))
(define-effect kb-body (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)))

;;;; Lists, as the OCaml library has them.

(define* list-map (poly ((a type) (b type)) (subr kb ((subr kb (a) b) (listof a @heap)) (listof b @heap)))
  (lambda (f l)
    (if (null? l) nil (let ((r (f (car l)))) (cons r (list-map f (cdr l)))))))

(define* list-iter (poly ((a type)) (subr kb ((subr kb (a) unit) (listof a @heap)) unit))
  (lambda (f l)
    (if (null? l) #u (begin (f (car l)) (list-iter f (cdr l))))))

(define* list-exists (poly ((a type)) (subr kb ((subr kb (a) bool) (listof a @heap)) bool))
  (lambda (p l)
    (if (null? l) #f (or (p (car l)) (list-exists p (cdr l))))))

(define* list-for-all (poly ((a type)) (subr kb ((subr kb (a) bool) (listof a @heap)) bool))
  (lambda (p l)
    (if (null? l) #t (and (p (car l)) (list-for-all p (cdr l))))))

(define* list-append (poly ((a type)) (subr kb ((listof a @heap) (listof a @heap)) (listof a @heap)))
  (lambda (l1 l2)
    (if (null? l1) l2 (cons (car l1) (list-append (cdr l1) l2)))))

(define* list-rev-append (poly ((a type)) (subr kb ((listof a @heap) (listof a @heap)) (listof a @heap)))
  (lambda (l1 l2)
    (if (null? l1) l2 (list-rev-append (cdr l1) (cons (car l1) l2)))))

(define* list-rev (poly ((a type)) (subr kb ((listof a @heap)) (listof a @heap)))
  (lambda (l) (list-rev-append l nil)))

(define* list-fold-left2 (poly ((a type) (b type) (c type))
                           (subr kb ((subr kb (a b c) a) a (listof b @heap) (listof c @heap)) a))
  (lambda (f accu l1 l2)
    (if (or (null? l1) (null? l2))
        accu
        (list-fold-left2 f (f accu (car l1) (car l2)) (cdr l1) (cdr l2)))))

(define* length-of (poly ((a type)) (subr kb ((listof a @heap)) int))
  (lambda (l) (if (null? l) 0 (+ 1 (length-of (cdr l))))))

(define* mem-int (subr kb (int (listof int @heap)) bool)
  (lambda (a l) (if (null? l) #f (or (= a (car l)) (mem-int a (cdr l))))))

(define* mem-string (subr kb (string (listof string @heap)) bool)
  (lambda (a l) (if (null? l) #f (or (string=? a (car l)) (mem-string a (cdr l))))))

;;;; Printing, hashed.

(define out-hash (ref int @heap) (new 0))

(define* print-string (subr kb (string) unit)
  (lambda (s)
    (letrec ((loop (subr kb (int) unit)
               (lambda (i)
                 (if (< i (string-length s))
                     (begin
                       (set out-hash (modulo (+ (* (get out-hash) 131) (char->integer (string-ref s i)))
                                             1000000007))
                       (loop (+ i 1)))
                     #u))))
      (loop 0))))

(define* print-int (subr kb (int) unit) (lambda (n) (print-string (int->string n))))
(define* print-newline (subr kb () unit) (lambda () (print-string "\n")))

;;;; Terms, and what the exceptions carry across a prompt.

(define-datatype term (t-var int) (t-term string (listof term @heap)))
(define-type terms (listof term @heap))
(define-type ints (listof int @heap))
(define-type binding (productof (v int) (t term)))
(define-type subst (listof binding @heap))
(define-type tpair (productof (fst term) (snd term)))
(define-type tpairs (listof tpair @heap))
(define-type super-item (productof (u ints) (s subst)))
(define-type supers (listof super-item @heap))
(define-type rule (productof (number int) (numvars int) (lhs term) (rhs term)))
(define-type rules (listof rule @heap))
(define-type tpairs-pair (productof (fst tpairs) (snd tpairs)))
(define-type terms-pair (productof (fst terms) (snd terms)))

(define-datatype outcome
  (ok-term term)
  (ok-terms (listof term @heap))
  (ok-bool bool)
  (ok-subst (listof (productof (v int) (t term)) @heap))
  (ok-supers (listof (productof (u (listof int @heap)) (s (listof (productof (v int) (t term)) @heap))) @heap))
  (ok-terms-pair (productof (fst (listof term @heap)) (snd (listof term @heap))))
  (ok-rules (listof (productof (number int) (numvars int) (lhs term) (rhs term)) @heap))
  (failed))

;; exception Failure, and exception Not_found
(define failure (prompt-tag outcome unit kb-body @f) (make-continuation-prompt-tag))
(define not-found (prompt-tag outcome unit kb-body @f) (make-continuation-prompt-tag))

(define* failwith (subr kb (string) void)
  (lambda (message) (abort-current-continuation failure #u)))

;;;; terms.ml: Term manipulations

(define* term=? (subr kb (term term) bool)
  (lambda (t1 t2)
    (tagcase t1
      (t-var (n1) (tagcase t2 (t-var (n2) (= n1 n2)) (else x #f)))
      (t-term (op1 sons1)
        (tagcase t2
          (t-term (op2 sons2)
            (and (string=? op1 op2)
                 (letrec ((each (subr kb (terms terms) bool)
                            (lambda (l1 l2)
                              (cond ((null? l1) (null? l2))
                                    ((null? l2) #f)
                                    (else (and (term=? (car l1) (car l2)) (each (cdr l1) (cdr l2))))))))
                   (each sons1 sons2))))
          (else x #f))))))

(define* union (subr kb (ints ints) ints)
  (lambda (l1 l2)
    (if (null? l1)
        l2
        (let ((a (car l1)) (r (cdr l1)))
          (if (mem-int a l2) (union r l2) (cons a (union r l2)))))))

(define-rec
  (vars (subr kb (term) ints)
    (lambda (t)
      (tagcase t
        (t-var (n) (cons n nil))
        (t-term (op l) (vars-of-list l)))))
  (vars-of-list (subr kb (terms) ints)
    (lambda (l)
      (if (null? l) nil (union (vars (car l)) (vars-of-list (cdr l)))))))

(define* list-assoc (subr kb (int subst) term)
  (lambda (n l)
    (cond ((null? l) (abort-current-continuation not-found #u))
          ((= (extract (car l) v) n) (extract (car l) t))
          (else (list-assoc n (cdr l))))))

(define* list-mem-assoc (subr kb (int subst) bool)
  (lambda (n l)
    (if (null? l) #f (or (= (extract (car l) v) n) (list-mem-assoc n (cdr l))))))

(define* substitute (subr kb (subst term) term)
  (lambda (subst t)
    (tagcase t
      (t-term (oper sons) (t-term oper (list-map (lambda ((s term)) (substitute subst s)) sons)))
      (t-var (n)
        (tagcase (prompt not-found (ok-term (list-assoc n subst)) (lambda (u) (failed)))
          (ok-term (x) x)
          (else y t))))))

;; Term replacement: replace M u N is M[u<-N].
(define-rec
  (replace (subr kb (term ints term) term)
    (lambda (m u n)
      (if (null? u)
          n
          (tagcase m
            (t-term (oper sons) (t-term oper (replace-nth (car u) sons (cdr u) n)))
            (else x (failwith "replace"))))))
  (replace-nth (subr kb (int terms ints term) terms)
    (lambda (i sons u n)
      (if (null? sons)
          (failwith "replace_nth")
          (let ((s (car sons)) (r (cdr sons)))
            (if (= i 1)
                (cons (replace s u n) r)
                (cons s (replace-nth (- i 1) r u n))))))))

;; Term matching.
(define* matching (subr kb (term term) subst)
  (lambda (term1 term2)
    (letrec ((match-rec (subr kb (subst term term) subst)
               (lambda (subst t1 t2)
                 (tagcase t1
                   (t-var (v)
                     (if (list-mem-assoc v subst)
                         (if (term=? t2 (list-assoc v subst)) subst (failwith "matching"))
                         (cons (product (v v) (t t2)) subst)))
                   (t-term (op1 sons1)
                     (tagcase t2
                       (t-term (op2 sons2)
                         (if (string=? op1 op2)
                             (list-fold-left2 match-rec subst sons1 sons2)
                             (failwith "matching")))
                       (else x (failwith "matching"))))))))
      (match-rec nil term1 term2))))

;; A naive unification algorithm.

(define* compsubst (subr kb (subst subst) subst)
  (lambda (subst1 subst2)
    (list-append (list-map (lambda ((b binding)) (product (v (extract b v)) (t (substitute subst1 (extract b t)))))
                           subst2)
                 subst1)))

(define* occurs (subr kb (int term) bool)
  (lambda (n t)
    (tagcase t
      (t-var (m) (= m n))
      (t-term (op sons) (list-exists (lambda ((s term)) (occurs n s)) sons)))))

(define* unify (subr kb (term term) subst)
  (lambda (term1 term2)
    (tagcase term1
      (t-var (n1)
        (cond ((term=? term1 term2) nil)
              ((occurs n1 term2) (failwith "unify"))
              (else (cons (product (v n1) (t term2)) nil))))
      (t-term (op1 sons1)
        (tagcase term2
          (t-var (n2)
            (if (occurs n2 term1)
                (failwith "unify")
                (cons (product (v n2) (t term1)) nil)))
          (t-term (op2 sons2)
            (if (string=? op1 op2)
                (list-fold-left2 (lambda ((s subst) (t1 term) (t2 term))
                                   (compsubst (unify (substitute s t1) (substitute s t2)) s))
                                 (the subst nil) sons1 sons2)
                (failwith "unify"))))))))

;; We need to print terms with variables independently from input terms
;; obtained by parsing. We give arbitrary names v1,v2,... to their variables.

(define infixes (listof string @heap) (list "+" "*"))

(define-rec
  (pretty-term (subr kb (term) unit)
    (lambda (t)
      (tagcase t
        (t-var (n) (begin (print-string "v") (print-int n)))
        (t-term (oper sons)
          (if (mem-string oper infixes)
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
                      (list-iter (lambda ((t term)) (begin (print-string ",") (pretty-term t))) (cdr sons))
                      (print-string ")")))))))))
  (pretty-close (subr kb (term) unit)
    (lambda (m)
      (tagcase m
        (t-term (oper sons)
          (if (mem-string oper infixes)
              (begin (print-string "(") (pretty-term m) (print-string ")"))
              (pretty-term m)))
        (else x (pretty-term m))))))

;;;; equations.ml: Equation manipulations

;; standardizes an equation so its variables are 1,2,...
(define* mk-rule (subr kb (int term term) rule)
  (lambda (num m n)
    (let* ((all-vars (union (vars m) (vars n)))
           (counter (the (ref int @heap) (new 0)))
           (subst (list-map (lambda ((v int))
                              (begin (set counter (+ (get counter) 1))
                                     (product (v v) (t (t-var (get counter))))))
                            (list-rev all-vars))))
      (product (number num)
               (numvars (get counter))
               (lhs (substitute subst m))
               (rhs (substitute subst n))))))

;; checks that rules are numbered in sequence and returns their number
(define* check-rules (subr kb (rules) int)
  (lambda (rules)
    (let ((counter (the (ref int @heap) (new 0))))
      (begin
        (list-iter (lambda ((r rule))
                     (begin
                       (set counter (+ (get counter) 1))
                       (if (not (= (extract r number) (get counter)))
                           (failwith "Rule numbers not in sequence")
                           #u)))
                   rules)
        (get counter)))))

(define* pretty-rule (subr kb (rule) unit)
  (lambda (rule)
    (begin
      (print-int (extract rule number)) (print-string " : ")
      (pretty-term (extract rule lhs)) (print-string " = ") (pretty-term (extract rule rhs))
      (print-newline))))

(define* pretty-rules (subr kb (rules) unit)
  (lambda (rules) (list-iter pretty-rule rules)))

;;;; Rewriting

;; Top-level rewriting. Let eq:L=R be an equation, M be a term such that L<=M.
;; With sigma = matching L M, we define the image of M by eq as sigma(R)
(define* reduce (subr kb (term term term) term)
  (lambda (l m r) (substitute (matching l m) r)))

;; Test whether m can be reduced by l, i.e. m contains an instance of l.
(define* can-match (subr kb (term term) bool)
  (lambda (l m)
    (tagcase (prompt failure (begin (matching l m) (ok-bool #t)) (lambda (u) (failed)))
      (ok-bool (b) b)
      (else x #f))))

(define* reducible (subr kb (term term) bool)
  (lambda (l m)
    (or (can-match l m)
        (tagcase m
          (t-term (op sons) (list-exists (lambda ((s term)) (reducible l s)) sons))
          (else x #f)))))

;; Top-level rewriting with multiple rules.
(define* mreduce (subr kb (rules term) term)
  (lambda (rules m)
    (if (null? rules)
        (failwith "mreduce")
        (let ((rule (car rules)) (rest (cdr rules)))
          (tagcase (prompt failure (ok-term (reduce (extract rule lhs) m (extract rule rhs)))
                     (lambda (u) (failed)))
            (ok-term (t) t)
            (else x (mreduce rest m)))))))

;; One step of rewriting in leftmost-outermost strategy,
;; with multiple rules. Fails if no redex is found
(define-rec
  (mrewrite1 (subr kb (rules term) term)
    (lambda (rules m)
      (tagcase (prompt failure (ok-term (mreduce rules m)) (lambda (u) (failed)))
        (ok-term (t) t)
        (else x
          (tagcase m
            (t-var (n) (failwith "mrewrite1"))
            (t-term (f sons) (t-term f (mrewrite1-sons rules sons))))))))
  (mrewrite1-sons (subr kb (rules terms) terms)
    (lambda (rules l)
      (if (null? l)
          (failwith "mrewrite1")
          (let ((son (car l)) (rest (cdr l)))
            (tagcase (prompt failure (ok-terms (cons (mrewrite1 rules son) rest)) (lambda (u) (failed)))
              (ok-terms (ts) ts)
              (else x (cons son (mrewrite1-sons rules rest)))))))))

;; Iterating rewrite1. Returns a normal form. May loop forever
(define* mrewrite-all (subr kb (rules term) term)
  (lambda (rules m)
    (tagcase (prompt failure (ok-term (mrewrite-all rules (mrewrite1 rules m))) (lambda (u) (failed)))
      (ok-term (t) t)
      (else x m))))

;;;; orderings.ml: Recursive Path Ordering

(define-datatype ordering (o-greater) (o-equal) (o-notge))
(define greater-v ordering (o-greater))
(define equal-v ordering (o-equal))
(define notge-v ordering (o-notge))
(define-type order-fn (subr kb (tpair) ordering))

(define* ge-ord (subr kb (order-fn tpair) bool)
  (lambda (order pair) (tagcase (order pair) (o-notge () #f) (else x #t))))
(define* gt-ord (subr kb (order-fn tpair) bool)
  (lambda (order pair) (tagcase (order pair) (o-greater () #t) (else x #f))))
(define* eq-ord (subr kb (order-fn tpair) bool)
  (lambda (order pair) (tagcase (order pair) (o-equal () #t) (else x #f))))

(define* rem-eq (subr kb ((subr kb (tpair) bool) term terms) terms)
  (lambda (equiv x l)
    (if (null? l)
        (failwith "rem_eq")
        (let ((y (car l)))
          (if (equiv (product (fst x) (snd y))) (cdr l) (cons y (rem-eq equiv x (cdr l))))))))

(define* diff-eq (subr kb ((subr kb (tpair) bool) terms terms) terms-pair)
  (lambda (equiv x y)
    (letrec ((diffrec (subr kb (terms terms) terms-pair)
               (lambda (a b)
                 (if (null? a)
                     (product (fst a) (snd b))
                     (let ((h (car a)) (t (cdr a)))
                       (tagcase (prompt failure (ok-terms-pair (diffrec t (rem-eq equiv h b)))
                                  (lambda (u) (failed)))
                         (ok-terms-pair (p) p)
                         (else z
                           (let ((p (diffrec t b)))
                             (product (fst (cons h (extract p fst))) (snd (extract p snd)))))))))))
      (if (> (length-of x) (length-of y)) (diffrec y x) (diffrec x y)))))

;; Multiset extension of order
(define* mult-ext (subr kb (order-fn tpair) ordering)
  (lambda (order pair)
    (tagcase (extract pair fst)
      (t-term (op1 sons1)
        (tagcase (extract pair snd)
          (t-term (op2 sons2)
            (let* ((d (diff-eq (lambda ((p tpair)) (eq-ord order p)) sons1 sons2))
                   (l1 (extract d fst))
                   (l2 (extract d snd)))
              (if (and (null? l1) (null? l2))
                  equal-v
                  (if (list-for-all
                       (lambda ((n term))
                         (list-exists (lambda ((m term)) (gt-ord order (product (fst m) (snd n)))) l1))
                       l2)
                      greater-v
                      notge-v))))
          (else x (failwith "mult_ext"))))
      (else x (failwith "mult_ext")))))

;; Lexicographic extension of order
(define* lex-ext (subr kb (order-fn tpair) ordering)
  (lambda (order pair)
    (let ((m (extract pair fst)) (n (extract pair snd)))
      (tagcase m
        (t-term (op1 sons1)
          (tagcase n
            (t-term (op2 sons2)
              (letrec ((lexrec (subr kb (terms terms) ordering)
                         (lambda (l1 l2)
                           (cond ((and (null? l1) (null? l2)) equal-v)
                                 ((null? l1) notge-v)
                                 ((null? l2) greater-v)
                                 (else
                                  (let ((x1 (car l1)) (x2 (car l2)))
                                    (tagcase (order (product (fst x1) (snd x2)))
                                      (o-greater ()
                                        (if (list-for-all (lambda ((n2 term)) (gt-ord order (product (fst m) (snd n2))))
                                                          (cdr l2))
                                            greater-v
                                            notge-v))
                                      (o-equal () (lexrec (cdr l1) (cdr l2)))
                                      (o-notge ()
                                        (if (list-exists (lambda ((m2 term)) (ge-ord order (product (fst m2) (snd n))))
                                                         (cdr l1))
                                            greater-v
                                            notge-v)))))))))
                (lexrec sons1 sons2)))
            (else x (failwith "lex_ext"))))
        (else x (failwith "lex_ext"))))))

;; Recursive path ordering
(define* rpo (subr kb ((subr kb (string string) ordering) (subr kb (order-fn tpair) ordering)) order-fn)
  (lambda (op-order ext)
    (letrec ((rporec (subr kb (tpair) ordering)
               (lambda (pair)
                 (let ((m (extract pair fst)) (n (extract pair snd)))
                   (if (term=? m n)
                       equal-v
                       (tagcase m
                         (t-var (vm) notge-v)
                         (t-term (op1 sons1)
                           (tagcase n
                             (t-var (vn) (if (occurs vn m) greater-v notge-v))
                             (t-term (op2 sons2)
                               (tagcase (op-order op1 op2)
                                 (o-greater ()
                                   (if (list-for-all (lambda ((n2 term)) (gt-ord rporec (product (fst m) (snd n2)))) sons2)
                                       greater-v
                                       notge-v))
                                 (o-equal () (ext rporec pair))
                                 (o-notge ()
                                   (if (list-exists (lambda ((m2 term)) (ge-ord rporec (product (fst m2) (snd n)))) sons1)
                                       greater-v
                                       notge-v))))))))))))
      rporec)))

;;;; kb.ml: Critical pairs

;; All (u,subst) such that N/u (&var) unifies with M,
;; with principal unifier subst
(define* super (subr kb (term term) supers)
  (lambda (m n)
    (tagcase n
      (t-term (op sons)
        (letrec ((collate (subr kb (int terms) supers)
                   (lambda (n l)
                     (if (null? l)
                         nil
                         (list-append
                          (list-map (lambda ((it super-item)) (the super-item (product (u (cons n (extract it u))) (s (extract it s)))))
                                    (super m (car l)))
                          (collate (+ n 1) (cdr l)))))))
          (let ((insides (collate 1 sons)))
            (tagcase (prompt failure (ok-supers (cons (product (u nil) (s (unify m n))) insides))
                       (lambda (u) (failed)))
              (ok-supers (l) l)
              (else x insides)))))
      (else x nil))))

;; All (u,subst), u&[], such that n/u unifies with m
(define* super-strict (subr kb (term term) supers)
  (lambda (m n)
    (tagcase n
      (t-term (op sons)
        (letrec ((collate (subr kb (int terms) supers)
                   (lambda (n l)
                     (if (null? l)
                         nil
                         (list-append
                          (list-map (lambda ((it super-item)) (the super-item (product (u (cons n (extract it u))) (s (extract it s)))))
                                    (super m (car l)))
                          (collate (+ n 1) (cdr l)))))))
          (collate 1 sons)))
      (else x nil))))

;; Critical pairs of l1=r1 with l2=r2
(define* critical-pairs (subr kb (tpair tpair) tpairs)
  (lambda (e1 e2)
    (let ((l1 (extract e1 fst)) (r1 (extract e1 snd)) (l2 (extract e2 fst)) (r2 (extract e2 snd)))
      (list-map (lambda ((it super-item))
                  (let ((subst (extract it s)))
                    (product (fst (substitute subst (replace l2 (extract it u) r1)))
                             (snd (substitute subst r2)))))
                (super l1 l2)))))

;; Strict critical pairs of l1=r1 with l2=r2
(define* strict-critical-pairs (subr kb (tpair tpair) tpairs)
  (lambda (e1 e2)
    (let ((l1 (extract e1 fst)) (r1 (extract e1 snd)) (l2 (extract e2 fst)) (r2 (extract e2 snd)))
      (list-map (lambda ((it super-item))
                  (let ((subst (extract it s)))
                    (product (fst (substitute subst (replace l2 (extract it u) r1)))
                             (snd (substitute subst r2)))))
                (super-strict l1 l2)))))

;; All critical pairs of eq1 with eq2
(define* mutual-critical-pairs (subr kb (tpair tpair) tpairs)
  (lambda (eq1 eq2)
    (list-append (strict-critical-pairs eq1 eq2) (critical-pairs eq2 eq1))))

;; Renaming of variables
(define* rename (subr kb (int tpair) tpair)
  (lambda (n p)
    (letrec ((ren-rec (subr kb (term) term)
               (lambda (t)
                 (tagcase t
                   (t-var (k) (t-var (+ k n)))
                   (t-term (op sons) (t-term op (list-map ren-rec sons)))))))
      (product (fst (ren-rec (extract p fst))) (snd (ren-rec (extract p snd)))))))

;;;; Completion

(define* deletion-message (subr kb (rule) unit)
  (lambda (rule)
    (begin (print-string "Rule ") (print-int (extract rule number)) (print-string " deleted")
           (print-newline))))

;; Generate failure message
(define* non-orientable (subr kb (tpair) unit)
  (lambda (p)
    (begin (pretty-term (extract p fst)) (print-string " = ") (pretty-term (extract p snd))
           (print-newline))))

(define* partition (poly ((a type)) (subr kb ((subr kb (a) bool) (listof a @heap))
                                          (productof (yes (listof a @heap)) (no (listof a @heap)))))
  (lambda (p l)
    (if (null? l)
        (product (yes nil) (no nil))
        (let* ((x (car l))
               (r (partition p (cdr l)))
               (l1 (extract r yes))
               (l2 (extract r no)))
          (if (p x) (product (yes (cons x l1)) (no l2)) (product (yes l1) (no (cons x l2))))))))

(define* get-rule (subr kb (int rules) rule)
  (lambda (n l)
    (cond ((null? l) (abort-current-continuation not-found #u))
          ((= n (extract (car l) number)) (car l))
          (else (get-rule n (cdr l))))))

;; Improved Knuth-Bendix completion procedure
(define* kb-completion (subr kb ((subr kb (tpair) bool) int rules tpairs int int tpairs) rules)
  (lambda (greater j0 rules0 failures0 k0 l0 eqs0)
    (letrec
        ((kbrec (subr kb (int rules tpairs int int tpairs) rules)
           (lambda (j rules failures1 k1 l1 eqs1)
             (letrec
                 ((process (subr kb (tpairs int int tpairs) rules)
                    (lambda (failures k l eqs)
                      (if (null? eqs)
                          (cond ((< k l) (next-criticals failures (+ k 1) l))
                                ((< l j) (next-criticals failures 1 (+ l 1)))
                                ((null? failures) rules) ; successful completion
                                (else
                                 (begin
                                   (print-string "Non-orientable equations :") (print-newline)
                                   (list-iter non-orientable failures)
                                   (failwith "kb_completion"))))
                          (let* ((m (extract (car eqs) fst))
                                 (n (extract (car eqs) snd))
                                 (eqs (cdr eqs))
                                 (m2 (mrewrite-all rules m))
                                 (n2 (mrewrite-all rules n)))
                            (cond ((term=? m2 n2) (process failures k l eqs))
                                  ((greater (product (fst m2) (snd n2))) (enter-rule m2 n2 failures k l eqs))
                                  ((greater (product (fst n2) (snd m2))) (enter-rule n2 m2 failures k l eqs))
                                  (else (process (cons (product (fst m2) (snd n2)) failures) k l eqs)))))))
                  (enter-rule (subr kb (term term tpairs int int tpairs) rules)
                    (lambda (left right failures k l eqs)
                      (let ((new-rule (mk-rule (+ j 1) left right)))
                        (begin
                          (pretty-rule new-rule)
                          (let* ((left-reducible (lambda ((rule rule)) (reducible left (extract rule lhs))))
                                 (parts (partition left-reducible rules))
                                 (redl (extract parts yes))
                                 (irredl (extract parts no)))
                            (begin
                              (list-iter deletion-message redl)
                              (let* ((right-reduce
                                      (lambda ((rule rule))
                                        (mk-rule (extract rule number) (extract rule lhs)
                                                 (mrewrite-all (cons new-rule rules) (extract rule rhs)))))
                                     (irreds (list-map right-reduce irredl))
                                     (eqs2 (list-map (lambda ((rule rule)) (product (fst (extract rule lhs)) (snd (extract rule rhs))))
                                                     redl)))
                                (kbrec (+ j 1) (cons new-rule irreds) nil k l
                                       (list-append eqs (list-append eqs2 failures))))))))))
                  (next-criticals (subr kb (tpairs int int) rules)
                    (lambda (failures k l)
                      (tagcase
                          (prompt not-found
                            (ok-rules
                             (let* ((rl (get-rule l rules))
                                    (el (product (fst (extract rl lhs)) (snd (extract rl rhs)))))
                               (if (= k l)
                                   (process failures k l
                                            (strict-critical-pairs el (rename (extract rl numvars) el)))
                                   (tagcase
                                       (prompt not-found
                                         (ok-rules
                                          (let* ((rk (get-rule k rules))
                                                 (ek (product (fst (extract rk lhs)) (snd (extract rk rhs)))))
                                            (process failures k l
                                                     (mutual-critical-pairs el (rename (extract rl numvars) ek)))))
                                         (lambda (u) (failed)))
                                     (ok-rules (rs) rs)
                                     (else x (next-criticals failures (+ k 1) l))))))
                            (lambda (u) (failed)))
                        (ok-rules (rs) rs)
                        (else x (next-criticals failures 1 (+ l 1)))))))
               (process failures1 k1 l1 eqs1)))))
      (kbrec j0 rules0 failures0 k0 l0 eqs0))))

;; complete_rules is assumed locally confluent, and checked Noetherian with
;; ordering greater, rules is any list of rules
(define* kb-complete (subr kb ((subr kb (tpair) bool) rules rules) unit)
  (lambda (greater complete-rules rules)
    (let* ((n (check-rules complete-rules))
           (eqs (list-map (lambda ((rule rule)) (product (fst (extract rule lhs)) (snd (extract rule rhs)))) rules))
           (completed-rules (kb-completion greater n complete-rules nil n n eqs)))
      (begin
        (print-string "Canonical set found :") (print-newline)
        (pretty-rules (list-rev completed-rules))))))

;;;; kbmain.ml

(define* leaf (subr pure (string) term) (lambda (s) (t-term s nil)))
(define* app1 (subr (alloc @heap) (string term) term) (lambda (s a) (t-term s (cons a nil))))
(define* app2 (subr (alloc @heap) (string term term) term) (lambda (s a b) (t-term s (list a b))))

(define* geom-rules (subr (alloc @heap) () rules)
  (lambda ()
    (let ((v1 (t-var 1)) (v2 (t-var 2)) (v3 (t-var 3)))
      (list (product (number 1) (numvars 1)
                     (lhs (app2 "*" (leaf "U") v1))
                     (rhs v1))
            (product (number 2) (numvars 1)
                     (lhs (app2 "*" (app1 "I" v1) v1))
                     (rhs (leaf "U")))
            (product (number 3) (numvars 3)
                     (lhs (app2 "*" (app2 "*" v1 v2) v3))
                     (rhs (app2 "*" v1 (app2 "*" v2 v3))))
            (product (number 4) (numvars 0)
                     (lhs (app2 "*" (leaf "A") (leaf "B")))
                     (rhs (app2 "*" (leaf "B") (leaf "A"))))
            (product (number 5) (numvars 0)
                     (lhs (app2 "*" (leaf "C") (leaf "C")))
                     (rhs (leaf "U")))
            (product (number 6) (numvars 0)
                     (lhs (app2 "*" (leaf "C") (app2 "*" (leaf "A") (app1 "I" (leaf "C")))))
                     (rhs (app1 "I" (leaf "A"))))
            (product (number 7) (numvars 0)
                     (lhs (app2 "*" (leaf "C") (app2 "*" (leaf "B") (app1 "I" (leaf "C")))))
                     (rhs (leaf "B")))))))

(define group-rank (subr pure (string) int)
  (lambda (s)
    (cond ((string=? s "U") 0)
          ((string=? s "*") 1)
          ((string=? s "I") 2)
          ((string=? s "B") 3)
          ((string=? s "C") 4)
          ((string=? s "A") 5)
          (else -1))))

(define* group-precedence (subr kb (string string) ordering)
  (lambda (op1 op2)
    (let ((r1 (group-rank op1))
          (r2 (group-rank op2)))
      (cond ((= r1 r2) equal-v)
            ((> r1 r2) greater-v)
            (else notge-v)))))

(define group-order order-fn (rpo group-precedence lex-ext))

(define* greater (subr kb (tpair) bool)
  (lambda (pair) (tagcase (group-order pair) (o-greater () #t) (else x #f))))

;; The input, where no compiler can fold it: a global.
(define iterations int 1)

(define* main (subr kb () int)
  (lambda ()
    (begin
      (set out-hash 0)
      (kb-complete greater nil (geom-rules))
      (get out-hash))))

(define* run (subr kb (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (main)))))
(run iterations 0)
