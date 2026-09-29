;;; BOYER -- a term rewriter and tautology checker: the Boyer-Moore
;;; theorem prover's rewriting, on a fixed theorem.
;;;
;;; From the SML/NJ benchmark suite.
;;; From MLton's benchmark suite (benchmark/tests/boyer.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. MLton's driver was not fetched; the
;;; iteration count, 30 proofs, is this port's. MLton's `doit n` runs n.
;;; Answer: #t, the theorem proved (the original's `testit` prints
;;; "Proved!").
;;;
;;; What changed:
;;; - A head's equality, which SML's `=` on the record {name, props} makes
;;;   a comparison of the name and of the `props` ref, is a comparison of
;;;   the names (`string=?`): FX-26 has no equality of refs, and `get`
;;;   makes one head per name, so the two agree. Terms are compared by
;;;   `term-equal?`, written out, where SML's `=` is structural.
;;; - Exceptions abort to a prompt of the handler that catches them, each a
;;;   tag of its own. `failure` (raised by `get_binding`) is caught by two
;;;   handlers, whose values are of different types (a term in
;;;   `apply_subst`, a substitution in `unify1`), so `get_binding` is
;;;   written twice, one for each. `Unify` is caught only by
;;;   `rewrite_with_lemmas`, whose `handle unify =>` catches everything
;;;   (a variable pattern); nothing else can reach it, so its tag carries
;;;   the unit value.
;;; - The rules' `CProp (name, [a, b])` is `(cp2 name a b)`, a procedure
;;;   making the same list and `CProp` (`cp0` … `cp6`, by arity).
;;;   Likewise the main term's `Prop (get "f", [...])` is `(p1 "f" ...)`.
;;;   SML's `get` is `get-head`, since FX-26's `get` reads a ref.
;;; - A head, SML's record {name, props}, is a datatype of one variant,
;;;   `mk-head`, taken apart by `tagcase`, and `headname` is written in
;;;   place: with a product, taken apart by `extract`, a call of a
;;;   procedure whose body extracts (`headname`, `truep`) made the caller
;;;   decline register code, so it ran as cellular code, and an abort from
;;;   native code found no prompt (reported). The datatype takes the term
;;;   type as a parameter, since two datatypes cannot mention each other.
;;; - `tautologyp` on a `Prop` of other than three arguments, where SML
;;;   raises Match, is false; it is never reached (the proof succeeds).

;;; ------------------------------------------------------------ terms

(define-datatype (head-of (t type))
  (mk-head string (ref (listof (productof (left t) (right t)) @heap) @heap)))
(define-datatype term (var int) (prop (head-of term) (listof term @heap)))
(define-type head (head-of term))
(define-type lemma (productof (left term) (right term)))
(define-type lemma-list (listof lemma @heap))
(define-type terms (listof term @heap))
(define-datatype binding (bind int term))
(define-type bindings (listof binding @heap))

;; What rewriting does, and the prompts' bodies may do.
(define-effect rewrites (maxeff (read @heap) (alloc @heap) spin (read @globals)))
(define-effect rw (maxeff rewrites (goto @z)))

(define lemmas (ref (listof head @heap) @heap) (new nil))

;; replacement for property lists (SML's `get`)
(define* get-head (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)) (string) head)
  (lambda (name)
    (letrec ((get-rec (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read (globals lemmas mk-head))) ((listof head @heap)) head)
               (lambda (hdl)
                 (if (null? hdl)
                     (let ((entry (mk-head name (the (ref lemma-list @heap) (new nil)))))
                       (begin (set lemmas (cons entry (get lemmas))) entry))
                     (tagcase (car hdl)
                       (mk-head (n p) (if (string=? n name) (car hdl) (get-rec (cdr hdl)))))))))
      (get-rec (get lemmas)))))

(define* add-lemma (subr (maxeff (read @heap) (write @heap) (alloc @heap)) (term) unit)
  (lambda (t)
    (tagcase t
      (prop (h args)
        (let ((left (car args)) (right (car (cdr args))))
          (tagcase left
            (prop (lh largs) (tagcase lh (mk-head (n r) (set r (cons (product (left left) (right right)) (get r))))))
            (var (v) #u))))
      (var (v) #u))))

(define* head-equal? (subr pure (head head) bool)
  (lambda (a b) (tagcase a (mk-head (n1 p1) (tagcase b (mk-head (n2 p2) (string=? n1 n2)))))))

(define-rec
  (term-equal? (subr (maxeff (read @heap) spin (read @globals)) (term term) bool)
    (lambda (a b)
      (tagcase a
        (var (v) (tagcase b (var (w) (= v w)) (else b #f)))
        (prop (h1 as1) (tagcase b (prop (h2 as2) (and (head-equal? h1 h2) (terms-equal? as1 as2))) (else b #f))))))
  (terms-equal? (subr (maxeff (read @heap) spin (read @globals)) (terms terms) bool)
    (lambda (a b)
      (if (null? a)
          (null? b)
          (and (not (null? b)) (term-equal? (car a) (car b)) (terms-equal? (cdr a) (cdr b)))))))

(define* map-terms (subr rw ((subr rw (term) term) terms) terms)
  (lambda (f l) (if (null? l) l (cons (f (car l)) (map-terms f (cdr l))))))

;; substitutions: the exceptions' tags.
(define failure-t (prompt-tag term string rewrites @z) (make-continuation-prompt-tag))
(define failure-s (prompt-tag bindings string rewrites @z) (make-continuation-prompt-tag))
(define unify-tag (prompt-tag term unit rewrites @z) (make-continuation-prompt-tag))

(define* get-binding-t (subr rw (int bindings) term)
  (lambda (v l)
    (if (null? l)
        (abort-current-continuation failure-t "unbound")
        (tagcase (car l) (bind (w t) (if (= v w) t (get-binding-t v (cdr l))))))))
(define* get-binding-s (subr rw (int bindings) term)
  (lambda (v l)
    (if (null? l)
        (abort-current-continuation failure-s "unbound")
        (tagcase (car l) (bind (w t) (if (= v w) t (get-binding-s v (cdr l))))))))

(define* apply-subst (subr (read @globals) (bindings) (subr rw (term) term))
  (lambda (alist)
    (letrec ((as-rec (subr rw (term) term)
               (lambda (t)
                 (tagcase t
                   (var (v) (prompt failure-t (get-binding-t v alist) (lambda (s) t)))
                   (prop (h argl) (prop h (map-terms as-rec argl)))))))
      as-rec)))

(define-rec
  (unify1 (subr rw (term term bindings) bindings)
    (lambda (term1 term2 s)
      (tagcase term2
        (var (v)
          (prompt failure-s
            (if (term-equal? (get-binding-s v s) term1) s (abort-current-continuation unify-tag #u))
            (lambda (m) (the bindings (cons (bind v term1) s)))))
        (prop (head2 argl2)
          (tagcase term1
            (var (w) (abort-current-continuation unify-tag #u))
            (prop (head1 argl1)
              (if (head-equal? head1 head2)
                  (unify1-lst argl1 argl2 s)
                  (abort-current-continuation unify-tag #u))))))))
  (unify1-lst (subr rw (terms terms bindings) bindings)
    (lambda (a b s)
      (if (and (null? a) (null? b))
          s
          (if (or (null? a) (null? b))
              (abort-current-continuation unify-tag #u)
              (unify1-lst (cdr a) (cdr b) (unify1 (car a) (car b) s)))))))

(define* unify (subr rw (term term) bindings)
  (lambda (term1 term2) (unify1 term1 term2 nil)))

(define-rec
  (rewrite (subr rw (term) term)
    (lambda (t)
      (tagcase t
        (var (v) t)
        (prop (h argl)
          (tagcase h (mk-head (n p) (rewrite-with-lemmas (prop h (map-terms rewrite argl)) (get p))))))))
  (rewrite-with-lemmas (subr rw (term lemma-list) term)
    (lambda (t ls)
      (if (null? ls)
          t
          (prompt unify-tag
            (rewrite ((apply-subst (unify t (extract (car ls) left))) (extract (car ls) right)))
            (lambda (u) (rewrite-with-lemmas t (cdr ls))))))))

;;; ------------------------------------------------------------ rules

(define-datatype cterm (cvar int) (cprop string (listof cterm @heap)))
(define-type cterms (listof cterm @heap))

(define* cterm-to-term (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)) (cterm) term)
  (lambda (c)
    (tagcase c
      (cvar (v) (var v))
      (cprop (p l)
        (letrec ((map-c (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)) (cterms) terms)
                   (lambda (l) (if (null? l) nil (cons (cterm-to-term (car l)) (map-c (cdr l)))))))
          (let ((h (get-head p))) (prop h (map-c l))))))))

(define* add (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)) (cterm) unit)
  (lambda (t) (add-lemma (cterm-to-term t))))

(define* cv (subr pure (int) cterm) (lambda (v) (cvar v)))
(define* cp0 (subr (alloc @heap) (string) cterm)
  (lambda (n) (cprop n (the cterms nil))))
(define* cp1 (subr (alloc @heap) (string cterm) cterm)
  (lambda (n a) (cprop n (the cterms (cons a nil)))))
(define* cp2 (subr (alloc @heap) (string cterm cterm) cterm)
  (lambda (n a b) (cprop n (the cterms (cons a (cons b nil))))))
(define* cp3 (subr (alloc @heap) (string cterm cterm cterm) cterm)
  (lambda (n a b c) (cprop n (the cterms (cons a (cons b (cons c nil)))))))
(define* cp4 (subr (alloc @heap) (string cterm cterm cterm cterm) cterm)
  (lambda (n a b c d) (cprop n (the cterms (cons a (cons b (cons c (cons d nil))))))))
(define* cp5 (subr (alloc @heap) (string cterm cterm cterm cterm cterm) cterm)
  (lambda (n a b c d e) (cprop n (the cterms (cons a (cons b (cons c (cons d (cons e nil)))))))))
(define* cp6 (subr (alloc @heap) (string cterm cterm cterm cterm cterm cterm) cterm)
  (lambda (n a b c d e f) (cprop n (the cterms (cons a (cons b (cons c (cons d (cons e (cons f nil))))))))))

(define rules unit
  (begin
   (add (cp2 "equal"
          (cp1 "compile" (cv 5))
          (cp1 "reverse" (cp2 "codegen" (cp1 "optimize" (cv 5)) (cp0 "nil")))))
   (add (cp2 "equal"
          (cp2 "eqp" (cv 23) (cv 24))
          (cp2 "equal" (cp1 "fix" (cv 23)) (cp1 "fix" (cv 24)))))
   (add (cp2 "equal" (cp2 "gt" (cv 23) (cv 24)) (cp2 "lt" (cv 24) (cv 23))))
   (add (cp2 "equal" (cp2 "le" (cv 23) (cv 24)) (cp2 "ge" (cv 24) (cv 23))))
   (add (cp2 "equal" (cp2 "ge" (cv 23) (cv 24)) (cp2 "le" (cv 24) (cv 23))))
   (add (cp2 "equal"
          (cp1 "boolean" (cv 23))
          (cp2 "or" (cp2 "equal" (cv 23) (cp0 "true")) (cp2 "equal" (cv 23) (cp0 "false")))))
   (add (cp2 "equal"
          (cp2 "iff" (cv 23) (cv 24))
          (cp2 "and" (cp2 "implies" (cv 23) (cv 24)) (cp2 "implies" (cv 24) (cv 23)))))
   (add (cp2 "equal"
          (cp1 "even1" (cv 23))
          (cp3 "if" (cp1 "zerop" (cv 23)) (cp0 "true") (cp1 "odd" (cp1 "sub1" (cv 23))))))
   (add (cp2 "equal"
          (cp2 "countps_" (cv 11) (cv 15))
          (cp3 "countps_loop" (cv 11) (cv 15) (cp0 "zero"))))
   (add (cp2 "equal" (cp1 "fact_" (cv 8)) (cp2 "fact_loop" (cv 8) (cp0 "one"))))
   (add (cp2 "equal" (cp1 "reverse_" (cv 23)) (cp2 "reverse_loop" (cv 23) (cp0 "nil"))))
   (add (cp2 "equal"
          (cp2 "divides" (cv 23) (cv 24))
          (cp1 "zerop" (cp2 "remainder" (cv 24) (cv 23)))))
   (add (cp2 "equal"
          (cp2 "assume_true" (cv 21) (cv 0))
          (cp2 "cons" (cp2 "cons" (cv 21) (cp0 "true")) (cv 0))))
   (add (cp2 "equal"
          (cp2 "assume_false" (cv 21) (cv 0))
          (cp2 "cons" (cp2 "cons" (cv 21) (cp0 "false")) (cv 0))))
   (add (cp2 "equal"
          (cp1 "tautology_checker" (cv 23))
          (cp2 "tautologyp" (cp1 "normalize" (cv 23)) (cp0 "nil"))))
   (add (cp2 "equal" (cp1 "falsify" (cv 23)) (cp2 "falsify1" (cp1 "normalize" (cv 23)) (cp0 "nil"))))
   (add (cp2 "equal"
          (cp1 "prime" (cv 23))
          (cp3 "and"
            (cp1 "not" (cp1 "zerop" (cv 23)))
            (cp1 "not" (cp2 "equal" (cv 23) (cp1 "add1" (cp0 "zero"))))
            (cp2 "prime1" (cv 23) (cp1 "sub1" (cv 23))))))
   (add (cp2 "equal"
          (cp2 "and" (cv 15) (cv 16))
          (cp3 "if" (cv 15) (cp3 "if" (cv 16) (cp0 "true") (cp0 "false")) (cp0 "false"))))
   (add (cp2 "equal"
          (cp2 "or" (cv 15) (cv 16))
          (cp4 "if"
            (cv 15)
            (cp0 "true")
            (cp3 "if" (cv 16) (cp0 "true") (cp0 "false"))
            (cp0 "false"))))
   (add (cp2 "equal" (cp1 "not" (cv 15)) (cp3 "if" (cv 15) (cp0 "false") (cp0 "true"))))
   (add (cp2 "equal"
          (cp2 "implies" (cv 15) (cv 16))
          (cp3 "if" (cv 15) (cp3 "if" (cv 16) (cp0 "true") (cp0 "false")) (cp0 "true"))))
   (add (cp2 "equal" (cp1 "fix" (cv 23)) (cp3 "if" (cp1 "numberp" (cv 23)) (cv 23) (cp0 "zero"))))
   (add (cp2 "equal"
          (cp3 "if" (cp3 "if" (cv 0) (cv 1) (cv 2)) (cv 3) (cv 4))
          (cp3 "if" (cv 0) (cp3 "if" (cv 1) (cv 3) (cv 4)) (cp3 "if" (cv 2) (cv 3) (cv 4)))))
   (add (cp2 "equal"
          (cp1 "zerop" (cv 23))
          (cp2 "or" (cp2 "equal" (cv 23) (cp0 "zero")) (cp1 "not" (cp1 "numberp" (cv 23))))))
   (add (cp2 "equal"
          (cp2 "plus" (cp2 "plus" (cv 23) (cv 24)) (cv 25))
          (cp2 "plus" (cv 23) (cp2 "plus" (cv 24) (cv 25)))))
   (add (cp2 "equal"
          (cp2 "equal" (cp2 "plus" (cv 0) (cv 1)) (cp0 "zero"))
          (cp2 "and" (cp1 "zerop" (cv 0)) (cp1 "zerop" (cv 1)))))
   (add (cp2 "equal" (cp2 "difference" (cv 23) (cv 23)) (cp0 "zero")))
   (add (cp2 "equal"
          (cp2 "equal" (cp2 "plus" (cv 0) (cv 1)) (cp2 "plus" (cv 0) (cv 2)))
          (cp2 "equal" (cp1 "fix" (cv 1)) (cp1 "fix" (cv 2)))))
   (add (cp2 "equal"
          (cp2 "equal" (cp0 "zero") (cp2 "difference" (cv 23) (cv 24)))
          (cp1 "not" (cp2 "gt" (cv 24) (cv 23)))))
   (add (cp2 "equal"
          (cp2 "equal" (cv 23) (cp2 "difference" (cv 23) (cv 24)))
          (cp2 "and"
            (cp1 "numberp" (cv 23))
            (cp2 "or" (cp2 "equal" (cv 23) (cp0 "zero")) (cp1 "zerop" (cv 24))))))
   (add (cp2 "equal"
          (cp2 "meaning" (cp1 "plus_tree" (cp2 "append" (cv 23) (cv 24))) (cv 0))
          (cp2 "plus"
            (cp2 "meaning" (cp1 "plus_tree" (cv 23)) (cv 0))
            (cp2 "meaning" (cp1 "plus_tree" (cv 24)) (cv 0)))))
   (add (cp2 "equal"
          (cp2 "meaning" (cp1 "plus_tree" (cp1 "plus_fringe" (cv 23))) (cv 0))
          (cp1 "fix" (cp2 "meaning" (cv 23) (cv 0)))))
   (add (cp2 "equal"
          (cp2 "append" (cp2 "append" (cv 23) (cv 24)) (cv 25))
          (cp2 "append" (cv 23) (cp2 "append" (cv 24) (cv 25)))))
   (add (cp2 "equal"
          (cp1 "reverse" (cp2 "append" (cv 0) (cv 1)))
          (cp2 "append" (cp1 "reverse" (cv 1)) (cp1 "reverse" (cv 0)))))
   (add (cp2 "equal"
          (cp2 "times" (cv 23) (cp2 "plus" (cv 24) (cv 25)))
          (cp2 "plus" (cp2 "times" (cv 23) (cv 24)) (cp2 "times" (cv 23) (cv 25)))))
   (add (cp2 "equal"
          (cp2 "times" (cp2 "times" (cv 23) (cv 24)) (cv 25))
          (cp2 "times" (cv 23) (cp2 "times" (cv 24) (cv 25)))))
   (add (cp2 "equal"
          (cp2 "equal" (cp2 "times" (cv 23) (cv 24)) (cp0 "zero"))
          (cp2 "or" (cp1 "zerop" (cv 23)) (cp1 "zerop" (cv 24)))))
   (add (cp2 "equal"
          (cp3 "exec" (cp2 "append" (cv 23) (cv 24)) (cv 15) (cv 4))
          (cp3 "exec" (cv 24) (cp3 "exec" (cv 23) (cv 15) (cv 4)) (cv 4))))
   (add (cp2 "equal"
          (cp2 "mc_flatten" (cv 23) (cv 24))
          (cp2 "append" (cp1 "flatten" (cv 23)) (cv 24))))
   (add (cp2 "equal"
          (cp2 "member" (cv 23) (cp2 "append" (cv 0) (cv 1)))
          (cp2 "or" (cp2 "member" (cv 23) (cv 0)) (cp2 "member" (cv 23) (cv 1)))))
   (add (cp2 "equal" (cp2 "member" (cv 23) (cp1 "reverse" (cv 24))) (cp2 "member" (cv 23) (cv 24))))
   (add (cp2 "equal" (cp1 "length" (cp1 "reverse" (cv 23))) (cp1 "length" (cv 23))))
   (add (cp2 "equal"
          (cp2 "member" (cv 0) (cp2 "intersect" (cv 1) (cv 2)))
          (cp2 "and" (cp2 "member" (cv 0) (cv 1)) (cp2 "member" (cv 0) (cv 2)))))
   (add (cp2 "equal" (cp2 "nth" (cp0 "zero") (cv 8)) (cp0 "zero")))
   (add (cp2 "equal"
          (cp2 "exp" (cv 8) (cp2 "plus" (cv 9) (cv 10)))
          (cp2 "times" (cp2 "exp" (cv 8) (cv 9)) (cp2 "exp" (cv 8) (cv 10)))))
   (add (cp2 "equal"
          (cp2 "exp" (cv 8) (cp2 "times" (cv 9) (cv 10)))
          (cp2 "exp" (cp2 "exp" (cv 8) (cv 9)) (cv 10))))
   (add (cp2 "equal"
          (cp2 "reverse_loop" (cv 23) (cv 24))
          (cp2 "append" (cp1 "reverse" (cv 23)) (cv 24))))
   (add (cp2 "equal" (cp2 "reverse_loop" (cv 23) (cp0 "nil")) (cp1 "reverse" (cv 23))))
   (add (cp2 "equal"
          (cp2 "count_list" (cv 25) (cp2 "sort_lp" (cv 23) (cv 24)))
          (cp2 "plus" (cp2 "count_list" (cv 25) (cv 23)) (cp2 "count_list" (cv 25) (cv 24)))))
   (add (cp2 "equal"
          (cp2 "equal" (cp2 "append" (cv 0) (cv 1)) (cp2 "append" (cv 0) (cv 2)))
          (cp2 "equal" (cv 1) (cv 2))))
   (add (cp2 "equal"
          (cp2 "plus"
            (cp2 "remainder" (cv 23) (cv 24))
            (cp2 "times" (cv 24) (cp2 "quotient" (cv 23) (cv 24))))
          (cp1 "fix" (cv 23))))
   (add (cp2 "equal"
          (cp2 "power_eval" (cp3 "big_plus" (cv 11) (cv 8) (cv 1)) (cv 1))
          (cp2 "plus" (cp2 "power_eval" (cv 11) (cv 1)) (cv 8))))
   (add (cp2 "equal"
          (cp2 "power_eval" (cp4 "big_plus" (cv 23) (cv 24) (cv 8) (cv 1)) (cv 1))
          (cp2 "plus"
            (cv 8)
            (cp2 "plus" (cp2 "power_eval" (cv 23) (cv 1)) (cp2 "power_eval" (cv 24) (cv 1))))))
   (add (cp2 "equal" (cp2 "remainder" (cv 24) (cp0 "one")) (cp0 "zero")))
   (add (cp2 "equal"
          (cp2 "lt" (cp2 "remainder" (cv 23) (cv 24)) (cv 24))
          (cp1 "not" (cp1 "zerop" (cv 24)))))
   (add (cp2 "equal" (cp2 "remainder" (cv 23) (cv 23)) (cp0 "zero")))
   (add (cp2 "equal"
          (cp2 "lt" (cp2 "quotient" (cv 8) (cv 9)) (cv 8))
          (cp2 "and"
            (cp1 "not" (cp1 "zerop" (cv 8)))
            (cp2 "or" (cp1 "zerop" (cv 9)) (cp1 "not" (cp2 "equal" (cv 9) (cp0 "one")))))))
   (add (cp2 "equal"
          (cp2 "lt" (cp2 "remainder" (cv 23) (cv 24)) (cv 23))
          (cp3 "and"
            (cp1 "not" (cp1 "zerop" (cv 24)))
            (cp1 "not" (cp1 "zerop" (cv 23)))
            (cp1 "not" (cp2 "lt" (cv 23) (cv 24))))))
   (add (cp2 "equal" (cp2 "power_eval" (cp2 "power_rep" (cv 8) (cv 1)) (cv 1)) (cp1 "fix" (cv 8))))
   (add (cp2 "equal"
          (cp2 "power_eval"
            (cp4 "big_plus"
              (cp2 "power_rep" (cv 8) (cv 1))
              (cp2 "power_rep" (cv 9) (cv 1))
              (cp0 "zero")
              (cv 1))
            (cv 1))
          (cp2 "plus" (cv 8) (cv 9))))
   (add (cp2 "equal" (cp2 "gcd" (cv 23) (cv 24)) (cp2 "gcd" (cv 24) (cv 23))))
   (add (cp2 "equal"
          (cp2 "nth" (cp2 "append" (cv 0) (cv 1)) (cv 8))
          (cp2 "append"
            (cp2 "nth" (cv 0) (cv 8))
            (cp2 "nth" (cv 1) (cp2 "difference" (cv 8) (cp1 "length" (cv 0)))))))
   (add (cp2 "equal" (cp2 "difference" (cp2 "plus" (cv 23) (cv 24)) (cv 23)) (cp1 "fix" (cv 24))))
   (add (cp2 "equal" (cp2 "difference" (cp2 "plus" (cv 24) (cv 23)) (cv 23)) (cp1 "fix" (cv 24))))
   (add (cp2 "equal"
          (cp2 "difference" (cp2 "plus" (cv 23) (cv 24)) (cp2 "plus" (cv 23) (cv 25)))
          (cp2 "difference" (cv 24) (cv 25))))
   (add (cp2 "equal"
          (cp2 "times" (cv 23) (cp2 "difference" (cv 2) (cv 22)))
          (cp2 "difference" (cp2 "times" (cv 2) (cv 23)) (cp2 "times" (cv 22) (cv 23)))))
   (add (cp2 "equal" (cp2 "remainder" (cp2 "times" (cv 23) (cv 25)) (cv 25)) (cp0 "zero")))
   (add (cp2 "equal"
          (cp2 "difference" (cp2 "plus" (cv 1) (cp2 "plus" (cv 0) (cv 2))) (cv 0))
          (cp2 "plus" (cv 1) (cv 2))))
   (add (cp2 "equal"
          (cp2 "difference" (cp1 "add1" (cp2 "plus" (cv 24) (cv 25))) (cv 25))
          (cp1 "add1" (cv 24))))
   (add (cp2 "equal"
          (cp2 "lt" (cp2 "plus" (cv 23) (cv 24)) (cp2 "plus" (cv 23) (cv 25)))
          (cp2 "lt" (cv 24) (cv 25))))
   (add (cp2 "equal"
          (cp2 "lt" (cp2 "times" (cv 23) (cv 25)) (cp2 "times" (cv 24) (cv 25)))
          (cp2 "and" (cp1 "not" (cp1 "zerop" (cv 25))) (cp2 "lt" (cv 23) (cv 24)))))
   (add (cp2 "equal"
          (cp2 "lt" (cv 24) (cp2 "plus" (cv 23) (cv 24)))
          (cp1 "not" (cp1 "zerop" (cv 23)))))
   (add (cp2 "equal"
          (cp2 "gcd" (cp2 "times" (cv 23) (cv 25)) (cp2 "times" (cv 24) (cv 25)))
          (cp2 "times" (cv 25) (cp2 "gcd" (cv 23) (cv 24)))))
   (add (cp2 "equal" (cp2 "value" (cp1 "normalize" (cv 23)) (cv 0)) (cp2 "value" (cv 23) (cv 0))))
   (add (cp2 "equal"
          (cp2 "equal" (cp1 "flatten" (cv 23)) (cp2 "cons" (cv 24) (cp0 "nil")))
          (cp2 "and" (cp1 "nlistp" (cv 23)) (cp2 "equal" (cv 23) (cv 24)))))
   (add (cp2 "equal" (cp1 "listp" (cp1 "gother" (cv 23))) (cp1 "listp" (cv 23))))
   (add (cp2 "equal"
          (cp2 "samefringe" (cv 23) (cv 24))
          (cp2 "equal" (cp1 "flatten" (cv 23)) (cp1 "flatten" (cv 24)))))
   (add (cp2 "equal"
          (cp2 "equal" (cp2 "greatest_factor" (cv 23) (cv 24)) (cp0 "zero"))
          (cp2 "and"
            (cp2 "or" (cp1 "zerop" (cv 24)) (cp2 "equal" (cv 24) (cp0 "one")))
            (cp2 "equal" (cv 23) (cp0 "zero")))))
   (add (cp2 "equal"
          (cp2 "equal" (cp2 "greatest_factor" (cv 23) (cv 24)) (cp0 "one"))
          (cp2 "equal" (cv 23) (cp0 "one"))))
   (add (cp2 "equal"
          (cp1 "numberp" (cp2 "greatest_factor" (cv 23) (cv 24)))
          (cp1 "not"
            (cp2 "and"
              (cp2 "or" (cp1 "zerop" (cv 24)) (cp2 "equal" (cv 24) (cp0 "one")))
              (cp1 "not" (cp1 "numberp" (cv 23)))))))
   (add (cp2 "equal"
          (cp1 "times_list" (cp2 "append" (cv 23) (cv 24)))
          (cp2 "times" (cp1 "times_list" (cv 23)) (cp1 "times_list" (cv 24)))))
   (add (cp2 "equal"
          (cp1 "prime_list" (cp2 "append" (cv 23) (cv 24)))
          (cp2 "and" (cp1 "prime_list" (cv 23)) (cp1 "prime_list" (cv 24)))))
   (add (cp2 "equal"
          (cp2 "equal" (cv 25) (cp2 "times" (cv 22) (cv 25)))
          (cp2 "and"
            (cp1 "numberp" (cv 25))
            (cp2 "or" (cp2 "equal" (cv 25) (cp0 "zero")) (cp2 "equal" (cv 22) (cp0 "one"))))))
   (add (cp2 "equal" (cp2 "ge" (cv 23) (cv 24)) (cp1 "not" (cp2 "lt" (cv 23) (cv 24)))))
   (add (cp2 "equal"
          (cp2 "equal" (cv 23) (cp2 "times" (cv 23) (cv 24)))
          (cp2 "or"
            (cp2 "equal" (cv 23) (cp0 "zero"))
            (cp2 "and" (cp1 "numberp" (cv 23)) (cp2 "equal" (cv 24) (cp0 "one"))))))
   (add (cp2 "equal" (cp2 "remainder" (cp2 "times" (cv 24) (cv 23)) (cv 24)) (cp0 "zero")))
   (add (cp2 "equal"
          (cp2 "equal" (cp2 "times" (cv 0) (cv 1)) (cp0 "one"))
          (cp6 "and"
            (cp1 "not" (cp2 "equal" (cv 0) (cp0 "zero")))
            (cp1 "not" (cp2 "equal" (cv 1) (cp0 "zero")))
            (cp1 "numberp" (cv 0))
            (cp1 "numberp" (cv 1))
            (cp2 "equal" (cp1 "sub1" (cv 0)) (cp0 "zero"))
            (cp2 "equal" (cp1 "sub1" (cv 1)) (cp0 "zero")))))
   (add (cp2 "equal"
          (cp2 "lt" (cp1 "length" (cp2 "delete" (cv 23) (cv 11))) (cp1 "length" (cv 11)))
          (cp2 "member" (cv 23) (cv 11))))
   (add (cp2 "equal"
          (cp1 "sort2" (cp2 "delete" (cv 23) (cv 11)))
          (cp2 "delete" (cv 23) (cp1 "sort2" (cv 11)))))
   (add (cp2 "equal" (cp1 "dsort" (cv 23)) (cp1 "sort2" (cv 23))))
   (add (cp2 "equal"
          (cp1 "length"
            (cp2 "cons"
              (cv 0)
              (cp2 "cons"
                (cv 1)
                (cp2 "cons"
                  (cv 2)
                  (cp2 "cons" (cv 3) (cp2 "cons" (cv 4) (cp2 "cons" (cv 5) (cv 6))))))))
          (cp2 "plus" (cp0 "six") (cp1 "length" (cv 6)))))
   (add (cp2 "equal"
          (cp2 "difference" (cp1 "add1" (cp1 "add1" (cv 23))) (cp0 "two"))
          (cp1 "fix" (cv 23))))
   (add (cp2 "equal"
          (cp2 "quotient" (cp2 "plus" (cv 23) (cp2 "plus" (cv 23) (cv 24))) (cp0 "two"))
          (cp2 "plus" (cv 23) (cp2 "quotient" (cv 24) (cp0 "two")))))
   (add (cp2 "equal"
          (cp2 "sigma" (cp0 "zero") (cv 8))
          (cp2 "quotient" (cp2 "times" (cv 8) (cp1 "add1" (cv 8))) (cp0 "two"))))
   (add (cp2 "equal"
          (cp2 "plus" (cv 23) (cp1 "add1" (cv 24)))
          (cp3 "if"
            (cp1 "numberp" (cv 24))
            (cp1 "add1" (cp2 "plus" (cv 23) (cv 24)))
            (cp1 "add1" (cv 23)))))
   (add (cp2 "equal"
          (cp2 "equal" (cp2 "difference" (cv 23) (cv 24)) (cp2 "difference" (cv 25) (cv 24)))
          (cp3 "if"
            (cp2 "lt" (cv 23) (cv 24))
            (cp1 "not" (cp2 "lt" (cv 24) (cv 25)))
            (cp3 "if"
              (cp2 "lt" (cv 25) (cv 24))
              (cp1 "not" (cp2 "lt" (cv 24) (cv 23)))
              (cp2 "equal" (cp1 "fix" (cv 23)) (cp1 "fix" (cv 25)))))))
   (add (cp2 "equal"
          (cp2 "meaning" (cp1 "plus_tree" (cp2 "delete" (cv 23) (cv 24))) (cv 0))
          (cp3 "if"
            (cp2 "member" (cv 23) (cv 24))
            (cp2 "difference"
              (cp2 "meaning" (cp1 "plus_tree" (cv 24)) (cv 0))
              (cp2 "meaning" (cv 23) (cv 0)))
            (cp2 "meaning" (cp1 "plus_tree" (cv 24)) (cv 0)))))
   (add (cp2 "equal"
          (cp2 "times" (cv 23) (cp1 "add1" (cv 24)))
          (cp2 "if"
            (cp1 "numberp" (cv 24))
            (cp3 "plus" (cv 23) (cp2 "times" (cv 23) (cv 24)) (cp1 "fix" (cv 23))))))
   (add (cp2 "equal"
          (cp2 "nth" (cp0 "nil") (cv 8))
          (cp3 "if" (cp1 "zerop" (cv 8)) (cp0 "nil") (cp0 "zero"))))
   (add (cp2 "equal"
          (cp1 "last" (cp2 "append" (cv 0) (cv 1)))
          (cp3 "if"
            (cp1 "listp" (cv 1))
            (cp1 "last" (cv 1))
            (cp3 "if"
              (cp1 "listp" (cv 0))
              (cp2 "cons" (cp1 "car" (cp1 "last" (cv 0))) (cv 1))
              (cv 1)))))
   (add (cp2 "equal"
          (cp2 "equal" (cp2 "lt" (cv 23) (cv 24)) (cv 25))
          (cp3 "if"
            (cp2 "lt" (cv 23) (cv 24))
            (cp2 "equal" (cp0 "true") (cv 25))
            (cp2 "equal" (cp0 "false") (cv 25)))))
   (add (cp2 "equal"
          (cp2 "assignment" (cv 23) (cp2 "append" (cv 0) (cv 1)))
          (cp3 "if"
            (cp2 "assignedp" (cv 23) (cv 0))
            (cp2 "assignment" (cv 23) (cv 0))
            (cp2 "assignment" (cv 23) (cv 1)))))
   (add (cp2 "equal"
          (cp1 "car" (cp1 "gother" (cv 23)))
          (cp3 "if" (cp1 "listp" (cv 23)) (cp1 "car" (cp1 "flatten" (cv 23))) (cp0 "zero"))))
   (add (cp2 "equal"
          (cp1 "flatten" (cp1 "cdr" (cp1 "gother" (cv 23))))
          (cp3 "if"
            (cp1 "listp" (cv 23))
            (cp1 "cdr" (cp1 "flatten" (cv 23)))
            (cp2 "cons" (cp0 "zero") (cp0 "nil")))))
   (add (cp2 "equal"
          (cp2 "quotient" (cp2 "times" (cv 24) (cv 23)) (cv 24))
          (cp3 "if" (cp1 "zerop" (cv 24)) (cp0 "zero") (cp1 "fix" (cv 23)))))
   (add (cp2 "equal"
          (cp2 "get" (cv 9) (cp3 "set" (cv 8) (cv 21) (cv 12)))
          (cp3 "if" (cp2 "eqp" (cv 9) (cv 8)) (cv 21) (cp2 "get" (cv 9) (cv 12)))))   #u))

;;; ------------------------------------------------------------ tautology checker

(define* mem (subr (maxeff (read @heap) spin (read @globals)) (term terms) bool)
  (lambda (x l) (if (null? l) #f (or (term-equal? x (car l)) (mem x (cdr l))))))

(define* truep (subr (maxeff (read @heap) spin (read @globals)) (term terms) bool)
  (lambda (x lst)
    (tagcase x
      (prop (h args) (or (tagcase h (mk-head (n p) (string=? n "true"))) (mem x lst)))
      (else y (mem x lst)))))

(define* falsep (subr (maxeff (read @heap) spin (read @globals)) (term terms) bool)
  (lambda (x lst)
    (tagcase x
      (prop (h args) (or (tagcase h (mk-head (n p) (string=? n "false"))) (mem x lst)))
      (else y (mem x lst)))))

(define* tautologyp (subr (maxeff (read @heap) (alloc @heap) spin (read @globals)) (term terms terms) bool)
  (lambda (x true-lst false-lst)
    (if (truep x true-lst)
        #t
        (if (falsep x false-lst)
            #f
            (tagcase x
              (var (v) #f)
              (prop (h args)
                (if (and (not (null? args)) (not (null? (cdr args))) (not (null? (cdr (cdr args))))
                         (null? (cdr (cdr (cdr args)))))
                    (let ((test (car args)) (yes (car (cdr args))) (no (car (cdr (cdr args)))))
                      (if (tagcase h (mk-head (n p) (string=? n "if")))
                          (if (truep test true-lst)
                              (tautologyp yes true-lst false-lst)
                              (if (falsep test false-lst)
                                  (tautologyp no true-lst false-lst)
                                  (and (tautologyp yes (cons test true-lst) false-lst)
                                       (tautologyp no true-lst (cons test false-lst)))))
                          #f))
                    #f)))))))

(define* tautp (subr rw (term) bool)
  (lambda (x) (tautologyp (rewrite x) nil nil)))

;;; ------------------------------------------------------------ the benchmark

(define* p0 (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)) (string) term)
  (lambda (n) (prop (get-head n) (the terms nil))))
(define* p1 (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)) (string term) term)
  (lambda (n a) (prop (get-head n) (the terms (cons a nil)))))
(define* p2 (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)) (string term term) term)
  (lambda (n a b) (prop (get-head n) (the terms (cons a (cons b nil))))))

(define subst bindings
  (the bindings
    (cons (bind 23 (p1 "f" (p2 "plus" (p2 "plus" (var 0) (var 1)) (p2 "plus" (var 2) (p0 "zero")))))
    (cons (bind 24 (p1 "f" (p2 "times" (p2 "times" (var 0) (var 1)) (p2 "plus" (var 2) (var 3)))))
    (cons (bind 25 (p1 "f" (p1 "reverse" (p2 "append" (p2 "append" (var 0) (var 1)) (p0 "nil")))))
    (cons (bind 20 (p2 "equal" (p2 "plus" (var 0) (var 1)) (p2 "difference" (var 23) (var 24))))
    (cons (bind 22 (p2 "lt" (p2 "remainder" (var 0) (var 1)) (p2 "member" (var 0) (p1 "length" (var 1)))))
          nil)))))))

(define term term
  (p2 "implies"
      (p2 "and"
          (p2 "implies" (var 23) (var 24))
          (p2 "and"
              (p2 "implies" (var 24) (var 25))
              (p2 "and"
                  (p2 "implies" (var 25) (var 20))
                  (p2 "implies" (var 20) (var 22)))))
      (p2 "implies" (var 23) (var 22))))

(define* doit (subr rw () bool)
  (lambda () (tautp ((apply-subst subst) term))))

;; The input, where no compiler can fold it: a global, which a later
;; definition may replace.
(define iterations int 30)

(define* run (subr rw (int bool) bool)
  (lambda (i result) (if (= i 0) result (run (- i 1) (doit)))))
(run iterations #f)
