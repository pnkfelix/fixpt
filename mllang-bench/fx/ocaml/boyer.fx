;;; BOYER -- the Boyer-Moore theorem prover's rewriter and tautology
;;; checker, proving a lemma after rewriting it with 106 lemmas.
;;;
;;; From OCaml's classic test programs (testsuite/tests/misc/boyer.ml, ocaml
;;; commit 7da997d28b1a), ported to FX-26. The original proves the term 10
;;; times and prints "Proved!" (the reference output) or "Cannot prove!".
;;; The port does those 10 proofs `iterations` = 3 times, the lemmas made
;;; once, and its value is the number of proofs that succeeded. Answer: 30
;;; (with `iterations` 1, 10: the reference's "Proved!").
;;;
;;; What the port changes:
;;; - The `head` record, with its mutable `props`, is a product whose
;;;   `props` field is a ref. OCaml compares heads with `==`; FX-26 has no
;;;   physical equality, so the port compares their names, which `get`
;;;   (here `get-head`) keeps unique, so that it means the same. The
;;;   structural `=` on terms (`List.mem`, and a binding compared with a
;;;   term) is `term=?`, heads again compared by name.
;;; - A compiler workaround: the names are compared by `string=?` written
;;;   out where heads are compared. Calling a procedure `same-head?` that
;;;   does it made the native run fail, "abort: no prompt for this tag",
;;;   where the cellular and lowered runs do not.
;;; - Exceptions: `failwith "unbound"` and `raise Unify`, each caught by a
;;;   `try` whose value is a term or a substitution, are aborts to two
;;;   prompt tags, `failure` and `unify-exn`; a prompt's body gives back an
;;;   `outcome`, a sum with a variant for each type a `try` gives, and its
;;;   handler `(failed)`. The prompts nest as deep as the original's `try`s
;;;   (`rewrite_with_lemmas` rewrites inside its `try`). `assert false` is
;;;   a `failwith` no prompt catches: an error, which never happens.
;;; - The lemmas, `CProp`/`CVar` constructor expressions in the original,
;;;   are built with `c0` .. `c6` (a `CProp` of that many arguments) and
;;;   `cv`, mechanically translated. `List.map` and `List.mem` are written
;;;   here; `cterm_to_term` maps the arguments before it gets the head,
;;;   in the order OCaml evaluates a constructor's arguments.
;;; - `apply_subst` gives back the whole term for an unbound variable, as
;;;   the original does.

(define-effect bo (maxeff (read @heap) (write @heap) (alloc @heap) spin (goto @x) (read @globals)))
(define-effect bo-body (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)))

;; Manipulations over terms

(define-datatype term
  (var int)
  (prop (productof (name string)
                   (props (ref (listof (productof (lhs term) (rhs term)) @heap) @heap)))
        (listof term @heap)))
(define-type terms (listof term @heap))
(define-type lemma (productof (lhs term) (rhs term)))
(define-type head (productof (name string) (props (ref (listof lemma @heap) @heap))))
(define-type binding (productof (v int) (t term)))
(define-type subst (listof binding @heap))

(define-datatype outcome (ok-term term) (ok-subst (listof (productof (v int) (t term)) @heap)) (failed))

;; exception Failure, and exception Unify
(define failure (prompt-tag outcome unit bo-body @x) (make-continuation-prompt-tag))
(define unify-exn (prompt-tag outcome unit bo-body @x) (make-continuation-prompt-tag))

(define* failwith (subr bo (string) void)
  (lambda (message) (abort-current-continuation failure #u)))

(define* list-map (subr bo ((subr bo (term) term) terms) terms)
  (lambda (f l)
    (if (null? l) nil (let ((r (f (car l)))) (cons r (list-map f (cdr l)))))))

(define* term=? (subr bo (term term) bool)
  (lambda (t1 t2)
    (tagcase t1
      (var (v1) (tagcase t2 (var (v2) (= v1 v2)) (else x #f)))
      (prop (h1 args1)
        (tagcase t2
          (prop (h2 args2)
            (and (string=? (extract h1 name) (extract h2 name))
                 (letrec ((each (subr bo (terms terms) bool)
                            (lambda (l1 l2)
                              (cond ((null? l1) (null? l2))
                                    ((null? l2) #f)
                                    (else (and (term=? (car l1) (car l2)) (each (cdr l1) (cdr l2))))))))
                   (each args1 args2))))
          (else x #f))))))

(define* list-mem (subr bo (term terms) bool)
  (lambda (x l) (if (null? l) #f (or (term=? x (car l)) (list-mem x (cdr l))))))

(define lemmas (ref (listof head @heap) @heap) (new nil))

;; Replacement for property lists

(define* get-head (subr bo (string) head)
  (lambda (name)
    (letrec ((get-rec (subr bo ((listof head @heap)) head)
               (lambda (l)
                 (if (null? l)
                     (let ((entry (the head (product (name name) (props (new nil))))))
                       (begin (set lemmas (cons entry (get lemmas))) entry))
                     (let ((hd1 (car l)))
                       (if (string=? (extract hd1 name) name) hd1 (get-rec (cdr l))))))))
      (get-rec (get lemmas)))))

(define* add-lemma (subr bo (term) unit)
  (lambda (t)
    (tagcase t
      (prop (h args)
        (if (and (not (null? args)) (not (null? (cdr args))) (null? (cdr (cdr args))))
            (let ((left (car args)) (right (car (cdr args))))
              (tagcase left
                (prop (headl a)
                  (set (extract headl props)
                       (cons (product (lhs left) (rhs right)) (get (extract headl props)))))
                (else x (failwith "assert false"))))
            (failwith "assert false")))
      (else x (failwith "assert false")))))

;; Substitutions

(define* get-binding (subr bo (int subst) term)
  (lambda (v l)
    (letrec ((get-rec (subr bo (subst) term)
               (lambda (l)
                 (cond ((null? l) (failwith "unbound"))
                       ((= v (extract (car l) v)) (extract (car l) t))
                       (else (get-rec (cdr l)))))))
      (get-rec l))))

(define* apply-subst (subr bo (subst term) term)
  (lambda (alist term)
    (letrec ((as-rec (subr bo (term) term)
               (lambda (t)
                 (tagcase t
                   (var (v)
                     (tagcase (prompt failure (ok-term (get-binding v alist)) (lambda (u) (failed)))
                       (ok-term (b) b)
                       (else x term)))
                   (prop (head argl) (prop head (list-map as-rec argl)))))))
      (as-rec term))))

(define-rec
  (unify (subr bo (term term) subst)
    (lambda (term1 term2) (unify1 term1 term2 nil)))
  (unify1 (subr bo (term term subst) subst)
    (lambda (term1 term2 unify-subst)
      (tagcase term2
        (var (v)
          (tagcase (prompt failure
                     (ok-subst (if (term=? (get-binding v unify-subst) term1)
                                   unify-subst
                                   (abort-current-continuation unify-exn #u)))
                     (lambda (u) (failed)))
            (ok-subst (s) s)
            (else x (cons (product (v v) (t term1)) unify-subst))))
        (prop (head2 argl2)
          (tagcase term1
            (var (v) (abort-current-continuation unify-exn #u))
            (prop (head1 argl1)
              (if (string=? (extract head1 name) (extract head2 name))
                  (unify1-lst argl1 argl2 unify-subst)
                  (abort-current-continuation unify-exn #u))))))))
  (unify1-lst (subr bo (terms terms subst) subst)
    (lambda (l1 l2 unify-subst)
      (cond ((and (null? l1) (null? l2)) unify-subst)
            ((or (null? l1) (null? l2)) (abort-current-continuation unify-exn #u))
            (else (unify1-lst (cdr l1) (cdr l2) (unify1 (car l1) (car l2) unify-subst)))))))

(define-rec
  (rewrite (subr bo (term) term)
    (lambda (term)
      (tagcase term
        (var (v) term)
        (prop (head argl)
          (rewrite-with-lemmas (prop head (list-map rewrite argl)) (get (extract head props)))))))
  (rewrite-with-lemmas (subr bo (term (listof lemma @heap)) term)
    (lambda (term lemmas)
      (if (null? lemmas)
          term
          (let ((t1 (extract (car lemmas) lhs))
                (t2 (extract (car lemmas) rhs))
                (rest (cdr lemmas)))
            (tagcase (prompt unify-exn (ok-term (rewrite (apply-subst (unify term t1) t2)))
                       (lambda (u) (failed)))
              (ok-term (t) t)
              (else x (rewrite-with-lemmas term rest))))))))

(define-datatype cterm (cvar int) (cprop string (listof cterm @heap)))

(define* cterm-to-term (subr bo (cterm) term)
  (lambda (c)
    (tagcase c
      (cvar (v) (var v))
      (cprop (p l)
        (letrec ((map-c (subr bo ((listof cterm @heap)) terms)
                   (lambda (l)
                     (if (null? l) nil (let ((r (cterm-to-term (car l)))) (cons r (map-c (cdr l))))))))
          (let* ((args (map-c l)) (h (get-head p)))
            (prop h args)))))))

(define* add (subr bo (cterm) unit) (lambda (t) (add-lemma (cterm-to-term t))))

;; `CProp` of 0 to 6 arguments, and `CVar`.
(define* cv (subr pure (int) cterm) (lambda (v) (cvar v)))
(define* c0 (subr pure (string) cterm) (lambda (p) (cprop p nil)))
(define* c1 (subr (alloc @heap) (string cterm) cterm) (lambda (p a) (cprop p (cons a nil))))
(define* c2 (subr (alloc @heap) (string cterm cterm) cterm) (lambda (p a b) (cprop p (cons a (cons b nil)))))
(define* c3 (subr (alloc @heap) (string cterm cterm cterm) cterm)
  (lambda (p a b c) (cprop p (cons a (cons b (cons c nil))))))
(define* c4 (subr (alloc @heap) (string cterm cterm cterm cterm) cterm)
  (lambda (p a b c d) (cprop p (cons a (cons b (cons c (cons d nil)))))))
(define* c6 (subr (alloc @heap) (string cterm cterm cterm cterm cterm cterm) cterm)
  (lambda (p a b c d e f) (cprop p (cons a (cons b (cons c (cons d (cons e (cons f nil)))))))))

(define* add-lemmas (subr bo () unit)
  (lambda ()
    (begin
      (add (c2 "equal" (c1 "compile" (cv 5)) (c1 "reverse" (c2 "codegen" (c1 "optimize" (cv 5)) (c0 "nil")))))
      (add (c2 "equal" (c2 "eqp" (cv 23) (cv 24)) (c2 "equal" (c1 "fix" (cv 23)) (c1 "fix" (cv 24)))))
      (add (c2 "equal" (c2 "gt" (cv 23) (cv 24)) (c2 "lt" (cv 24) (cv 23))))
      (add (c2 "equal" (c2 "le" (cv 23) (cv 24)) (c2 "ge" (cv 24) (cv 23))))
      (add (c2 "equal" (c2 "ge" (cv 23) (cv 24)) (c2 "le" (cv 24) (cv 23))))
      (add (c2 "equal" (c1 "boolean" (cv 23)) (c2 "or" (c2 "equal" (cv 23) (c0 "true")) (c2 "equal" (cv 23) (c0 "false")))))
      (add (c2 "equal" (c2 "iff" (cv 23) (cv 24)) (c2 "and" (c2 "implies" (cv 23) (cv 24)) (c2 "implies" (cv 24) (cv 23)))))
      (add (c2 "equal" (c1 "even1" (cv 23)) (c3 "if" (c1 "zerop" (cv 23)) (c0 "true") (c1 "odd" (c1 "sub1" (cv 23))))))
      (add (c2 "equal" (c2 "countps_" (cv 11) (cv 15)) (c3 "countps_loop" (cv 11) (cv 15) (c0 "zero"))))
      (add (c2 "equal" (c1 "fact_" (cv 8)) (c2 "fact_loop" (cv 8) (c0 "one"))))
      (add (c2 "equal" (c1 "reverse_" (cv 23)) (c2 "reverse_loop" (cv 23) (c0 "nil"))))
      (add (c2 "equal" (c2 "divides" (cv 23) (cv 24)) (c1 "zerop" (c2 "remainder" (cv 24) (cv 23)))))
      (add (c2 "equal" (c2 "assume_true" (cv 21) (cv 0)) (c2 "cons" (c2 "cons" (cv 21) (c0 "true")) (cv 0))))
      (add (c2 "equal" (c2 "assume_false" (cv 21) (cv 0)) (c2 "cons" (c2 "cons" (cv 21) (c0 "false")) (cv 0))))
      (add (c2 "equal" (c1 "tautology_checker" (cv 23)) (c2 "tautologyp" (c1 "normalize" (cv 23)) (c0 "nil"))))
      (add (c2 "equal" (c1 "falsify" (cv 23)) (c2 "falsify1" (c1 "normalize" (cv 23)) (c0 "nil"))))
      (add (c2 "equal" (c1 "prime" (cv 23)) (c3 "and" (c1 "not" (c1 "zerop" (cv 23))) (c1 "not" (c2 "equal" (cv 23) (c1 "add1" (c0 "zero")))) (c2 "prime1" (cv 23) (c1 "sub1" (cv 23))))))
      (add (c2 "equal" (c2 "and" (cv 15) (cv 16)) (c3 "if" (cv 15) (c3 "if" (cv 16) (c0 "true") (c0 "false")) (c0 "false"))))
      (add (c2 "equal" (c2 "or" (cv 15) (cv 16)) (c4 "if" (cv 15) (c0 "true") (c3 "if" (cv 16) (c0 "true") (c0 "false")) (c0 "false"))))
      (add (c2 "equal" (c1 "not" (cv 15)) (c3 "if" (cv 15) (c0 "false") (c0 "true"))))
      (add (c2 "equal" (c2 "implies" (cv 15) (cv 16)) (c3 "if" (cv 15) (c3 "if" (cv 16) (c0 "true") (c0 "false")) (c0 "true"))))
      (add (c2 "equal" (c1 "fix" (cv 23)) (c3 "if" (c1 "numberp" (cv 23)) (cv 23) (c0 "zero"))))
      (add (c2 "equal" (c3 "if" (c3 "if" (cv 0) (cv 1) (cv 2)) (cv 3) (cv 4)) (c3 "if" (cv 0) (c3 "if" (cv 1) (cv 3) (cv 4)) (c3 "if" (cv 2) (cv 3) (cv 4)))))
      (add (c2 "equal" (c1 "zerop" (cv 23)) (c2 "or" (c2 "equal" (cv 23) (c0 "zero")) (c1 "not" (c1 "numberp" (cv 23))))))
      (add (c2 "equal" (c2 "plus" (c2 "plus" (cv 23) (cv 24)) (cv 25)) (c2 "plus" (cv 23) (c2 "plus" (cv 24) (cv 25)))))
      (add (c2 "equal" (c2 "equal" (c2 "plus" (cv 0) (cv 1)) (c0 "zero")) (c2 "and" (c1 "zerop" (cv 0)) (c1 "zerop" (cv 1)))))
      (add (c2 "equal" (c2 "difference" (cv 23) (cv 23)) (c0 "zero")))
      (add (c2 "equal" (c2 "equal" (c2 "plus" (cv 0) (cv 1)) (c2 "plus" (cv 0) (cv 2))) (c2 "equal" (c1 "fix" (cv 1)) (c1 "fix" (cv 2)))))
      (add (c2 "equal" (c2 "equal" (c0 "zero") (c2 "difference" (cv 23) (cv 24))) (c1 "not" (c2 "gt" (cv 24) (cv 23)))))
      (add (c2 "equal" (c2 "equal" (cv 23) (c2 "difference" (cv 23) (cv 24))) (c2 "and" (c1 "numberp" (cv 23)) (c2 "or" (c2 "equal" (cv 23) (c0 "zero")) (c1 "zerop" (cv 24))))))
      (add (c2 "equal" (c2 "meaning" (c1 "plus_tree" (c2 "append" (cv 23) (cv 24))) (cv 0)) (c2 "plus" (c2 "meaning" (c1 "plus_tree" (cv 23)) (cv 0)) (c2 "meaning" (c1 "plus_tree" (cv 24)) (cv 0)))))
      (add (c2 "equal" (c2 "meaning" (c1 "plus_tree" (c1 "plus_fringe" (cv 23))) (cv 0)) (c1 "fix" (c2 "meaning" (cv 23) (cv 0)))))
      (add (c2 "equal" (c2 "append" (c2 "append" (cv 23) (cv 24)) (cv 25)) (c2 "append" (cv 23) (c2 "append" (cv 24) (cv 25)))))
      (add (c2 "equal" (c1 "reverse" (c2 "append" (cv 0) (cv 1))) (c2 "append" (c1 "reverse" (cv 1)) (c1 "reverse" (cv 0)))))
      (add (c2 "equal" (c2 "times" (cv 23) (c2 "plus" (cv 24) (cv 25))) (c2 "plus" (c2 "times" (cv 23) (cv 24)) (c2 "times" (cv 23) (cv 25)))))
      (add (c2 "equal" (c2 "times" (c2 "times" (cv 23) (cv 24)) (cv 25)) (c2 "times" (cv 23) (c2 "times" (cv 24) (cv 25)))))
      (add (c2 "equal" (c2 "equal" (c2 "times" (cv 23) (cv 24)) (c0 "zero")) (c2 "or" (c1 "zerop" (cv 23)) (c1 "zerop" (cv 24)))))
      (add (c2 "equal" (c3 "exec" (c2 "append" (cv 23) (cv 24)) (cv 15) (cv 4)) (c3 "exec" (cv 24) (c3 "exec" (cv 23) (cv 15) (cv 4)) (cv 4))))
      (add (c2 "equal" (c2 "mc_flatten" (cv 23) (cv 24)) (c2 "append" (c1 "flatten" (cv 23)) (cv 24))))
      (add (c2 "equal" (c2 "member" (cv 23) (c2 "append" (cv 0) (cv 1))) (c2 "or" (c2 "member" (cv 23) (cv 0)) (c2 "member" (cv 23) (cv 1)))))
      (add (c2 "equal" (c2 "member" (cv 23) (c1 "reverse" (cv 24))) (c2 "member" (cv 23) (cv 24))))
      (add (c2 "equal" (c1 "length" (c1 "reverse" (cv 23))) (c1 "length" (cv 23))))
      (add (c2 "equal" (c2 "member" (cv 0) (c2 "intersect" (cv 1) (cv 2))) (c2 "and" (c2 "member" (cv 0) (cv 1)) (c2 "member" (cv 0) (cv 2)))))
      (add (c2 "equal" (c2 "nth" (c0 "zero") (cv 8)) (c0 "zero")))
      (add (c2 "equal" (c2 "exp" (cv 8) (c2 "plus" (cv 9) (cv 10))) (c2 "times" (c2 "exp" (cv 8) (cv 9)) (c2 "exp" (cv 8) (cv 10)))))
      (add (c2 "equal" (c2 "exp" (cv 8) (c2 "times" (cv 9) (cv 10))) (c2 "exp" (c2 "exp" (cv 8) (cv 9)) (cv 10))))
      (add (c2 "equal" (c2 "reverse_loop" (cv 23) (cv 24)) (c2 "append" (c1 "reverse" (cv 23)) (cv 24))))
      (add (c2 "equal" (c2 "reverse_loop" (cv 23) (c0 "nil")) (c1 "reverse" (cv 23))))
      (add (c2 "equal" (c2 "count_list" (cv 25) (c2 "sort_lp" (cv 23) (cv 24))) (c2 "plus" (c2 "count_list" (cv 25) (cv 23)) (c2 "count_list" (cv 25) (cv 24)))))
      (add (c2 "equal" (c2 "equal" (c2 "append" (cv 0) (cv 1)) (c2 "append" (cv 0) (cv 2))) (c2 "equal" (cv 1) (cv 2))))
      (add (c2 "equal" (c2 "plus" (c2 "remainder" (cv 23) (cv 24)) (c2 "times" (cv 24) (c2 "quotient" (cv 23) (cv 24)))) (c1 "fix" (cv 23))))
      (add (c2 "equal" (c2 "power_eval" (c3 "big_plus" (cv 11) (cv 8) (cv 1)) (cv 1)) (c2 "plus" (c2 "power_eval" (cv 11) (cv 1)) (cv 8))))
      (add (c2 "equal" (c2 "power_eval" (c4 "big_plus" (cv 23) (cv 24) (cv 8) (cv 1)) (cv 1)) (c2 "plus" (cv 8) (c2 "plus" (c2 "power_eval" (cv 23) (cv 1)) (c2 "power_eval" (cv 24) (cv 1))))))
      (add (c2 "equal" (c2 "remainder" (cv 24) (c0 "one")) (c0 "zero")))
      (add (c2 "equal" (c2 "lt" (c2 "remainder" (cv 23) (cv 24)) (cv 24)) (c1 "not" (c1 "zerop" (cv 24)))))
      (add (c2 "equal" (c2 "remainder" (cv 23) (cv 23)) (c0 "zero")))
      (add (c2 "equal" (c2 "lt" (c2 "quotient" (cv 8) (cv 9)) (cv 8)) (c2 "and" (c1 "not" (c1 "zerop" (cv 8))) (c2 "or" (c1 "zerop" (cv 9)) (c1 "not" (c2 "equal" (cv 9) (c0 "one")))))))
      (add (c2 "equal" (c2 "lt" (c2 "remainder" (cv 23) (cv 24)) (cv 23)) (c3 "and" (c1 "not" (c1 "zerop" (cv 24))) (c1 "not" (c1 "zerop" (cv 23))) (c1 "not" (c2 "lt" (cv 23) (cv 24))))))
      (add (c2 "equal" (c2 "power_eval" (c2 "power_rep" (cv 8) (cv 1)) (cv 1)) (c1 "fix" (cv 8))))
      (add (c2 "equal" (c2 "power_eval" (c4 "big_plus" (c2 "power_rep" (cv 8) (cv 1)) (c2 "power_rep" (cv 9) (cv 1)) (c0 "zero") (cv 1)) (cv 1)) (c2 "plus" (cv 8) (cv 9))))
      (add (c2 "equal" (c2 "gcd" (cv 23) (cv 24)) (c2 "gcd" (cv 24) (cv 23))))
      (add (c2 "equal" (c2 "nth" (c2 "append" (cv 0) (cv 1)) (cv 8)) (c2 "append" (c2 "nth" (cv 0) (cv 8)) (c2 "nth" (cv 1) (c2 "difference" (cv 8) (c1 "length" (cv 0)))))))
      (add (c2 "equal" (c2 "difference" (c2 "plus" (cv 23) (cv 24)) (cv 23)) (c1 "fix" (cv 24))))
      (add (c2 "equal" (c2 "difference" (c2 "plus" (cv 24) (cv 23)) (cv 23)) (c1 "fix" (cv 24))))
      (add (c2 "equal" (c2 "difference" (c2 "plus" (cv 23) (cv 24)) (c2 "plus" (cv 23) (cv 25))) (c2 "difference" (cv 24) (cv 25))))
      (add (c2 "equal" (c2 "times" (cv 23) (c2 "difference" (cv 2) (cv 22))) (c2 "difference" (c2 "times" (cv 2) (cv 23)) (c2 "times" (cv 22) (cv 23)))))
      (add (c2 "equal" (c2 "remainder" (c2 "times" (cv 23) (cv 25)) (cv 25)) (c0 "zero")))
      (add (c2 "equal" (c2 "difference" (c2 "plus" (cv 1) (c2 "plus" (cv 0) (cv 2))) (cv 0)) (c2 "plus" (cv 1) (cv 2))))
      (add (c2 "equal" (c2 "difference" (c1 "add1" (c2 "plus" (cv 24) (cv 25))) (cv 25)) (c1 "add1" (cv 24))))
      (add (c2 "equal" (c2 "lt" (c2 "plus" (cv 23) (cv 24)) (c2 "plus" (cv 23) (cv 25))) (c2 "lt" (cv 24) (cv 25))))
      (add (c2 "equal" (c2 "lt" (c2 "times" (cv 23) (cv 25)) (c2 "times" (cv 24) (cv 25))) (c2 "and" (c1 "not" (c1 "zerop" (cv 25))) (c2 "lt" (cv 23) (cv 24)))))
      (add (c2 "equal" (c2 "lt" (cv 24) (c2 "plus" (cv 23) (cv 24))) (c1 "not" (c1 "zerop" (cv 23)))))
      (add (c2 "equal" (c2 "gcd" (c2 "times" (cv 23) (cv 25)) (c2 "times" (cv 24) (cv 25))) (c2 "times" (cv 25) (c2 "gcd" (cv 23) (cv 24)))))
      (add (c2 "equal" (c2 "value" (c1 "normalize" (cv 23)) (cv 0)) (c2 "value" (cv 23) (cv 0))))
      (add (c2 "equal" (c2 "equal" (c1 "flatten" (cv 23)) (c2 "cons" (cv 24) (c0 "nil"))) (c2 "and" (c1 "nlistp" (cv 23)) (c2 "equal" (cv 23) (cv 24)))))
      (add (c2 "equal" (c1 "listp" (c1 "gother" (cv 23))) (c1 "listp" (cv 23))))
      (add (c2 "equal" (c2 "samefringe" (cv 23) (cv 24)) (c2 "equal" (c1 "flatten" (cv 23)) (c1 "flatten" (cv 24)))))
      (add (c2 "equal" (c2 "equal" (c2 "greatest_factor" (cv 23) (cv 24)) (c0 "zero")) (c2 "and" (c2 "or" (c1 "zerop" (cv 24)) (c2 "equal" (cv 24) (c0 "one"))) (c2 "equal" (cv 23) (c0 "zero")))))
      (add (c2 "equal" (c2 "equal" (c2 "greatest_factor" (cv 23) (cv 24)) (c0 "one")) (c2 "equal" (cv 23) (c0 "one"))))
      (add (c2 "equal" (c1 "numberp" (c2 "greatest_factor" (cv 23) (cv 24))) (c1 "not" (c2 "and" (c2 "or" (c1 "zerop" (cv 24)) (c2 "equal" (cv 24) (c0 "one"))) (c1 "not" (c1 "numberp" (cv 23)))))))
      (add (c2 "equal" (c1 "times_list" (c2 "append" (cv 23) (cv 24))) (c2 "times" (c1 "times_list" (cv 23)) (c1 "times_list" (cv 24)))))
      (add (c2 "equal" (c1 "prime_list" (c2 "append" (cv 23) (cv 24))) (c2 "and" (c1 "prime_list" (cv 23)) (c1 "prime_list" (cv 24)))))
      (add (c2 "equal" (c2 "equal" (cv 25) (c2 "times" (cv 22) (cv 25))) (c2 "and" (c1 "numberp" (cv 25)) (c2 "or" (c2 "equal" (cv 25) (c0 "zero")) (c2 "equal" (cv 22) (c0 "one"))))))
      (add (c2 "equal" (c2 "ge" (cv 23) (cv 24)) (c1 "not" (c2 "lt" (cv 23) (cv 24)))))
      (add (c2 "equal" (c2 "equal" (cv 23) (c2 "times" (cv 23) (cv 24))) (c2 "or" (c2 "equal" (cv 23) (c0 "zero")) (c2 "and" (c1 "numberp" (cv 23)) (c2 "equal" (cv 24) (c0 "one"))))))
      (add (c2 "equal" (c2 "remainder" (c2 "times" (cv 24) (cv 23)) (cv 24)) (c0 "zero")))
      (add (c2 "equal" (c2 "equal" (c2 "times" (cv 0) (cv 1)) (c0 "one")) (c6 "and" (c1 "not" (c2 "equal" (cv 0) (c0 "zero"))) (c1 "not" (c2 "equal" (cv 1) (c0 "zero"))) (c1 "numberp" (cv 0)) (c1 "numberp" (cv 1)) (c2 "equal" (c1 "sub1" (cv 0)) (c0 "zero")) (c2 "equal" (c1 "sub1" (cv 1)) (c0 "zero")))))
      (add (c2 "equal" (c2 "lt" (c1 "length" (c2 "delete" (cv 23) (cv 11))) (c1 "length" (cv 11))) (c2 "member" (cv 23) (cv 11))))
      (add (c2 "equal" (c1 "sort2" (c2 "delete" (cv 23) (cv 11))) (c2 "delete" (cv 23) (c1 "sort2" (cv 11)))))
      (add (c2 "equal" (c1 "dsort" (cv 23)) (c1 "sort2" (cv 23))))
      (add (c2 "equal" (c1 "length" (c2 "cons" (cv 0) (c2 "cons" (cv 1) (c2 "cons" (cv 2) (c2 "cons" (cv 3) (c2 "cons" (cv 4) (c2 "cons" (cv 5) (cv 6)))))))) (c2 "plus" (c0 "six") (c1 "length" (cv 6)))))
      (add (c2 "equal" (c2 "difference" (c1 "add1" (c1 "add1" (cv 23))) (c0 "two")) (c1 "fix" (cv 23))))
      (add (c2 "equal" (c2 "quotient" (c2 "plus" (cv 23) (c2 "plus" (cv 23) (cv 24))) (c0 "two")) (c2 "plus" (cv 23) (c2 "quotient" (cv 24) (c0 "two")))))
      (add (c2 "equal" (c2 "sigma" (c0 "zero") (cv 8)) (c2 "quotient" (c2 "times" (cv 8) (c1 "add1" (cv 8))) (c0 "two"))))
      (add (c2 "equal" (c2 "plus" (cv 23) (c1 "add1" (cv 24))) (c3 "if" (c1 "numberp" (cv 24)) (c1 "add1" (c2 "plus" (cv 23) (cv 24))) (c1 "add1" (cv 23)))))
      (add (c2 "equal" (c2 "equal" (c2 "difference" (cv 23) (cv 24)) (c2 "difference" (cv 25) (cv 24))) (c3 "if" (c2 "lt" (cv 23) (cv 24)) (c1 "not" (c2 "lt" (cv 24) (cv 25))) (c3 "if" (c2 "lt" (cv 25) (cv 24)) (c1 "not" (c2 "lt" (cv 24) (cv 23))) (c2 "equal" (c1 "fix" (cv 23)) (c1 "fix" (cv 25)))))))
      (add (c2 "equal" (c2 "meaning" (c1 "plus_tree" (c2 "delete" (cv 23) (cv 24))) (cv 0)) (c3 "if" (c2 "member" (cv 23) (cv 24)) (c2 "difference" (c2 "meaning" (c1 "plus_tree" (cv 24)) (cv 0)) (c2 "meaning" (cv 23) (cv 0))) (c2 "meaning" (c1 "plus_tree" (cv 24)) (cv 0)))))
      (add (c2 "equal" (c2 "times" (cv 23) (c1 "add1" (cv 24))) (c2 "if" (c1 "numberp" (cv 24)) (c3 "plus" (cv 23) (c2 "times" (cv 23) (cv 24)) (c1 "fix" (cv 23))))))
      (add (c2 "equal" (c2 "nth" (c0 "nil") (cv 8)) (c3 "if" (c1 "zerop" (cv 8)) (c0 "nil") (c0 "zero"))))
      (add (c2 "equal" (c1 "last" (c2 "append" (cv 0) (cv 1))) (c3 "if" (c1 "listp" (cv 1)) (c1 "last" (cv 1)) (c3 "if" (c1 "listp" (cv 0)) (c2 "cons" (c1 "car" (c1 "last" (cv 0))) (cv 1)) (cv 1)))))
      (add (c2 "equal" (c2 "equal" (c2 "lt" (cv 23) (cv 24)) (cv 25)) (c3 "if" (c2 "lt" (cv 23) (cv 24)) (c2 "equal" (c0 "true") (cv 25)) (c2 "equal" (c0 "false") (cv 25)))))
      (add (c2 "equal" (c2 "assignment" (cv 23) (c2 "append" (cv 0) (cv 1))) (c3 "if" (c2 "assignedp" (cv 23) (cv 0)) (c2 "assignment" (cv 23) (cv 0)) (c2 "assignment" (cv 23) (cv 1)))))
      (add (c2 "equal" (c1 "car" (c1 "gother" (cv 23))) (c3 "if" (c1 "listp" (cv 23)) (c1 "car" (c1 "flatten" (cv 23))) (c0 "zero"))))
      (add (c2 "equal" (c1 "flatten" (c1 "cdr" (c1 "gother" (cv 23)))) (c3 "if" (c1 "listp" (cv 23)) (c1 "cdr" (c1 "flatten" (cv 23))) (c2 "cons" (c0 "zero") (c0 "nil")))))
      (add (c2 "equal" (c2 "quotient" (c2 "times" (cv 24) (cv 23)) (cv 24)) (c3 "if" (c1 "zerop" (cv 24)) (c0 "zero") (c1 "fix" (cv 23)))))
      (add (c2 "equal" (c2 "get" (cv 9) (c3 "set" (cv 8) (cv 21) (cv 12))) (c3 "if" (c2 "eqp" (cv 9) (cv 8)) (cv 21) (c2 "get" (cv 9) (cv 12))))))))
(add-lemmas)

;; Tautology checker

(define* truep (subr bo (term terms) bool)
  (lambda (x lst)
    (tagcase x
      (prop (head args) (or (string=? (extract head name) "true") (list-mem x lst)))
      (else y (list-mem x lst)))))

(define* falsep (subr bo (term terms) bool)
  (lambda (x lst)
    (tagcase x
      (prop (head args) (or (string=? (extract head name) "false") (list-mem x lst)))
      (else y (list-mem x lst)))))

(define* tautologyp (subr bo (term terms terms) bool)
  (lambda (x true-lst false-lst)
    (cond ((truep x true-lst) #t)
          ((falsep x false-lst) #f)
          (else
           (tagcase x
             (var (v) #f)
             (prop (head args)
               (if (and (not (null? args)) (not (null? (cdr args)))
                        (not (null? (cdr (cdr args)))) (null? (cdr (cdr (cdr args)))))
                   (let ((test (car args)) (yes (car (cdr args))) (no (car (cdr (cdr args)))))
                     (if (string=? (extract head name) "if")
                         (cond ((truep test true-lst) (tautologyp yes true-lst false-lst))
                               ((falsep test false-lst) (tautologyp no true-lst false-lst))
                               (else (and (tautologyp yes (cons test true-lst) false-lst)
                                          (tautologyp no true-lst (cons test false-lst)))))
                         #f))
                   (failwith "assert false"))))))))

(define* tautp (subr bo (term) bool)
  (lambda (x)
    (let ((y (rewrite x)))
      (tautologyp y nil nil))))

;; the benchmark

(define* the-subst (subr bo () subst)
  (lambda ()
    (let* ((b23 (product (v 23) (t (cterm-to-term
                                    (c1 "f" (c2 "plus" (c2 "plus" (cv 0) (cv 1)) (c2 "plus" (cv 2) (c0 "zero"))))))))
           (b24 (product (v 24) (t (cterm-to-term
                                    (c1 "f" (c2 "times" (c2 "times" (cv 0) (cv 1)) (c2 "plus" (cv 2) (cv 3))))))))
           (b25 (product (v 25) (t (cterm-to-term
                                    (c1 "f" (c1 "reverse" (c2 "append" (c2 "append" (cv 0) (cv 1)) (c0 "nil"))))))))
           (b20 (product (v 20) (t (cterm-to-term
                                    (c2 "equal" (c2 "plus" (cv 0) (cv 1)) (c2 "difference" (cv 23) (cv 24)))))))
           (b22 (product (v 22) (t (cterm-to-term
                                    (c2 "lt" (c2 "remainder" (cv 0) (cv 1))
                                        (c2 "member" (cv 0) (c1 "length" (cv 1)))))))))
      (cons b23 (cons b24 (cons b25 (cons b20 (cons b22 nil))))))))

(define subst subst (the-subst))

(define term term
  (cterm-to-term
   (c2 "implies"
       (c2 "and"
           (c2 "implies" (cv 23) (cv 24))
           (c2 "and"
               (c2 "implies" (cv 24) (cv 25))
               (c2 "and"
                   (c2 "implies" (cv 25) (cv 20))
                   (c2 "implies" (cv 20) (cv 22)))))
       (c2 "implies" (cv 23) (cv 22)))))

;; The input, where no compiler can fold it: a global.
(define iterations int 3)

;; The original's main: 10 proofs; how many succeeded.
(define* main (subr bo () int)
  (lambda ()
    (letrec ((loop (subr bo (int int) int)
               (lambda (i ok)
                 (if (<= i 10)
                     (loop (+ i 1) (if (tautp (apply-subst subst term)) (+ ok 1) ok))
                     ok))))
      (loop 1 0))))

(define* run (subr bo (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (+ result (main))))))
(run iterations 0)
