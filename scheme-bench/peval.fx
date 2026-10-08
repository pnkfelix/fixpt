;;; PEVAL -- A simple partial evaluator for Scheme, written by Marc Feeley.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/peval.scm),
;;; ported to FX-26. Larceny's input: 2000 iterations of (test input1
;;; input2), input1 being the `reverse' procedure below (example8) and
;;; input2 ((a b c d e f g h i j k l m n o p q r s t u v w x y z)).
;;; Larceny checks only the tenth partial evaluation, which is also this
;;; port's value, shown as a datum.
;;; Answer: (lambda () (list (quote z) (quote y) (quote x) (quote w)
;;;   (quote v) (quote u) (quote t) (quote s) (quote r) (quote q) (quote p)
;;;   (quote o) (quote n) (quote m) (quote l) (quote k) (quote j) (quote i)
;;;   (quote h) (quote g) (quote f) (quote e) (quote d) (quote c) (quote b)
;;;   (quote a)))
;;;
;;; What the port changed, and why:
;;; - The partial evaluator walks and destructively rewrites Scheme data,
;;;   so its values are `sx', a sum of the kinds of datum it meets (symbols,
;;;   integers, booleans, the empty list, and mutable pairs), with `scar',
;;;   `scons', `sset-car!' and the rest over it. FX-26's `datum' is
;;;   immutable, so it cannot be used. A pair is a sum around an FX-26
;;;   pair: two objects where Scheme has one. The fixed symbols the code
;;;   builds with ('quote, 'lambda, 'let, 'list, '+, '*), the empty list,
;;;   #t and #f are made once, as Scheme's are.
;;; - `not-constant' was a fresh list compared by `eq?'; here it is a
;;;   variant of its own (`nc'), made once, so the comparison is the same.
;;; - FX-26 has no `eq?' on pairs. The `eq?' of the table of primitives
;;;   (no example folds it on pairs) is exact all the same: `same-pair?'
;;;   writes a marker into one pair's car, looks for it in the other's, and
;;;   puts the car back.
;;; - The primitive `/' is left out: it needs rationals, which FX-26 does
;;;   not have, and no example uses it.
;;; - `ref-count' returns a product (total, oper, always-evaled) instead of
;;;   a three-element list; its three counters are refs.
;;; - The quoted examples are written as Scheme text, read into `sx' once
;;;   when the program is loaded (as Scheme reads its quoted constants) by a
;;;   small reader here, `read-sx'.
;;; - `test' makes its ten partial evaluations left to right (Scheme leaves
;;;   the order of `list''s arguments unspecified; it decides only the
;;;   numbers in the renamed variables, not the answer).

(define-type sx
  (sumof (sy symbol) (nm int) (bl bool) (nl unit) (pr (pairof sx sx @heap)) (nc unit) (probe unit)))
(define-type sxpair (pairof sx sx @heap))
(define-effect sxe (maxeff (read @heap) (write @heap) (alloc @heap) spin))

;------------------------------------------------------------------------------

; Scheme's data, as `sx'.

(define snil sx (sum nl #u))
(define strue sx (sum bl #t))
(define sfalse sx (sum bl #f))
(define not-constant sx (sum nc #u)) ; special value indicating non-constant parms.
(define the-probe sx (sum probe #u))
(define s-quote sx (sum sy 'quote))
(define s-lambda sx (sum sy 'lambda))
(define s-let sx (sum sy 'let))
(define s-list sx (sum sy 'list))
(define s-plus sx (sum sy '+))
(define s-times sx (sum sy '*))

;; `car' of what is not a pair: an error, as in Scheme.
(define* not-a-pair (subr (read @heap) () sx) (lambda () (car (the (union nil sxpair) no-pair))))

(define* scons (subr (alloc @heap) (sx sx) sx) (lambda (a d) (sum pr (cons a d))))
(define* scar (subr (read @heap) (sx) sx) (lambda (x) (tagcase x (pr p (car p)) (else y (not-a-pair)))))
(define* scdr (subr (read @heap) (sx) sx) (lambda (x) (tagcase x (pr p (cdr p)) (else y (not-a-pair)))))
(define* sset-car! (subr (maxeff (read @heap) (write @heap)) (sx sx) unit)
  (lambda (x v) (tagcase x (pr p (set-car! p v)) (else y (begin (not-a-pair) #u)))))
(define* sset-cdr! (subr (maxeff (read @heap) (write @heap)) (sx sx) unit)
  (lambda (x v) (tagcase x (pr p (set-cdr! p v)) (else y (begin (not-a-pair) #u)))))
(define* scaar (subr (read @heap) (sx) sx) (lambda (x) (scar (scar x))))
(define* scadr (subr (read @heap) (sx) sx) (lambda (x) (scar (scdr x))))
(define* scdar (subr (read @heap) (sx) sx) (lambda (x) (scdr (scar x))))
(define* scddr (subr (read @heap) (sx) sx) (lambda (x) (scdr (scdr x))))
(define* scaddr (subr (read @heap) (sx) sx) (lambda (x) (scar (scddr x))))
(define* scdddr (subr (read @heap) (sx) sx) (lambda (x) (scdr (scddr x))))
(define* scadar (subr (read @heap) (sx) sx) (lambda (x) (scar (scdar x))))
(define* scadddr (subr (read @heap) (sx) sx) (lambda (x) (scar (scdddr x))))
(define* scaddar (subr (read @heap) (sx) sx) (lambda (x) (scar (scddr (scar x)))))

(define* spair? (subr pure (sx) bool) (lambda (x) (tagcase x (pr p #t) (else y #f))))
(define* snull? (subr pure (sx) bool) (lambda (x) (tagcase x (nl u #t) (else y #f))))
(define* ssymbol? (subr pure (sx) bool) (lambda (x) (tagcase x (sy s #t) (else y #f))))
(define* snumber? (subr pure (sx) bool) (lambda (x) (tagcase x (nm n #t) (else y #f))))
(define* sfalse? (subr pure (sx) bool) (lambda (x) (tagcase x (bl b (not b)) (else y #f))))
;; Whether `x' is the symbol `s'.
(define* sym-is? (subr pure (sx symbol) bool)
  (lambda (x s) (tagcase x (sy y (symbol=? y s)) (else y #f))))
(define* sym-of (subr (read @heap) (sx) symbol)
  (lambda (x) (tagcase x (sy s s) (else y (begin (not-a-pair) 'error)))))
(define* num-of (subr (read @heap) (sx) int)
  (lambda (x) (tagcase x (nm n n) (else y (begin (not-a-pair) 0)))))
(define* sbool (subr pure (bool) sx) (lambda (b) (if b strue sfalse)))

(define* slist1 (subr (alloc @heap) (sx) sx) (lambda (a) (scons a snil)))
(define* slist2 (subr (alloc @heap) (sx sx) sx) (lambda (a b) (scons a (scons b snil))))
(define* slist3 (subr (alloc @heap) (sx sx sx) sx) (lambda (a b c) (scons a (scons b (scons c snil)))))

;; Whether two pairs are one: write a marker into p's car and look for it
;; in q's (FX-26 has no `eq?' on pairs).
(define* same-pair? (subr (maxeff (read @heap) (write @heap)) (sxpair sxpair) bool)
  (lambda (p q)
    (let ((a (car p)))
      (begin (set-car! p the-probe)
             (let ((r (tagcase (car q) (probe u #t) (else y #f))))
               (begin (set-car! p a) r))))))

(define* seq? (subr (maxeff (read @heap) (write @heap)) (sx sx) bool)
  (lambda (a b)
    (tagcase a
      (sy x (tagcase b (sy y (symbol=? x y)) (else z #f)))
      (nm x (tagcase b (nm y (= x y)) (else z #f)))
      (bl x (tagcase b (bl y (if x y (not y))) (else z #f)))
      (nl x (snull? b))
      (nc x (tagcase b (nc y #t) (else z #f)))
      (probe x #f)
      (pr p (tagcase b (pr q (same-pair? p q)) (else z #f))))))

(define* sequal? (subr (maxeff (read @heap) (write @heap) spin) (sx sx) bool)
  (lambda (a b)
    (if (and (spair? a) (spair? b))
        (and (sequal? (scar a) (scar b)) (sequal? (scdr a) (scdr b)))
        (seq? a b))))

(define* slength (subr (maxeff (read @heap) spin) (sx) int)
  (lambda (l) (if (spair? l) (+ 1 (slength (scdr l))) 0)))
(define* slist-ref (subr (maxeff (read @heap) spin) (sx int) sx)
  (lambda (l i) (if (= i 0) (scar l) (slist-ref (scdr l) (- i 1)))))
(define* sappend (subr (maxeff (read @heap) (alloc @heap) spin) (sx sx) sx)
  (lambda (a b) (if (spair? a) (scons (scar a) (sappend (scdr a) b)) b)))
(define* sassq (subr (maxeff (read @heap) (write @heap) spin) (sx sx) sx)
  (lambda (x l)
    (cond ((not (spair? l)) sfalse)
          ((seq? (scaar l) x) (scar l))
          (else (sassq x (scdr l))))))
(define* smemq (subr (maxeff (read @heap) (write @heap) spin) (sx sx) bool)
  (lambda (x l) (and (spair? l) (or (seq? (scar l) x) (smemq x (scdr l))))))

;; What the partial evaluator reads: the globals from here to `simplify!'.
(define-effect evaluator
  (read (globals snil strue sfalse not-constant the-probe s-quote s-lambda
     s-let s-list s-plus s-times not-a-pair scons scar scdr sset-car! sset-cdr!
     scaar scadr scdar scddr scaddr scdddr scadar scadddr scaddar spair?
     snull? ssymbol? snumber? sfalse? sym-is? sym-of num-of sbool slist1
     slist2 slist3 same-pair? seq? sequal? slength slist-ref sappend sassq
     smemq smap sfor-each every? some? map2 get-last-pair const-expr?
     const-value quot current-num new-variable new-variables alphatize
     not-constant? remove-constant extract-constant beta-subst ref-count
     binding-frame bound-expr add-binding for-each! arg-pattern ssum sproduct
     *primitives* passq reduce-global constant-fold-global quote-nil nil-entry
     peval simplify!)))

(define-effect sxlib
  (read (globals not-a-pair scons scar scdr spair? snull? snil sfalse strue sbool)))

(define smap (poly ((e effect)) (subr (maxeff e sxe sxlib) ((subr e (sx) sx) sx) sx))
  (lambda (f l)
    (letrec ((loop (subr (maxeff e sxe sxlib) (sx) sx)
               (lambda (l) (if (spair? l) (scons (f (scar l)) (loop (scdr l))) snil))))
      (loop l))))
(define sfor-each (poly ((e effect)) (subr (maxeff e sxe sxlib) ((subr e (sx) unit) sx) unit))
  (lambda (f l)
    (letrec ((loop (subr (maxeff e sxe sxlib) (sx) unit)
               (lambda (l) (if (spair? l) (begin (f (scar l)) (loop (scdr l))) #u))))
      (loop l))))

;------------------------------------------------------------------------------

; Utilities

(define every? (poly ((e effect)) (subr (maxeff e sxe sxlib) ((subr e (sx) bool) sx) bool))
  (lambda (pred? l)
    (letrec ((loop (subr (maxeff e sxe sxlib) (sx) bool)
               (lambda (l) (or (snull? l) (and (pred? (scar l)) (loop (scdr l)))))))
      (loop l))))

(define some? (poly ((e effect)) (subr (maxeff e sxe sxlib) ((subr e (sx) bool) sx) bool))
  (lambda (pred? l)
    (letrec ((loop (subr (maxeff e sxe sxlib) (sx) bool)
               (lambda (l) (if (snull? l) #f (or (pred? (scar l)) (loop (scdr l)))))))
      (loop l))))

(define map2 (poly ((e effect)) (subr (maxeff e sxe sxlib) ((subr e (sx sx) sx) sx sx) sx))
  (lambda (f l1 l2)
    (letrec ((loop (subr (maxeff e sxe sxlib) (sx sx) sx)
               (lambda (l1 l2)
                 (if (spair? l1)
                     (scons (f (scar l1) (scar l2)) (loop (scdr l1) (scdr l2)))
                     snil))))
      (loop l1 l2))))

(define* get-last-pair (subr (maxeff (read @heap) spin) (sx) sx)
  (lambda (l) (let ((x (scdr l))) (if (spair? x) (get-last-pair x) l))))

;------------------------------------------------------------------------------
;
; The partial evaluator.

(define* const-expr? (subr (read @heap) (sx) bool) ; is 'expr' a constant expression?
  (lambda (expr)
    (and (not (ssymbol? expr))
         (or (not (spair? expr))
             (sym-is? (scar expr) 'quote)))))

(define* const-value (subr (read @heap) (sx) sx) ; return the value of a constant expression
  (lambda (expr)
    (if (spair? expr) ; then it must be a quoted constant
        (scadr expr)
        expr)))

(define* quot (subr (alloc @heap) (sx) sx) ; make a quoted constant whose value is 'val'
  (lambda (val) (slist2 s-quote val)))

(define current-num (ref int @heap) (new 0))

(define* new-variable (subr (maxeff (read @heap) (write @heap)) (sx) sx)
  (lambda (name)
    (begin
      (set current-num (+ (get current-num) 1))
      (sum sy (string->symbol
               (string-append (symbol->string (sym-of name))
                              (string-append "_" (int->string (get current-num)))))))))

(define* new-variables (subr sxe (sx sx) sx)
  (lambda (parms env)
    (sappend (smap (lambda (x) (scons x (new-variable x))) parms) env)))

(define* alphatize (subr sxe (sx sx) sx)
  (lambda (exp env) ; return a copy of 'exp' where each bound var has
    (letrec ((alpha (subr (maxeff sxe evaluator) (sx) sx) ; been renamed (to prevent aliasing problems)
               (lambda (exp)
                 (cond ((const-expr? exp)
                        (quot (const-value exp)))
                       ((ssymbol? exp)
                        (let ((x (sassq exp env))) (if (spair? x) (scdr x) exp)))
                       ((or (sym-is? (scar exp) 'if) (sym-is? (scar exp) 'begin))
                        (scons (scar exp) (smap alpha (scdr exp))))
                       ((or (sym-is? (scar exp) 'let) (sym-is? (scar exp) 'letrec))
                        (let ((new-env (new-variables (smap scar (scadr exp)) env)))
                          (slist3 (scar exp)
                                  (smap (lambda (x)
                                          (slist2 (scdr (sassq (scar x) new-env))
                                                  (if (sym-is? (scar exp) 'let)
                                                      (alpha (scadr x))
                                                      (alphatize (scadr x) new-env))))
                                        (scadr exp))
                                  (alphatize (scaddr exp) new-env))))
                       ((sym-is? (scar exp) 'lambda)
                        (let ((new-env (new-variables (scadr exp) env)))
                          (slist3 s-lambda
                                  (smap (lambda (x) (scdr (sassq x new-env))) (scadr exp))
                                  (alphatize (scaddr exp) new-env))))
                       (else
                        (smap alpha exp))))))
      (alpha exp))))


(define* not-constant? (subr pure (sx) bool) (lambda (x) (tagcase x (nc u #t) (else y #f))))

(define* remove-constant (subr (maxeff (read @heap) (alloc @heap) spin) (sx sx) sx)
  (lambda (l a) ; remove from list 'l' all elements whose
    (cond ((snull? l) ; corresponding element in 'a' is a constant
           snil)
          ((not-constant? (scar a))
           (scons (scar l) (remove-constant (scdr l) (scdr a))))
          (else
           (remove-constant (scdr l) (scdr a))))))

(define* extract-constant (subr (maxeff (read @heap) (alloc @heap) spin) (sx sx) sx)
  (lambda (l a) ; extract from list 'l' all elements whose
    (cond ((snull? l) ; corresponding element in 'a' is a constant
           snil)
          ((not-constant? (scar a))
           (extract-constant (scdr l) (scdr a)))
          (else
           (scons (scar l) (extract-constant (scdr l) (scdr a)))))))

(define* beta-subst (subr sxe (sx sx) sx)
  (lambda (exp env) ; return a modified 'exp' where each var named in
    (letrec ((bs (subr (maxeff sxe evaluator) (sx) sx) ; 'env' is replaced by the corresponding expr (it
               (lambda (exp)
                 (cond ((const-expr? exp) ; is assumed that the code has been alphatized)
                        (quot (const-value exp)))
                       ((ssymbol? exp)
                        (let ((x (sassq exp env)))
                          (if (spair? x) (scdr x) exp)))
                       ((or (sym-is? (scar exp) 'if) (sym-is? (scar exp) 'begin))
                        (scons (scar exp) (smap bs (scdr exp))))
                       ((or (sym-is? (scar exp) 'let) (sym-is? (scar exp) 'letrec))
                        (slist3 (scar exp)
                                (smap (lambda (x) (slist2 (scar x) (bs (scadr x)))) (scadr exp))
                                (bs (scaddr exp))))
                       ((sym-is? (scar exp) 'lambda)
                        (slist3 s-lambda
                                (scadr exp)
                                (bs (scaddr exp))))
                       (else
                        (smap bs exp))))))
      (bs exp))))

;------------------------------------------------------------------------------
;
; The expression simplifier's helpers.

(define-type counts (productof (total int) (oper int) (always bool)))

(define* ref-count (subr sxe (sx sx) counts)
  (lambda (exp var) ; compute how many references to variable 'var'
    (let ((total (the (ref int @heap) (new 0))) ; are contained in 'exp'
          (oper (the (ref int @heap) (new 0)))
          (always-evaled (the (ref bool @heap) (new #t))))
      (letrec ((rc (subr (maxeff sxe evaluator) (sx bool) unit)
                 (lambda (exp ae)
                   (cond ((const-expr? exp) #u)
                         ((ssymbol? exp)
                          (if (seq? exp var)
                              (begin
                                (set total (+ (get total) 1))
                                (set always-evaled (and ae (get always-evaled))))
                              #u))
                         ((sym-is? (scar exp) 'if)
                          (begin
                            (rc (scadr exp) ae)
                            (sfor-each (lambda (x) (rc x #f)) (scddr exp))))
                         ((sym-is? (scar exp) 'begin)
                          (sfor-each (lambda (x) (rc x ae)) (scdr exp)))
                         ((or (sym-is? (scar exp) 'let) (sym-is? (scar exp) 'letrec))
                          (begin
                            (sfor-each (lambda (x) (rc (scadr x) ae)) (scadr exp))
                            (rc (scaddr exp) ae)))
                         ((sym-is? (scar exp) 'lambda)
                          (rc (scaddr exp) #f))
                         (else
                          (begin
                            (sfor-each (lambda (x) (rc x ae)) exp)
                            (if (ssymbol? (scar exp))
                                (if (seq? (scar exp) var) (set oper (+ (get oper) 1)) #u)
                                #u)))))))
        (begin
          (rc exp #t)
          (product (total (get total)) (oper (get oper)) (always (get always-evaled))))))))

(define* binding-frame (subr sxe (sx sx) sx)
  (lambda (var env)
    (cond ((snull? env) sfalse)
          ((or (sym-is? (scaar env) 'let) (sym-is? (scaar env) 'letrec))
           (if (spair? (sassq var (scadar env))) (scar env) (binding-frame var (scdr env))))
          ((sym-is? (scaar env) 'lambda)
           (if (smemq var (scadar env)) (scar env) (binding-frame var (scdr env))))
          (else
           (begin (not-a-pair) sfalse))))) ; "ill-formed environment"

(define* bound-expr (subr sxe (sx sx) sx)
  (lambda (var frame)
    (cond ((or (sym-is? (scar frame) 'let) (sym-is? (scar frame) 'letrec))
           (scadr (sassq var (scadr frame))))
          ((sym-is? (scar frame) 'lambda)
           not-constant)
          (else
           (not-a-pair))))) ; "ill-formed frame"

(define* add-binding (subr sxe (sx sx sx) sx)
  (lambda (val frame name)
    (letrec ((find-val (subr (maxeff sxe evaluator) (sx sx) sx)
               (lambda (val bindings)
                 (cond ((snull? bindings) sfalse)
                       ((sequal? val (scadar bindings)) ; *kludge* equal? is not exactly what
                        (scaar bindings))               ; we want...
                       (else
                        (find-val val (scdr bindings)))))))
      (let ((found (find-val val (scadr frame))))
        (if (not (sfalse? found))
            found
            (let ((var (new-variable name)))
              (begin
                (sset-cdr! (get-last-pair (scadr frame)) (slist1 (slist2 var val)))
                var)))))))

(define for-each! (poly ((e effect)) (subr (maxeff e sxe sxlib) ((subr e (sx) unit) sx) unit))
  (lambda (proc! l) ; call proc! on each CONS CELL in the list 'l'
    (letrec ((loop (subr (maxeff e sxe sxlib) (sx) unit)
               (lambda (l) (if (not (snull? l)) (begin (proc! l) (loop (scdr l))) #u))))
      (loop l))))

(define* arg-pattern (subr (maxeff (read @heap) (alloc @heap) spin) (sx) sx)
  (lambda (exps) ; return the argument pattern (i.e. the list of
    (if (snull? exps) ; constants in 'exps' but with the not-constant
        snil          ; value wherever the corresponding expression in
        (scons (if (const-expr? (scar exps)) ; 'exps' is not a constant)
                   (const-value (scar exps))
                   not-constant)
               (arg-pattern (scdr exps))))))

;------------------------------------------------------------------------------
;
; Knowledge about primitive procedures.

(define* ssum (subr (maxeff (read @heap) spin) (sx int) int)
  (lambda (lst n) (if (snull? lst) n (ssum (scdr lst) (+ n (num-of (scar lst)))))))

(define* sproduct (subr (maxeff (read @heap) spin) (sx int) int)
  (lambda (lst n) (if (snull? lst) n (sproduct (scdr lst) (* n (num-of (scar lst)))))))

(define-type prim (subr (maxeff sxe evaluator) (sx) sx))

;; The primitive `/' is left out: see the header.
(define *primitives* (listof (pairof symbol prim @heap) @heap)
  (list (cons 'car (lambda (args)
                     (if (and (= (slength args) 1)
                              (spair? (scar args)))
                         (quot (scar (scar args)))
                         sfalse)))
        (cons 'cdr (lambda (args)
                     (if (and (= (slength args) 1)
                              (spair? (scar args)))
                         (quot (scdr (scar args)))
                         sfalse)))
        (cons '+ (lambda (args)
                   (if (every? snumber? args)
                       (quot (sum nm (ssum args 0)))
                       sfalse)))
        (cons '* (lambda (args)
                   (if (every? snumber? args)
                       (quot (sum nm (sproduct args 1)))
                       sfalse)))
        (cons '- (lambda (args)
                   (if (and (> (slength args) 0)
                            (every? snumber? args))
                       (quot (sum nm (if (snull? (scdr args))
                                         (- 0 (num-of (scar args)))
                                         (- (num-of (scar args)) (ssum (scdr args) 0)))))
                       sfalse)))
        (cons '< (lambda (args)
                   (if (and (= (slength args) 2)
                            (every? snumber? args))
                       (quot (sbool (< (num-of (scar args)) (num-of (scadr args)))))
                       sfalse)))
        (cons '= (lambda (args)
                   (if (and (= (slength args) 2)
                            (every? snumber? args))
                       (quot (sbool (= (num-of (scar args)) (num-of (scadr args)))))
                       sfalse)))
        (cons '> (lambda (args)
                   (if (and (= (slength args) 2)
                            (every? snumber? args))
                       (quot (sbool (> (num-of (scar args)) (num-of (scadr args)))))
                       sfalse)))
        (cons 'eq? (lambda (args)
                     (if (= (slength args) 2)
                         (quot (sbool (seq? (scar args) (scadr args))))
                         sfalse)))
        (cons 'not (lambda (args)
                     (if (= (slength args) 1)
                         (quot (sbool (sfalse? (scar args))))
                         sfalse)))
        (cons 'null? (lambda (args)
                       (if (= (slength args) 1)
                           (quot (sbool (snull? (scar args))))
                           sfalse)))
        (cons 'pair? (lambda (args)
                       (if (= (slength args) 1)
                           (quot (sbool (spair? (scar args))))
                           sfalse)))
        (cons 'symbol? (lambda (args)
                         (if (= (slength args) 1)
                             (quot (sbool (ssymbol? (scar args))))
                             sfalse)))))

(define* passq (subr (maxeff (read @heap) spin) (symbol (listof (pairof symbol prim @heap) @heap)) (union nil (pairof symbol prim @heap)))
  (lambda (name l)
    (cond ((null? l) no-pair)
          ((symbol=? (car (car l)) name) (car l))
          (else (passq name (cdr l))))))

(define* reduce-global (subr sxe (sx sx) sx)
  (lambda (name args)
    (let ((x (passq (sym-of name) *primitives*)))
      (if (null? x) sfalse ((cdr x) args)))))

(define* constant-fold-global (subr sxe (sx sx) sx)
  (lambda (name exprs)
    (letrec ((flatten (subr (maxeff sxe evaluator) (sx sx) sx)
               (lambda (args op)
                 (cond ((snull? args)
                        snil)
                       ((and (spair? (scar args)) (seq? (scaar args) op))
                        (sappend (flatten (scdar args) op) (flatten (scdr args) op)))
                       (else
                        (scons (scar args) (flatten (scdr args) op)))))))
      (let* ((args (if (or (sym-is? name '+) (sym-is? name '*)) ; associative ops
                       (flatten exprs name)
                       exprs))
             (folded (if (every? const-expr? args)
                         (reduce-global name (smap const-value args))
                         sfalse)))
        (if (not (sfalse? folded))
            folded
            (let* ((pattern (arg-pattern args))
                   (non-const (remove-constant args pattern))
                   (const (smap const-value (extract-constant args pattern))))
              (cond ((sym-is? name '+) ; + is commutative
                     (let ((x (reduce-global s-plus const)))
                       (if (not (sfalse? x))
                           (let ((y (const-value x)))
                             (scons s-plus
                                    (if (= (num-of y) 0) non-const (scons x non-const))))
                           (scons name args))))
                    ((sym-is? name '*) ; * is commutative
                     (let ((x (reduce-global s-times const)))
                       (if (not (sfalse? x))
                           (let ((y (const-value x)))
                             (scons s-times
                                    (if (= (num-of y) 1) non-const (scons x non-const))))
                           (scons name args))))
                    ((sym-is? name 'cons)
                     (cond ((and (const-expr? (scadr args))
                                 (snull? (const-value (scadr args))))
                            (slist2 s-list (scar args)))
                           ((and (spair? (scadr args))
                                 (sym-is? (scar (scadr args)) 'list))
                            (scons s-list (scons (scar args) (scdr (scadr args)))))
                           (else
                            (scons name args))))
                    (else
                     (scons name args)))))))))

;------------------------------------------------------------------------------
;
; (peval proc args) will transform a procedure that is known to be called
; with constants as some of its arguments into a specialized procedure that
; is 'equivalent' but accepts only the non-constant parameters.  'proc' is the
; list representation of a lambda-expression and 'args' is a list of values,
; one for each parameter of the lambda-expression.  A special value (i.e.
; 'not-constant') is used to indicate an argument that is not a constant.
; The returned procedure is one that has as parameters the parameters of the
; original procedure which are NOT passed constants.  Constants will have been
; substituted for the constant parameters that are referenced in the body
; of the procedure.
;
; For example:
;
;   (peval
;     '(lambda (x y z) (f z x y)) ; the procedure
;     (list 1 not-constant #t))   ; the knowledge about x, y and z
;
; will return: (lambda (y) (f '#t '1 y))

(define quote-nil sx (scons s-quote (scons snil snil)))   ; ''()
(define nil-entry sx (scons snil snil))                   ; '(())

;; The partial evaluator and the expression simplifier call each other.
(define-rec
  (peval (subr (maxeff sxe evaluator) (sx sx) sx)
    (lambda (proc args)
      (simplify!
        (let ((parms (scadr proc))  ; get the parameter list
              (body (scaddr proc))) ; get the body of the procedure
          (slist3 s-lambda
                  (remove-constant parms args) ; remove the constant parameters
                  (beta-subst ; in the body, replace variable refs to the constant
                    body      ; parameters by the corresponding constant
                    (map2 (lambda (x y) (if (not-constant? y) nil-entry (scons x (quot y))))
                          parms
                          args)))))))

  ; The expression simplifier.
  (simplify! (subr (maxeff sxe evaluator) (sx) sx)
    (lambda (exp) ; simplify the expression 'exp' destructively (it
                  ; is assumed that the code has been alphatized)
      (let ((changed? (the (ref bool @heap) (new #f))))
        (letrec
          ((simp! (subr (maxeff sxe evaluator) (sx sx) unit)
             (lambda (where env)
               (letrec
                 ((s! (subr (maxeff sxe evaluator) (sx) unit)
                    (lambda (where)
                      (let ((exp (scar where)))
                        (cond ((const-expr? exp) #u) ; leave constants the way they are

                              ((ssymbol? exp) #u)    ; leave variable references the way they are

                              ((sym-is? (scar exp) 'if) ; dead code removal for conditionals
                               (begin
                                 (s! (scdr exp))        ; simplify the predicate
                                 (if (const-expr? (scadr exp)) ; is the predicate a constant?
                                     (begin
                                       (sset-car! where
                                         (let ((v (const-value (scadr exp))))
                                           (if (or (sfalse? v) (snull? v)) ; false?
                                               (if (= (slength exp) 3) quote-nil (scadddr exp))
                                               (scaddr exp))))
                                       (s! where))
                                     (for-each! s! (scddr exp))))) ; simplify consequent and alt.

                              ((sym-is? (scar exp) 'begin)
                               (begin
                                 (for-each! s! (scdr exp))
                                 (letrec ((loop (subr (maxeff sxe evaluator) (sx) unit)
                                            (lambda (exps) ; remove all useless expressions
                                              (if (not (snull? (scddr exps))) ; not last expression?
                                                  (let ((x (scadr exps)))
                                                    (loop (if (or (const-expr? x)
                                                                  (ssymbol? x)
                                                                  (and (spair? x) (sym-is? (scar x) 'lambda)))
                                                              (begin (sset-cdr! exps (scddr exps)) exps)
                                                              (scdr exps))))
                                                  #u))))
                                   (loop exp))
                                 (if (snull? (scddr exp)) ; only one expression in the begin?
                                     (sset-car! where (scadr exp))
                                     #u)))

                              ((or (sym-is? (scar exp) 'let) (sym-is? (scar exp) 'letrec))
                               (let ((new-env (scons exp env)))
                                 (letrec
                                   ((keep (subr (maxeff sxe evaluator) (int) sx)
                                      (lambda (i)
                                        (if (>= i (slength (scadar where)))
                                            snil
                                            (let* ((var (scar (slist-ref (scadar where) i)))
                                                   (val (scadr (sassq var (scadar where))))
                                                   (refs (ref-count (scar where) var))
                                                   (self-refs (ref-count val var))
                                                   (total-refs (- (extract refs total) (extract self-refs total)))
                                                   (oper-refs (- (extract refs oper) (extract self-refs oper))))
                                              (cond ((= total-refs 0)
                                                     (keep (+ i 1)))
                                                    ((or (const-expr? val)
                                                         (ssymbol? val)
                                                         (and (spair? val)
                                                              (sym-is? (scar val) 'lambda)
                                                              (= total-refs 1)
                                                              (= oper-refs 1)
                                                              (= (extract self-refs total) 0))
                                                         (and (extract refs always)
                                                              (= total-refs 1)))
                                                     (begin
                                                       (sset-car! where
                                                         (beta-subst (scar where)
                                                                     (slist1 (scons var val))))
                                                       (keep (+ i 1))))
                                                    (else
                                                     (scons var (keep (+ i 1))))))))))
                                   (begin
                                     (simp! (scddr exp) new-env)
                                     (for-each! (lambda (x) (simp! (scdar x) new-env)) (scadr exp))
                                     (let ((to-keep (keep 0)))
                                       (if (< (slength to-keep) (slength (scadar where)))
                                           (begin
                                             (if (snull? to-keep)
                                                 (sset-car! where (scaddar where))
                                                 (sset-car! (scdar where)
                                                   (smap (lambda (v) (sassq v (scadar where))) to-keep)))
                                             (s! where))
                                           (if (snull? to-keep)
                                               (sset-car! where (scaddar where))
                                               #u)))))))

                              ((sym-is? (scar exp) 'lambda)
                               (simp! (scddr exp) (scons exp env)))

                              (else
                               (begin
                                 (for-each! s! exp)
                                 (cond ((ssymbol? (scar exp)) ; is the operator position a var ref?
                                        (let ((frame (binding-frame (scar exp) env)))
                                          (if (spair? frame) ; is it a bound variable?
                                              (let ((proc (bound-expr (scar exp) frame)))
                                                (if (and (spair? proc)
                                                         (sym-is? (scar proc) 'lambda)
                                                         (some? const-expr? (scdr exp)))
                                                    (let* ((args (arg-pattern (scdr exp)))
                                                           (new-proc (peval proc args))
                                                           (new-args (remove-constant (scdr exp) args)))
                                                      (sset-car! where
                                                        (scons (add-binding new-proc frame (scar exp))
                                                               new-args)))
                                                    #u))
                                              (sset-car! where
                                                (constant-fold-global (scar exp) (scdr exp))))))
                                       ((not (spair? (scar exp))) #u)
                                       ((sym-is? (scaar exp) 'lambda)
                                        (begin
                                          (sset-car! where
                                            (slist3 s-let
                                                    (map2 slist2 (scadar exp) (scdr exp))
                                                    (scaddar exp)))
                                          (s! where)))
                                       (else #u)))))))))
                 (s! where))))

           (remove-empty-calls! (subr (maxeff sxe evaluator) (sx sx) unit)
             (lambda (where env)
               (letrec
                 ((rec! (subr (maxeff sxe evaluator) (sx) unit)
                    (lambda (where)
                      (let ((exp (scar where)))
                        (cond ((const-expr? exp) #u)
                              ((ssymbol? exp) #u)
                              ((sym-is? (scar exp) 'if)
                               (begin
                                 (rec! (scdr exp))
                                 (rec! (scddr exp))
                                 (rec! (scdddr exp))))
                              ((sym-is? (scar exp) 'begin)
                               (for-each! rec! (scdr exp)))
                              ((or (sym-is? (scar exp) 'let) (sym-is? (scar exp) 'letrec))
                               (let ((new-env (scons exp env)))
                                 (begin
                                   (remove-empty-calls! (scddr exp) new-env)
                                   (for-each! (lambda (x) (remove-empty-calls! (scdar x) new-env))
                                              (scadr exp)))))
                              ((sym-is? (scar exp) 'lambda)
                               (rec! (scddr exp)))
                              (else
                               (begin
                                 (for-each! rec! (scdr exp))
                                 (if (and (snull? (scdr exp)) (ssymbol? (scar exp)))
                                     (let ((frame (binding-frame (scar exp) env)))
                                       (if (spair? frame) ; is it a bound variable?
                                           (let ((proc (bound-expr (scar exp) frame)))
                                             (if (and (spair? proc)
                                                      (sym-is? (scar proc) 'lambda))
                                                 (begin
                                                   (set changed? #t)
                                                   (sset-car! where (scaddr proc)))
                                                 #u))
                                           #u))
                                     #u))))))))
                 (rec! where)))))

          (let ((x (slist1 exp)))
            (letrec ((loop (subr (maxeff sxe evaluator) () sx)
                       (lambda ()
                         (begin
                           (set changed? #f)
                           (simp! x snil)
                           (remove-empty-calls! x snil)
                           (if (get changed?) (loop) (scar x))))))
              (loop))))))))

(define* partial-evaluate (subr sxe (sx sx) sx)
  (lambda (proc args)
    (peval (alphatize proc snil) args)))

;------------------------------------------------------------------------------
;
; Reading the examples: a small reader of Scheme text into `sx', for the
; quoted data of the original (symbols, integers, #t, #f, lists and ').

(define* delimiter? (subr pure (char) bool)
  (lambda (c) (or (char-whitespace? c) (char=? c #\() (char=? c #\)))))

(define* skip-space (subr (maxeff (read @heap) (write @heap) spin) (string (ref int @heap)) unit)
  (lambda (s pos)
    (if (and (< (get pos) (string-length s)) (char-whitespace? (string-ref s (get pos))))
        (begin (set pos (+ (get pos) 1)) (skip-space s pos))
        #u)))

(define* token-end (subr spin (string int) int)
  (lambda (s i)
    (if (and (< i (string-length s)) (not (delimiter? (string-ref s i))))
        (token-end s (+ i 1))
        i)))

(define* digits (subr spin (string int int int) int)
  (lambda (s i j acc)
    (if (< i j)
        (digits s (+ i 1) j (+ (* acc 10) (- (char->integer (string-ref s i)) 48)))
        acc)))

(define-effect reader
  (read (globals read-datum read-tail skip-space token-end delimiter? digits
     sbool strue sfalse scons slist2 s-quote snil)))

(define-rec
  (read-datum (subr (maxeff sxe reader) (string (ref int @heap)) sx)
    (lambda (s pos)
      (begin
        (skip-space s pos)
        (let ((c (string-ref s (get pos))))
          (cond ((char=? c #\() (begin (set pos (+ (get pos) 1)) (read-tail s pos)))
                ((char=? c #\') (begin (set pos (+ (get pos) 1)) (slist2 s-quote (read-datum s pos))))
                (else
                 (let* ((i (get pos)) (j (token-end s i)))
                   (begin
                     (set pos j)
                     (cond ((char=? c #\#) (sbool (char=? (string-ref s (+ i 1)) #\t)))
                           ((char-numeric? c) (sum nm (digits s i j 0)))
                           (else (sum sy (string->symbol (substring s i j)))))))))))))
  (read-tail (subr (maxeff sxe reader) (string (ref int @heap)) sx)
    (lambda (s pos)
      (begin
        (skip-space s pos)
        (if (char=? (string-ref s (get pos)) #\))
            (begin (set pos (+ (get pos) 1)) snil)
            (let ((x (read-datum s pos)))
              (scons x (read-tail s pos))))))))

(define* read-sx (subr sxe (string) sx)
  (lambda (s) (read-datum s (new 0))))

;------------------------------------------------------------------------------
;
; Examples:

(define* try-peval (subr sxe (sx sx) sx)
  (lambda (proc args)
    (partial-evaluate proc args)))

; . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

(define example1 sx (read-sx "
  (lambda (a b c)
     (if (null? a) b (+ (car a) c)))"))

;(try-peval example1 (list '(10 11) not-constant '1))

; . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

(define example2 sx (read-sx "
  (lambda (x y)
     (let ((q (lambda (a b) (if (< a 0) b (- 10 b)))))
       (if (< x 0) (q (- y) (- x)) (q y x))))"))

;(try-peval example2 (list not-constant '1))

; . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

(define example3 sx (read-sx "
  (lambda (l n)
     (letrec ((add-list
               (lambda (l n)
                 (if (null? l)
                   '()
                   (cons (+ (car l) n) (add-list (cdr l) n))))))
       (add-list l n)))"))

;(try-peval example3 (list not-constant '1))

;(try-peval example3 (list '(1 2 3) not-constant))

; . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

(define example4 sx (read-sx "
  (lambda (exp env)
     (letrec ((eval
               (lambda (exp env)
                 (letrec ((eval-list
                            (lambda (l env)
                              (if (null? l)
                                '()
                                (cons (eval (car l) env)
                                      (eval-list (cdr l) env))))))
                   (if (symbol? exp) (lookup exp env)
                     (if (not (pair? exp)) exp
                       (if (eq? (car exp) 'quote) (car (cdr exp))
                         (apply (eval (car exp) env)
                                (eval-list (cdr exp) env)))))))))
       (eval exp env)))"))

;(try-peval example4 (list 'x not-constant))

;(try-peval example4 (list '(f 1 2 3) not-constant))

; . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

(define example5 sx (read-sx "
  (lambda (a b)
     (letrec ((funct
               (lambda (x)
                 (+ x b (if (< x 1) 0 (funct (- x 1)))))))
       (funct a)))"))

;(try-peval example5 (list '5 not-constant))

; . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

(define example6 sx (read-sx "
  (lambda ()
     (letrec ((fib
               (lambda (x)
                 (if (< x 2) x (+ (fib (- x 1)) (fib (- x 2)))))))
       (fib 10)))"))

;(try-peval example6 '())

; . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

(define example7 sx (read-sx "
  (lambda (input)
     (letrec ((copy (lambda (in)
                      (if (pair? in)
                        (cons (copy (car in))
                              (copy (cdr in)))
                        in))))
       (copy input)))"))

;(try-peval example7 (list '(a b c d e f g h i j k l m n o p q r s t u v w x y z)))

; . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

;; The quoted constants `test' passes.
(define list-10-11 sx (read-sx "(10 11)"))
(define list-1-2-3 sx (read-sx "(1 2 3)"))
(define sym-x sx (read-sx "x"))
(define list-f-1-2-3 sx (read-sx "(f 1 2 3)"))
(define list-a-z sx (read-sx "(a b c d e f g h i j k l m n o p q r s t u v w x y z)"))

(define* test (subr sxe (sx sx) sx)
  (lambda (input1 input2)
    (begin
      (set current-num 0)
      (let* ((r1 (try-peval example1 (slist3 list-10-11 not-constant (sum nm 1))))
             (r2 (try-peval example2 (slist2 not-constant (sum nm 1))))
             (r3 (try-peval example3 (slist2 not-constant (sum nm 1))))
             (r4 (try-peval example3 (slist2 list-1-2-3 not-constant)))
             (r5 (try-peval example4 (slist2 sym-x not-constant)))
             (r6 (try-peval example4 (slist2 list-f-1-2-3 not-constant)))
             (r7 (try-peval example5 (slist2 (sum nm 5) not-constant)))
             (r8 (try-peval example6 snil))
             (r9 (try-peval example7 (slist1 list-a-z)))
             (r10 (try-peval input1 input2)))
        (scons r1 (scons r2 (scons r3 (scons r4 (scons r5
          (scons r6 (scons r7 (scons r8 (scons r9 (scons r10 snil))))))))))))))

;; The result, for printing: a datum.
(define* sx->datum (subr (maxeff (read @heap) spin) (sx) datum)
  (lambda (x)
    (tagcase x
      (sy s (string->symbol (symbol->string s)))
      (nm n n)
      (bl b b)
      (nl u nil)
      (pr p (cons (sx->datum (car p)) (sx->datum (cdr p))))
      (nc u 'not-constant)
      (probe u 'probe))))

;; The inputs, where no compiler can fold them (Larceny's `hide'): globals,
;; which a later definition may replace.
(define input1 sx (read-sx "
  (lambda (input)
    (letrec ((reverse (lambda (in result)
                        (if (pair? in)
                          (reverse (cdr in) (cons (car in) result))
                          result))))
      (reverse input '())))"))
(define input2 sx (read-sx "((a b c d e f g h i j k l m n o p q r s t u v w x y z))"))
(define iterations int 2000)

(define* run (subr sxe (int sx) sx)
  (lambda (i result) (if (= i 0) result (run (- i 1) (test input1 input2)))))
(sx->datum (slist-ref (run iterations snil) 9))
