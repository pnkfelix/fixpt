;;; Typed hygienic macros, in FX-26: what a template's export binds of what
;;; its uses give, compared and said, and the names a template binds in its
;;; uses of macros that make definitions (`macros.rs`'s `exports`,
;;; `shown_exports` and `binders_under`). Part of the expander: loaded by
;;; `macros-files.fx`, and loading `macros-align.fx`, whose nodes these read,
;;; so that `macros.fx` takes one instance of each through it.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define align-module ((proj (load-module "fx26:macros-align.fx") rs re rm rc rp)))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types (type syn))
(import parser-module syn-symbol? syn-symbol (type names))
(import types-module fail-at name-in? proper-items sorted-strings joined atm-var atm-rib-of
        atm-lit (type fails atm atms strings))
(import align-module node-kids node-syn pvar? makes-defns? normal atm-in? lv-rib lv-cage k-pair
        k-form k-desc k-binder (type levels pvars))

;;; ------------------------------------------------------------ exports

;; What an export binds of what a use gives, as compared (`macros.rs`'s
;; `exports`): its pattern variables' atoms and its ribcages, each once;
;; the template's own binders, made fresh, none of it.
(define-type exported (tupleof atms names))
(define exports-of (->* (levels) exported)
  (lambda (env) (exports-onto (normal env) nil nil)))
(define exports-onto (->* (levels atms names) exported)
  (lambda (ls as ns)
    (if (null? ls)
        (tuple as ns)
        (tagcase (car ls)
          (lv-rib (xs) (exports-onto (cdr ls) (atms-onto xs as) ns))
          (lv-cage (n) (exports-onto (cdr ls) as (if (name-in? n ns) ns (cons n ns))))))))
(define atms-onto (->* (atms atms) atms)
  (lambda (xs as)
    (cond ((null? xs) as)
          ((atm-in? (car xs) as) (atms-onto (cdr xs) as))
          (else (atms-onto (cdr xs) (cons (car xs) as))))))
(define exports=? (->* (exported exported) bool)
  (lambda (x y)
    (and (atms-within? (extract x 1) (extract y 1)) (atms-within? (extract y 1) (extract x 1))
         (names-within? (extract x 2) (extract y 2)) (names-within? (extract y 2) (extract x 2)))))
(define atms-within? (->* (atms atms) bool)
  (lambda (xs ys) (or (null? xs) (and (atm-in? (car xs) ys) (atms-within? (cdr xs) ys)))))
(define names-within? (->* (names names) bool)
  (lambda (xs ys) (or (null? xs) (and (name-in? (car xs) ys) (names-within? (cdr xs) ys)))))
;; An export's names, as said, in order (`shown_exports`).
(define shown-exports (->* (exported) string)
  (lambda (e)
    (let ((ss (sorted-strings (append (atm-strings (extract e 1)) (cage-strings (extract e 2)))
                              nil)))
      (if (null? ss) "nothing" (joined ss)))))
(define atm-strings (->* (atms) strings)
  (lambda (as)
    (if (null? as)
        nil
        (let ((rest (atm-strings (cdr as))))
          (tagcase (car as)
            (atm-var (n d) (cons (string-append "`" (symbol->string n) "`") rest))
            (atm-rib-of (n) (cons (string-append "what `" (symbol->string n) "` defines") rest))
            (atm-lit (t d) rest))))))
(define cage-strings (->* (names) strings)
  (lambda (ns)
    (if (null? ns)
        nil
        (cons (string-append "what `" (symbol->string (car ns)) "` defines")
              (cage-strings (cdr ns))))))
;; The names a template binds in its uses of macros that make definitions,
;; nodes `i` to `n`, each with the macro: what their signatures do not say
;; they define, it does not see (`macros.rs`'s `binders_under`).
(define-type nested (listof (tupleof symbol symbol) acyclic))
(define nested-binders (->* (int int pvars) nested)
  (lambda (i n ps) (nested-from i (- n 1) ps nil)))
;; Those of nodes `i` to `j`, before `out`: from the last back, so that
;; they are in the nodes' order.
(define nested-from (->* (int int pvars nested) nested)
  (lambda (i j ps out)
    (if (< j i)
        out
        (let* ((items (proper-items (node-syn j)))
               (h (if (and (not (null? items)) (syn-symbol? (car items))) (list (car items)) nil))
               (here (tagcase (node-kids j)
                       (k-form (x)
                         (if (and (not (null? h)) (not (pvar? (syn-symbol (car h)) ps))
                                  (makes-defns? (syn-symbol (car h))))
                             (binders-under x (syn-symbol (car h)))
                             nil))
                       (else y nil))))
          (nested-from i (- j 1) ps (append here out))))))
(define binders-under (->* (int symbol) nested)
  (lambda (at m)
    (tagcase (node-kids at)
      (k-pair (x y) (append (binders-under x m) (binders-under y m)))
      (k-form (x) (binders-under x m))
      (k-desc (xs) (binders-under-each xs m))
      (k-binder (n d) (if d (the nested nil) (the nested (list (tuple n m)))))
      (else y (the nested nil)))))
(define binders-under-each (->* ((listof int acyclic) symbol) nested)
  (lambda (xs m)
    (if (null? xs) nil (append (binders-under (car xs) m) (binders-under-each (cdr xs) m)))))
;; The macro whose use binds `n`, of `ns`, in a list of one.
(define nested-of (->* (symbol nested) (listof symbol acyclic))
  (lambda (n ns)
    (cond ((null? ns) nil)
          ((symbol=? n (extract (car ns) 1)) (list (extract (car ns) 2)))
          (else (nested-of n (cdr ns))))))
;; A name a nested use binds, `n`, which no binder of the template's binds
;; here (`b`), and the use is not said to define: refused, not read at the
;; top level, which the template would seem to mean by it.
(define unsaid-nested (->* (fails symbol (listof int acyclic) nested syn) unit)
  (lambda (fail n b nested s)
    (let ((m (nested-of n nested)))
      (if (and (null? b) (not (null? m)))
          (let ((n (symbol->string n)))
            (fail-at fail (string-append "`" n "` is bound in a use of `" (symbol->string (car m))
                                         "`, whose signature does not say its uses define it: "
                                         "say so (`(-> (export σ β) defn)`), or write `(with "
                                         "#%toplevel " n ")` for the top level's")
                     s))
          #u))))
