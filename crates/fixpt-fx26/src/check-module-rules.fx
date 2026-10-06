;;; The checker, in FX-26: first-class modules' rules
;;; (`docs/research/first-class-modules.md`, stage M2): `module` and `with`,
;;; module types compared, and what the termination check sees in them. The
;;; Rust checker's `modules.rs`, rule for rule; `check-modules.fx` reads and
;;; names. Part of the checker, `check-types.fx` first.

;;; ------------------------------------------------------------ module

;; `n`'s innermost binding, now of type `t`.
(define k-rebind-top (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (n t) (table-set! (get k-env) n (cons t (cdr (table-ref (get k-env) n nil))))))
;; What an error's message `m` is made into.
(define-type k-say (subr (maxeff checks spin) (string) string))
;; `f`'s value, or, if it fails, the error `say` makes of its message.
(define k-saying (subr (maxeff (read @globals) checks spin) (k-thunk k-say) k-te)
  (lambda (f say)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb) (k-fail (say m) ea eb))
        (k-ok (xs) (k-fail "k-ok inside" 0 0))))))
;; What `define*` says when `name`, found to be a `tf`, does not check at
;; it, as `m` says: the program's error, since only that check sees a call
;; of `name` as recursion.
(define k-star-mistake (subr (maxeff kreads (alloc @t) spin) (symbol int string) string)
  (lambda (name tf m)
    (k-cat5 (k-cat3 "`define*` found `" (symbol->string name) "` to be a ") (k-show-ty tf)
            ": " m "")))

;; What a module's items make, its abstract types, descriptions and values
;; (each newest first), and the effect of making them.
(define-type k-made (productof (1 k-parts) (2 k-parts) (3 k-parts) (4 k-eff)))
(define k-made-of (subr (alloc @t) (k-parts k-parts k-parts k-eff) k-made)
  (lambda (abs ds vs e) (product (1 abs) (2 ds) (3 vs) (4 e))))
;; The bindings of lambdas `ls`, and the types written, resolved.
(define-type k-mod-bound (productof (1 k-letrec-bs) (2 k-ids)))
;; Lambda `l`'s type `t`, resolved: a `define*`'s the type it is checked at
;; first, reading any global, or an error at its lambda if not a `subr`.
(define k-mod-first-type (subr (maxeff checks spin) (k-mlam int) int)
  (lambda (l t)
    (if (extract l 6)
        (let ((w (k-with-latent t (k-one (a-read (r-globals))))))
          (if (< w 0)
              (begin (k-fail-at "`define*` finds what a procedure reads: its type is a `subr`"
                                (extract l 3))
                     w)
              w))
        t)))
;; The bindings of lambdas `ls`, each type resolved at `a`..`b` in turn.
(define k-mod-bindings (subr (maxeff checks spin) (k-mlams int int) k-mod-bound)
  (lambda (ls a b)
    (if (null? ls)
        (product (1 (the k-letrec-bs nil)) (2 (the k-ids nil)))
        (let* ((t (k-resolve-selects (extract (car ls) 2) a b))
               (w (k-mod-first-type (car ls) t))
               (rest (k-mod-bindings (cdr ls) a b)))
          (product (1 (the k-letrec-bs (cons (product (1 (extract (car ls) 1)) (2 w)
                                                       (3 (extract (car ls) 3)))
                                              (extract rest 1))))
                   (2 (the k-ids (cons t (extract rest 2)))))))))
;; Each of `bs` bound, known, a definition's type named as a value's is.
(define k-mod-bind (subr (maxeff kstate spin) (k-letrec-bs k-mlams) unit)
  (lambda (bs ls)
    (if (null? bs)
        #u
        (let ((n (extract (car bs) 1)) (t (extract (car bs) 2)))
          (begin (k-bind n (if (extract (car ls) 5) t (k-name-nat n t)))
                 (k-note-known n 0)
                 (k-mod-bind (cdr bs) (cdr ls)))))))
;; Why each group found so far may not end ("" if it ends), by its first
;; member's name.
(define-type k-ends (listof (productof (1 symbol) (2 string)) acyclic))
(define k-ends-of (subr (read @globals) (k-ends symbol) k-ends)
  (lambda (ws n)
    (cond ((null? ws) nil)
          ((symbol=? (extract (car ws) 1) n) ws)
          (else (k-ends-of (cdr ws) n)))))
;; `ws` with why `group` may not end, found once for the group (the same
;; for each of its members).
(define k-ends-with (subr (maxeff kstate spin) (k-ends k-letrec-bs) k-ends)
  (lambda (ws group)
    (if (or (null? group) (not (null? (k-ends-of ws (extract (car group) 1)))))
        ws
        (the k-ends (cons (product (1 (extract (car group) 1)) (2 (k-termination group))) ws)))))
;; Why `group`, found in `ws`, may not end.
(define k-group-end (subr (read @globals) (k-ends k-letrec-bs) string)
  (lambda (ws group) (extract (car (k-ends-of ws (extract (car group) 1))) 2)))
;; A member of `group` other than `n`, in a list; none if there is none.
(define k-other-member (subr (read @globals) (k-letrec-bs symbol) k-letrec-bs)
  (lambda (group n)
    (cond ((null? group) nil)
          ((symbol=? (extract (car group) 1) n) (k-other-member (cdr group) n))
          (else group))))
;; An effect, and a type.
(define-type k-eff-ty (productof (1 k-eff) (2 int)))
;; The effect of checking each lambda of `bs` against its type, in the
;; scope of every item, with its recursive group (of `gs`, `k-mod-groups`)
;; checked to end, as a `define-rec`'s members are; `ws` why the groups so
;; far may not, `ds` the types written; and the bindings, a `define*`'s at
;; the type found.
(define-type k-mod-checked (productof (1 k-eff) (2 k-letrec-bs)))
;; The type `bs` gives `n`.
(define k-bs-type (subr (read @globals) (k-letrec-bs symbol) int)
  (lambda (bs n)
    (if (symbol=? (extract (car bs) 1) n) (extract (car bs) 2) (k-bs-type (cdr bs) n))))
;; Names `ns`, each at its type in `bs`, onto `out`.
(define k-bs-parts (subr (maxeff (read @globals) (alloc @t)) (k-names k-letrec-bs k-parts) k-parts)
  (lambda (ns bs out)
    (if (null? ns)
        out
        (let ((t (k-bs-type bs (car ns)))) (k-bs-parts (cdr ns) bs (k-part-onto (car ns) t out))))))
;; The module's values, in written order, onto `out` (newest first): a
;; lambda's at its type in `bs`, another's as made, in `vs`.
(define k-mod-vals (subr kbuilds (k-items k-parts k-letrec-bs k-parts) k-parts)
  (lambda (items vs bs out)
    (if (null? items)
        out
        (let* ((it (car items)) (k (extract it 1)) (ns (extract it 2))
               (more (cond ((k-lambda-item? it) (k-bs-parts ns bs out))
                           ((= k 2) (k-part-onto (car ns) (k-part-of vs (car ns)) out))
                           ((= k 3) (k-bs-parts ns bs out))
                           (else out))))
          (k-mod-vals (cdr items) vs bs more)))))
;; Each value's type, `vs`, mentions none of `inner`, the sizes and abstract
;; types named inside the module; or an error at `a`..`b`.
(define k-vals-known (subr (maxeff checks spin) (k-parts k-ids int int) unit)
  (lambda (vs inner a b)
    (if (null? vs)
        #u
        (let ((v (k-first-mentioned (extract (car vs) 2) inner)))
          (if (< v 0)
              (k-vals-known (cdr vs) inner a b)
              (k-fail (k-cat5 "`" (symbol->string (extract (car vs) 1)) "`'s type mentions `"
                              (k-dvar-string v) "`, which is not known outside the module")
                      a b))))))

;;; ------------------------------------------------------------ with

;; The names of parts `ps`.
(define k-comp-names (subr (maxeff (read @globals) (alloc @t)) (k-parts) k-names)
  (lambda (ps) (if (null? ps) nil (cons (extract (car ps) 1) (k-comp-names (cdr ps))))))
;; Each of `ps` bound, the first first.
(define k-bind-parts (subr (maxeff kstate spin) (k-parts) unit)
  (lambda (ps)
    (if (null? ps)
        #u
        (begin (k-bind (extract (car ps) 1) (extract (car ps) 2)) (k-bind-parts (cdr ps))))))


;;; ------------------------------------------------------------ subtyping


