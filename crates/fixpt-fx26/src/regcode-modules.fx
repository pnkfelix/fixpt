;;; Register code, in FX-26: modules (`docs/research/first-class-modules.md`,
;;; stage M3), as the Rust compiler's `r_module` and `r_with` make them.
;;; After `regcode-core.fx`, which reaches them through `r-module-code`.

;; Where names are, to register code and to the cellular compiler.
(define-type r-scopes (pairof renv cenv @k))

;; RESULT kept in a new frame slot, there for `n` in `sc`: the slot, and
;; the scopes with it.
(define-type r-kept (pairof int r-scopes @k))
(define r-keep-named (subr rcompiles (rgen symbol r-scopes) r-kept)
  (lambda (g n sc)
    (let* ((s (r-keep-in-slot g))
           (inner (the r-scopes (cons (r-bind n (rl-slot s) (car sc)) (r-local (cdr sc) n)))))
      (the r-kept (cons s inner)))))
;; `vals`, newest first, onto `acc` the oldest first: as operands.
(define r-slots-oldest (subr rbuilds (rints rargs) rargs)
  (lambda (vals acc)
    (if (null? vals) acc (r-slots-oldest (cdr vals) (the rargs (cons (a-slot (car vals)) acc))))))
;; `ss` onto `vals`, newest first.
(define r-slots-onto (subr rbuilds (rints rints) rints)
  (lambda (ss vals) (if (null? ss) vals (r-slots-onto (cdr ss) (the rints (cons (car ss) vals))))))

;; A module's items kept in frame slots in order, `vals` the values' slots
;; so far (newest first): all of them. A `define-rec`'s closures are made as
;; a `letrec`'s are, with no join points.
(define r-module-items (subr rcompiles (rgen mod-items r-scopes rints) rints)
  (lambda (g items sc vals)
    (if (null? items)
        vals
        (let* ((it (car items)) (k (extract it 1)) (ns (extract it 2)) (xs (extract it 4)))
          (cond
            ((= k 1) (r-module-items g (cdr items) sc vals))
            ((= k 0)
             (let* ((up (begin (r-exp g (car xs) (car sc) (cdr sc) #f)
                               (r-keep-named g (c-converter "up-" (car ns)) sc)))
                    (sc1 (cdr up))
                    (down (begin (r-exp g (car (cdr xs)) (car sc1) (cdr sc1) #f)
                                 (r-keep-named g (c-converter "down-" (car ns)) sc1))))
               (r-module-items g (cdr items) (cdr down) vals)))
            ((= k 2)
             (let ((kept (begin (r-exp g (car xs) (car sc) (cdr sc) #f)
                                (r-keep-named g (car ns) sc))))
               (r-module-items g (cdr items) (cdr kept) (the rints (cons (car kept) vals)))))
            (else
             (let* ((bs (c-rec-of ns (extract it 3) xs))
                    (joins (r-repeat #f (c-count-letrec bs) nil))
                    (at (r-letrec-slots-j g joins))
                    (patches (r-letrec-make g bs bs at 0 (car sc) (cdr sc) joins))
                    (patched (r-letrec-patch g patches at))
                    (env2 (r-letrec-env bs at (car sc)))
                    (inner (the r-scopes (cons env2 (r-letrec-te bs (cdr sc))))))
               (r-module-items g (cdr items) inner (r-slots-onto at vals)))))))))
;; A module: its items kept in frame slots in order, as its stack code keeps
;; them; then the product of its values. Declined in a leaf.
(define r-module (subr rcompiles (rgen mod-items renv cenv bool) unit)
  (lambda (g items env te tail)
    (if (extract g leaf)
        (r-decline)
        (let* ((slots (get (extract g nslot)))
               (vals (r-module-items g items (the r-scopes (cons env te)) nil)))
          (begin (r-make-frozen g 37 (r-slots-oldest vals nil) env te)
                 (set (extract g nslot) slots)
                 (r-done g tail))))))

;; Module `m`'s value into RESULT, from where `env` has it; declined if it
;; is not in a place.
(define r-module-value (subr rcompiles (rgen symbol renv) unit)
  (lambda (g m env)
    (let ((l (r-where env m)))
      (if (null? l)
          (r-decline)
          (tagcase (car l)
            (rl-reg (k) (r-opn g rop-reg k))
            (rl-slot (s) (r-opn g rop-stack s))
            (rl-free (i) (r-opn g rop-lexical i))
            (rl-global (c) (r-op1 g rop-global (wcell-global c)))
            (else y (r-decline)))))))
;; Module `m`'s values `ns`, by position from field `i`, each into its slot
;; of `at`: the scopes with them.
(define r-with-fields (subr rcompiles (rgen symbol syms rints int r-scopes) r-scopes)
  (lambda (g m ns at i sc)
    (if (null? ns)
        sc
        (begin
          (r-module-value g m (car sc))
          (r-opn g rop-field (+ i 2))
          (r-opn g rop-setstk (car at))
          (let ((inner (the r-scopes (cons (r-bind (car ns) (rl-slot (car at)) (car sc))
                                           (r-local (cdr sc) (car ns))))))
            (r-with-fields g m (cdr ns) (cdr at) (+ i 1) inner))))))
;; A frame slot for each of `ns`.
(define r-slots-for (subr (maxeff emits spin) (rgen syms) rints)
  (lambda (g ns)
    (if (null? ns) nil (let ((s (r-slot g))) (the rints (cons s (r-slots-for g (cdr ns))))))))
;; `with`: the module's values, by position, kept in frame slots; then the
;; body. Declined in a leaf.
(define r-with (subr rcompiles (rgen symbol exp int int renv cenv bool) unit)
  (lambda (g m body a b env te tail)
    (let ((ns (c-with-at a b)))
      (if (or (extract g leaf) (null? ns))
          (r-decline)
          (let* ((slots (get (extract g nslot)))
                 (at (r-slots-for g (car ns)))
                 (sc (r-with-fields g m (car ns) at 0 (the r-scopes (cons env te)))))
            (begin (r-exp g body (car sc) (cdr sc) tail) (set (extract g nslot) slots)))))))

(define r-module-or-with (subr rcompiles (rgen exp renv cenv bool) unit)
  (lambda (g x env te tail)
    (tagcase x
      (e-module (items a b) (r-module g items env te tail))
      (e-with (m body a b) (r-with g m body a b env te tail))
      (else y (r-decline)))))
(set r-module-code r-module-or-with)
