;;; The checker, in FX-26: the rules for processes and `par` (`docs/fx26.md`,
;;; "Processes"), the Rust checker's `processes.rs`, rule for rule and in
;;; its words. The forms call the scheduler's procedures (`fx26:processes.fx`)
;;; through the hidden global of its load (`k-library-type`); a process's
;;; body must be transmissible, and do nothing outside it but what a process
;;; may (`k-spawn-te`); `par`'s branches must not interfere (`k-par-te`);
;;; `race`'s must be cancellable (`k-race-te`).
;;; Also `(with #%fx n)`'s rule, out of the rules' recursive group.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-binders-types (load-module "fx26:check-binders-types.fx"))
       (check-data-types (load-module "fx26:check-data-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-calls-types (load-module "fx26:check-calls-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-synth-types (load-module "fx26:check-synth-types.fx"))
       (check-subtype-types (load-module "fx26:check-subtype-types.fx"))
       (check-module-rules-types (load-module "fx26:check-module-rules-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-env (select check-env-types check-env-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (check-binders (select check-binders-types check-binders-sig))
           (check-data (select check-data-types check-data-sig))
           (check-print (select check-print-types check-print-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig))
           (check-calls (select check-calls-types check-calls-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-synth (select check-synth-types check-synth-sig))
           (check-subtype (select check-subtype-types check-subtype-sig))
           (check-module-rules (select check-module-rules-types check-module-rules-sig)))
    (module

;; The types it uses of the files before it.
(hide (include check-types-types) (include check-env-types))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-env) (include check-print) (include check-print-parts)
      (include check-calls) (include check-effects) (include check-subtype))
(define k-start (with check-resolve k-start))
(define k-end (with check-resolve k-end))
(define k-free-vars (with check-resolve k-free-vars))
(define k-regions-distinct? (with check-binders k-regions-distinct?))
(define k-with-used (with check-synth k-with-used))
(define k-comp-names (with check-module-rules k-comp-names))

;; The generative types of processes, and what may be sent to one
;; (`check-data.fx`).
(define k-addr-index (with check-data k-addr-index))
(define k-inbox-index (with check-data k-inbox-index))
(define k-untransmissible (with check-data k-untransmissible))
(define k-crossing-atom? (with check-data k-crossing-atom?))

;;; ------------------------------------------------------------ the library

;; `(with m n)` where `m` is the hidden global of the scheduler's load
;; (`fx26:processes.fx`) and `n` names one of its procedures: the type the
;; forms of processes and `par` give it, the standard `%processes:n`'s;
;; -1 otherwise (the Rust checker's `library_type`).
(define k-library-type (subr (maxeff kreads spin) (symbol kx) int)
  (lambda (m body)
    (if (symbol=? m '%shared:fx26:processes.fx)
        (tagcase body
          (x-var (n c d)
            (k-std-type (string->symbol (string-append "%processes:" (symbol->string n)))))
          (else y -1))
        -1)))
;; The procedure of the scheduler's that operator `f` names, given `args`
;; as its forms give them: `spawn-process` of one, `par2` of two; else "".
(define k-library-op (subr (maxeff kreads spin) (kx kxs) string)
  (lambda (f args)
    (tagcase f
      (x-with (m body a b)
        (if (< (k-library-type m body) 0)
            ""
            (tagcase body
              (x-var (n c d)
                (let ((s (symbol->string n)) (k (k-length args)))
                  (cond ((and (string=? s "spawn-process") (= k 1)) s)
                        ((and (string=? s "par2") (= k 2)) s)
                        ((and (string=? s "race2") (= k 2)) s)
                        (else ""))))
              (else y ""))))
      (else y ""))))
;; `(with m n)` of the library, its type `lt`: the member noted for the
;; compilers, as an ordinary `with`'s is; reading the global no effect.
(define k-library-with (subr (maxeff checks spin) (int kx int int int) k-te)
  (lambda (mt body lt a b)
    (tagcase (k-get mt)
      (ty-module (abs ds vs)
        (let ((used (k-with-used vs (k-free-vars body) 0)))
          (begin
            (k-note-with (product (1 a) (2 b) (3 (k-comp-names (extract used 1)))
                                  (4 (extract used 2))))
            (k-te lt nil))))
      (else y (k-te lt nil)))))

;;; ------------------------------------------------------------ spawn and par

;; What synthesizes an expression's type and effect: the rules' `k-synth`.
(define-type k-synth-fn (subr (maxeff checks spin) (kx) k-te))
;; `((with … spawn-process) body)`, `body` a `plambda` of one place over a
;; `lambda` of two parameters, synthesized by `synth`, as the operator `f`
;; is: the process's address, and the spawn's effect (the Rust checker's
;; `synth_spawn`).
(define k-spawn-te (subr (maxeff checks spin) (kx kx kxs int k-synth-fn) k-te)
  (lambda (x f args expected synth)
    (let* ((noted (synth f)) (body (car args)) (pt (synth body)) (a (k-start x)) (b (k-end x))
           (usage "a process's body is `(spawn (mailbox message-type place) body …)`")
           (parts (k-spawn-parts body pt)))
      (if (null? parts)
          (k-fail usage a b)
          (let* ((p (car parts)) (r (extract p 1)) (e (extract p 2)) (msg (extract p 3)))
            (begin
              (k-spawn-holds (k-free-vars body) a b)
              (let ((why (k-untransmissible msg nil nil)))
                (if (string=? why "")
                    #u
                    (k-fail (k-copied-why msg why) a b)))
              (let* ((seen (k-without-region e (r-var r)))
                     (bad (k-not-crossing seen)))
                (if (null? bad)
                    (let* ((io (k-has-io? seen))
                           (seen (if io (k-insert (a-nondet) seen) seen))
                           (at (k-address-region msg expected))
                           (addr (k-ty-new (ty-named k-addr-index (list (dt msg) (dr at))))))
                      (k-te addr (k-insert (a-alloc at) seen)))
                    (k-fail (k-cat3 k-shares-nothing "its body has "
                                    (string-append (k-show-effect bad) ", on a region outside it"))
                            a b)))))))))
;; What a process's body must not do, as said when it does.
(define k-shares-nothing string "a process may share nothing that can be written, and ")
;; That a process's messages, of type `msg`, must be transmissible, and why
;; they are not.
(define k-copied-why (subr (maxeff kstate spin) (int string) string)
  (lambda (msg why)
    (k-cat5 "a process's messages are copied to it, so they must be transmissible, "
            "and a " (k-show-ty msg) " is not: " why)))
;; The place binder, the latent effect and the message type of a process's
;; body of type `pt`, in a list of one; none if it is not one.
(define k-spawn-parts (subr (maxeff checks spin) (kx k-te)
                            (listof (productof (1 int) (2 k-eff) (3 int)) acyclic))
  (lambda (body pt)
    (tagcase body
      (x-plambda (bs lam a b)
        (if (and (= (k-length bs) 1) (= (extract (car bs) 2) 3)
                 (tagcase lam (x-lambda (ps l c d) (= (k-length ps) 2)) (else y #f)))
            (let ((r (extract (car bs) 1)))
              (tagcase (k-get (extract pt 1))
                (ty-poly (pbs inner)
                  (tagcase (k-get inner)
                    (ty-subr (e ps res cv)
                      (tagcase (k-get (car ps))
                        (ty-named (w ds)
                          (if (and (= w k-inbox-index) (= (k-length ds) 2)
                                   (tagcase (car (cdr ds))
                                     (dr (q) (k-region=? q (r-var r)))
                                     (else y #f)))
                              (tagcase (car ds)
                                (dt (m) (list (product (1 r) (2 e) (3 m))))
                                (else y nil))
                              nil))
                        (else y nil)))
                    (else y nil)))
                (else y nil)))
            nil))
      (else y nil))))
;; Each free variable of a process's body, globals too, but the standard
;; bindings and the hidden globals of loads, transmissible.
(define k-spawn-holds (subr (maxeff checks spin) (k-names int int) unit)
  (lambda (vs a b)
    (if (null? vs)
        #u
        (let* ((v (car vs)) (t (k-lookup v)))
          (begin
            (if (or (< t 0) (= t (k-std-type v)) (k-shared-name? v))
                #u
                (let ((why (k-untransmissible t nil nil)))
                  (if (string=? why "") #u (k-fail (k-holds-why v why) a b))))
            (k-spawn-holds (cdr vs) a b))))))
;; That a process's body holds `v`, which it may not, and why.
(define k-holds-why (subr (maxeff kstate spin) (symbol string) string)
  (lambda (v why) (k-cat5 k-shares-nothing "its body holds `" (symbol->string v) "`: " why)))
;; `e` without its atoms on region `r`.
(define k-without-region (subr (maxeff kstate spin) (k-eff k-region) k-eff)
  (lambda (e r)
    (cond ((null? e) nil)
          ((and (k-has-region? (car e)) (k-region=? (k-atom-region (car e)) r))
           (k-without-region (cdr e) r))
          (else (cons (car e) (k-without-region (cdr e) r))))))
;; The first atom of `e` a process may not have, alone; none if none.
(define k-not-crossing (subr (maxeff kstate spin) (k-eff) k-eff)
  (lambda (e)
    (cond ((null? e) nil)
          ((k-crossing-atom? (car e)) (k-not-crossing (cdr e)))
          (else (k-one (car e))))))
(define k-has-io? (subr (read @globals) (k-eff) bool)
  (lambda (e)
    (and (not (null? e)) (or (tagcase (car e) (a-io (k) #t) (else y #f)) (k-has-io? (cdr e))))))
;; The region of an address of messages `msg`: as `expected` says, if it is
;; one of the same messages; else one of its own.
(define k-address-region (subr (maxeff checks spin) (int int) k-region)
  (lambda (msg expected)
    (let ((given (if (< expected 0)
                     nil
                     (tagcase (k-get expected)
                       (ty-named (w ds)
                         (if (and (= w k-addr-index) (= (k-length ds) 2))
                             (tagcase (car ds)
                               (dt (m)
                                 (tagcase (car (cdr ds))
                                   (dr (q) (if (and (k-subtype msg m) (k-subtype m msg))
                                               (the k-regions (list q))
                                               nil))
                                   (else y nil)))
                               (else y nil))
                             nil))
                       (else y nil)))))
      (if (null? given) (k-fresh-region "@process") (car given)))))

;; `((with … par2) f g)`, operator `op`, `f` and `g` thunks, synthesized by
;; `synth`: both their values, `(productof (1 A) (2 B))`, and every effect,
;; if neither transfers control out of its branch and the two do not
;; interfere (the Rust checker's `synth_par`).
(define k-par-te (subr (maxeff checks spin) (kx kx kxs k-synth-fn) k-te)
  (lambda (x op args synth)
    (let* ((noted (synth op)) (ft (synth (car args))) (gt (synth (car (cdr args))))
           (usage "`(par ((name expression) …) body …)`") (a (k-start x)) (b (k-end x)))
      (tagcase (k-get (extract ft 1))
        (ty-subr (e1 ps1 r1 c1)
          (tagcase (k-get (extract gt 1))
            (ty-subr (e2 ps2 r2 c2)
              (if (or (not (null? ps1)) (not (null? ps2)))
                  (k-fail usage a b)
                  (begin
                    (k-par-ends (car args) e1)
                    (k-par-ends (car (cdr args)) e2)
                    (let ((clash (k-interference e1 e2)))
                      (if (null? clash)
                          (k-te (k-pair-type r1 r2)
                                (k-union (k-union (extract ft 2) (extract gt 2)) (k-union e1 e2)))
                          (k-fail (k-cat5 "`par`'s branches interfere: one has "
                                          (k-show-effect (k-one (extract (car clash) 1)))
                                          " and another "
                                          (k-show-effect (k-one (extract (car clash) 2)))
                                          ", so the answer could depend on which runs first")
                                  a b))))))
            (else y (k-fail usage a b))))
        (else y (k-fail usage a b))))))
;; `par2`'s or `race2`'s rule, as `lop` says (`k-library-op`), of `x`.
(define k-branches-te (subr (maxeff checks spin) (string kx kx kxs k-synth-fn) k-te)
  (lambda (lop x op args synth)
    (if (string=? lop "par2") (k-par-te x op args synth) (k-race-te x op args synth))))
;; `((with … race2) f g)`, operator `op`, `f` and `g` thunks, synthesized
;; by `synth`: a branch's value, both of one type, and every effect and
;; `nondet`, if each branch is cancellable and the two do not interfere
;; (the Rust checker's `synth_race`).
(define k-race-te (subr (maxeff checks spin) (kx kx kxs k-synth-fn) k-te)
  (lambda (x op args synth)
    (let* ((noted (synth op)) (ft (synth (car args))) (gt (synth (car (cdr args))))
           (usage "`(race expression expression …)`") (a (k-start x)) (b (k-end x)))
      (tagcase (k-get (extract ft 1))
        (ty-subr (e1 ps1 r1 c1)
          (tagcase (k-get (extract gt 1))
            (ty-subr (e2 ps2 r2 c2)
              (if (or (not (null? ps1)) (not (null? ps2)))
                  (k-fail usage a b)
                  (begin
                    (k-race-cancellable (car args) e1)
                    (k-race-cancellable (car (cdr args)) e2)
                    (let ((clash (k-interference e1 e2)))
                      (if (null? clash)
                          (k-te (k-race-type r1 r2 a b)
                                (k-union (k-union (k-union (extract ft 2) (extract gt 2))
                                                  (k-union e1 e2))
                                         (k-one (a-nondet))))
                          (k-fail (k-cat5 "`race`'s branches interfere: one has "
                                          (k-show-effect (k-one (extract (car clash) 1)))
                                          " and another "
                                          (k-show-effect (k-one (extract (car clash) 2)))
                                          "")
                                  a b))))))
            (else y (k-fail usage a b))))
        (else y (k-fail usage a b))))))
;; A `race` branch, of effect `e`, that does nothing another could see.
(define k-race-cancellable (subr (maxeff checks spin) (kx k-eff) unit)
  (lambda (branch e)
    (cond ((null? e) #u)
          ((tagcase (car e)
             (a-write (r) #t) (a-init (r) #t) (a-send (r) #t) (a-io (k) #t) (a-goto (r) #t)
             (a-comefrom (r) #t) (a-var (v) #t) (a-app (v ds) #t) (else y #f))
           (k-fail (string-append k-race-unseen (k-show-effect (k-one (car e))))
                   (k-start branch) (k-end branch)))
          (else (k-race-cancellable branch (cdr e))))))
;; What a `race` branch that could be seen is told, before its effect.
(define k-race-unseen string
  (string-append "a `race` branch may be stopped half way, so it must do nothing another "
                 "could see, and this one has "))
;; The one type of `race`'s branches, `ra` and `rb`: the wider.
(define k-race-type (subr (maxeff checks spin) (int int int int) int)
  (lambda (ra rb a b)
    (cond ((k-subtype rb ra) ra)
          ((k-subtype ra rb) rb)
          (else (k-fail (k-cat5 "`race`'s branches give values of two types, " (k-show-ty ra)
                                " and " (k-show-ty rb) "")
                        a b)))))
;; `(productof (1 a) (2 b))`.
(define k-pair-type (subr (maxeff kstate spin) (int int) int)
  (lambda (a b)
    (let ((one (product (1 (string->symbol "1")) (2 a)))
          (two (product (1 (string->symbol "2")) (2 b))))
      (k-ty-new (ty-product (list one two))))))
;; A branch, of effect `e`, that transfers no control out of itself.
(define k-par-ends (subr (maxeff checks spin) (kx k-eff) unit)
  (lambda (branch e)
    (cond ((null? e) #u)
          ((tagcase (car e) (a-goto (r) #t) (a-comefrom (r) #t) (else y #f))
           (k-fail (string-append "a `par` branch must end where it began, and this one has "
                                  (k-show-effect (k-one (car e))))
                   (k-start branch) (k-end branch)))
          (else (k-par-ends branch (cdr e))))))

;; The first pair of atoms, one of each effect, that interfere, in a list of
;; one; none if none (the Rust checker's `interference`).
(define k-interference (subr (maxeff kstate spin) (k-eff k-eff)
                             (listof (productof (1 k-atom) (2 k-atom)) acyclic))
  (lambda (x y)
    (if (null? x)
        nil
        (let ((hit (k-interferes-any (car x) y)))
          (if (null? hit)
              (k-interference (cdr x) y)
              (list (product (1 (car x)) (2 (car hit)))))))))
(define k-interferes-any (subr (maxeff kstate spin) (k-atom k-eff) k-eff)
  (lambda (a y)
    (cond ((null? y) nil)
          ((or (k-interferes? a (car y)) (k-interferes? (car y) a)) (k-one (car y)))
          (else (k-interferes-any a (cdr y))))))
;; Whether `a` interferes with `b`, one way: a write against a read, a
;; write, a fill or an await; a fill against a write; a send against a
;; send, a receive against a send or a receive, on regions that may be one;
;; any two I/O effects; an unknown effect against anything but an
;; allocation, `spin` and `nondet`.
(define k-interferes? (subr (maxeff kstate spin) (k-atom k-atom) bool)
  (lambda (a b)
    (let ((one (lambda ((p k-region) (q k-region)) (not (k-regions-distinct? p q))))
          (rb (k-atom-region b)))
      (tagcase a
        (a-var (v) (not (k-harmless? b)))
        (a-app (v ds) (not (k-harmless? b)))
        (a-write (p)
          (tagcase b
            (a-read (q) (one p q)) (a-write (q) (one p q)) (a-init (q) (one p q))
            (a-await (q) (one p q)) (else y #f)))
        (a-init (p) (tagcase b (a-write (q) (one p q)) (else y #f)))
        (a-send (p) (tagcase b (a-send (q) (one p q)) (else y #f)))
        (a-receive (p) (tagcase b (a-send (q) (one p q)) (a-receive (q) (one p q)) (else y #f)))
        (a-io (k) (tagcase b (a-io (j) #t) (else y #f)))
        (else y #f)))))
(define k-harmless? (subr pure (k-atom) bool)
  (lambda (a) (tagcase a (a-alloc (r) #t) (a-spin () #t) (a-nondet () #t) (else y #f))))

;;; ------------------------------------------------------------ #%fx

;; `(with #%fx n)`: the standard `n`'s type, whatever binds `n` since.
(define k-synth-fx (subr (maxeff checks spin) (kx int kx int int) k-te)
  (lambda (x mt body a b)
    (cond ((>= mt 0)
           (k-fail "`#%fx` is the standard bindings' module, which nothing else may be" a b))
          (else
           (let ((t (tagcase body
                      (x-var (n c d)
                        (if (and (k-second-class? n) (not (k-operator? n a b)))
                            (k-fail (k-named-only n) a b)
                            (k-std-type n)))
                      (else y -1))))
             (if (< t 0)
                 (k-fail "`(with #%fx name)` names one standard binding" a b)
                 (begin (if (k-operator? (k-fx-name body) a b) #u (k-note-fx-plain body a b))
                        (k-te t nil))))))))
;; The operator `(with #%fx n)`, noted as `k-note-fx-plain` notes it, once.
(define k-note-fx-plain-op (subr (maxeff checks spin) (kx) unit)
  (lambda (f)
    (tagcase f
      (x-with (m body a b) (if (k-fx-module? m) (k-note-fx-plain body a b) #u))
      (else y #u))))
;; Where nothing shadows `n`, `(with #%fx n)` is the plain `n`: the fact
;; -502, for the compiler (the Rust checker's `fx_plain`).
(define k-note-fx-plain (subr (maxeff checks spin) (kx int int) unit)
  (lambda (body a b)
    (if (string=? (k-std-op body) "")
        #u
        (set k-extracts (cons (product (1 a) (2 b) (3 -502)) (get k-extracts)))))))))
