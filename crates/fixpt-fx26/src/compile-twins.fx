;;; The compiler written in FX-26: the twin phase
;;; (`docs/research/compiler-middle-phase.md`, step 4). A top-level form's
;;; words are all made first, by the stack compiler, each noting the twin to
;;; be made (`c-twins`, `c-standard-twins`), and its specialized copies, as
;;; the plan says (`c-make-copies`); then each twin, its register code, in
;;; order, by the register compiler (`r-register-code`, `r-standard-word`),
;;; which makes no word. As the Rust compiler's `form_twins`. After the
;;; register compiler, which the stack compiler no longer calls; before the
;;; program loop (`compile-programs.fx`), which calls this.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((compile-types (load-module "fx26:compile-types.fx"))
       (compile-exps-types (load-module "fx26:compile-exps-types.fx"))
       (compile-lift-types (load-module "fx26:compile-lift-types.fx"))
       (compile-plan-types (load-module "fx26:compile-plan-types.fx"))
       (regcode-entry-types (load-module "fx26:regcode-entry-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((compile (select compile-types compile-sig))
           (compile-exps (select compile-exps-types compile-exps-sig))
           (compile-plan (select compile-plan-types compile-plan-sig))
           (compile-lift (select compile-lift-types compile-lift-sig))
           (regcode-entry (select regcode-entry-types regcode-entry-sig)))
    (module

;; The types it uses of the files before it.
(define-effect c-emits (select compile-types c-emits))
(define-effect compiles (select compile-types compiles))
(define-type c-spec (select compile-exps-types c-spec))
(define-type c-twin (select compile-exps-types c-twin))
(define-type c-standard-twin (select compile-lift-types c-standard-twin))
;; What it uses of the modules it is given.
(define c-genv (with compile c-genv))
(define c-registers (with compile c-registers))
(define c-made-reuse (with compile-exps c-made-reuse))
(define c-own-now (with compile-exps c-own-now))
(define c-r-plan-ctx (with compile-exps c-r-plan-ctx))
(define c-spec-now (with compile-exps c-spec-now))
(define c-twins (with compile-exps c-twins))
(define c-make-copies (with compile-plan c-make-copies))
(define c-plan-copy-order (with compile-plan c-plan-copy-order))
(define c-planned-fv (with compile-lift c-planned-fv))
(define c-r-in-plan (with compile-lift c-r-in-plan))
(define c-standard-twins (with compile-lift c-standard-twins))
(define c-twin-depth (with compile-lift c-twin-depth))
(define r-register-code (with regcode-entry r-register-code))
(define r-standard-word (with regcode-entry r-standard-word))

;; `cells` as word `w`'s register twin, unless there are none.
(define c-twin! (subr c-emits (tword (listof wcell @k)) unit)
  (lambda (w cells) (if (null? cells) #u (begin (set-register-twin w cells) #u))))
;; Register code for twin `t`, made with the words its stack code made; a
;; copy's in its context.
(define c-make-twin (subr (maxeff compiles spin) (c-twin) unit)
  (lambda (t)
    (let ((w (extract t 1)) (ps (extract t 2)) (body (extract t 3)) (defining (extract t 6))
          (copy (extract t 8))
          (outer-spec (get c-spec-now)) (outer-genv (get c-genv)) (outer-ctx (get c-r-plan-ctx)))
      (begin
        (set c-own-now
             (if (null? defining)
                 (the (listof (productof (1 symbol) (2 tword)) @k) nil)
                 (cons (product (1 (car defining)) (2 w)) nil)))
        (if (null? copy)
            #u
            (begin (set c-spec-now (the (listof c-spec @k) (cons (extract (car copy) 1) nil)))
                   (set c-r-plan-ctx (cons (extract (car copy) 2) outer-ctx))
                   (set c-genv (extract (car copy) 3))))
        (let* ((outer-reuse (get c-made-reuse))
               (outer-in-plan (get c-r-in-plan))
               ;; A planned lambda, or a copy: the plan's.
               (in-plan (or (not (null? copy)) (not (null? (c-planned-fv ps body)))))
               (cells (begin (set c-made-reuse (extract t 7))
                             (set c-r-in-plan in-plan)
                             (set c-twin-depth (+ (get c-twin-depth) 1))
                             (r-register-code ps body (extract t 4) (extract t 5)))))
          (begin (set c-twin-depth (- (get c-twin-depth) 1))
                 (set c-r-in-plan outer-in-plan)
                 (set c-spec-now outer-spec) (set c-genv outer-genv) (set c-r-plan-ctx outer-ctx)
                 (set c-made-reuse outer-reuse) (c-twin! w cells)))))))
;; Each of `ts`, last first, made in order.
(define c-make-twins (subr (maxeff compiles spin) ((listof c-twin @k)) unit)
  (lambda (ts) (if (null? ts) #u (begin (c-make-twins (cdr ts)) (c-make-twin (car ts))))))
(define c-make-standard-twins (subr (maxeff compiles spin) ((listof c-standard-twin @k)) unit)
  (lambda (ts)
    (if (null? ts) #u (begin (c-make-standard-twins (cdr ts)) (c-make-standard-twin (car ts))))))

;; A typed call of `n` arguments: in tail position, a tail call.
;; Word `w`'s register code as standard operation `op` of `n` arguments has
;; it as a value.
(define c-make-standard-twin (subr (maxeff compiles spin) (c-standard-twin) unit)
  (lambda (t)
    (let ((cells (r-standard-word (extract t 2) (extract t 3))))
      (if (null? cells) #u (begin (set-register-twin (extract t 1) cells) #u)))))
;; The form's specialized copies, as its plan says, after its words; then
;; the twins of all of them, in order (step 4): register code, a phase after
;; the stack code, which makes no word. (The standard operations' after the
;; lambdas': no register code depends on another's.)
(define c-form-twins (subr (maxeff compiles spin) () unit)
  (lambda ()
    (begin
      (if (get c-registers) (c-make-copies (get c-plan-copy-order)) #u)
      (let ((ts (get c-twins)) (ss (get c-standard-twins)))
        (begin (set c-twins nil) (set c-standard-twins nil)
               (c-make-twins ts) (c-make-standard-twins ss)))))))))
