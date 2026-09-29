;;; Register code, in FX-26: specialized procedures' temporaries, and the
;;; entry. After `regcode-core.fx`.

;; Each argument into a frame slot of its own, in order: the slots.
(define r-spec-temps (subr (maxeff compiles spin) (rgen (listof exp acyclic) renv cenv) (listof int @k))
  (lambda (g args env te)
    (if (null? args)
        nil
        (let* ((s (begin (r-exp g (car args) env te #f) (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) s))))
               (rest (r-spec-temps g (cdr args) env te)))
          (cons s rest)))))

;;; ------------------------------------------------------------ the entry

;; The register environment of a lambda's body, from its cellular one: its
;; parameters in registers in a leaf, else in the frame.
(define r-env-of (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (cenv bool) renv)
  (lambda (inner leaf)
    (if (null? inner)
        nil
        (let ((rest (r-env-of (cdr inner) leaf)) (n (car (car inner))))
          (tagcase (cdr (car inner))
            (at-slot (i) (the renv (cons (cons n (if leaf (rl-reg (+ i 1)) (rl-slot i))) rest)))
            (at-free (i) (the renv (cons (cons n (rl-free i)) rest)))
            (at-loop (z) (the renv (cons (cons n (rl-loop)) rest)))
            (at-global (g) (the renv (cons (cons n (rl-global g)) rest)))
            (at-pending (s) (begin (r-decline) rest))
            (at-lifted (k) (the renv (cons (cons n (rl-lifted k)) rest))))))))

(define r-store-params (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (rgen int int) unit)
  (lambda (g i n)
    (cond ((= i n) #u)
          ((or (<= n register-regs) (< (+ i 1) register-regs))
           (let ((s (r-slot g))) (begin (r-opnn g rop-store (+ i 1) s) (r-store-params g (+ i 1) n))))
          (else
           (let ((s (r-slot g)))
             (begin
               (r-opn g rop-reg register-regs)
               (r-opn g rop-op1 routine-pair-car)
               (r-opn g rop-setstk s)
               (if (< (+ i 1) n)
                   (begin (r-opn g rop-reg register-regs) (r-opn g rop-op1 routine-pair-cdr) (r-opn g rop-setreg register-regs))
                   #u)
               (r-store-params g (+ i 1) n)))))))

;; Whether a fast version may be worth compiling, asked before it is, as the
;; Rust compiler's `r_fast_may_pay` says: whether, with inlined calls no
;; calls, the body would be a leaf; or it mentions its own name, and so may
;; loop.
(define r-fast-may-pay?
  (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syns-a)) acyclic) exp cenv (listof c-this @k) (listof (productof (1 symbol) (2 tword)) @k)) bool)
  (lambda (ps body inner this own)
    (or (and (not (null? own)) (c-mentions? body (extract (car own) 1)))
        (let ((outer-assuming (get r-assuming)) (outer-name (get r-own-name)))
          (begin
            (set r-assuming #t)
            (set r-own-name (if (null? own) (the (listof (pairof symbol int @k) @k) nil) (cons (the (pairof symbol int @k) (cons (extract (car own) 1) (c-count-params ps))) nil)))
            (let ((leaf (not (r-collects body inner this #t))))
              (begin (set r-assuming outer-assuming) (set r-own-name outer-name) leaf)))))))
;; A lambda's body in register code, not yet assembled, in a list; none where
;; this compiler declines. In a fast version, where a call inlined or of
;; itself in tail position is no call, a leaf maybe where the plain one is
;; not.
(define r-register-body
  (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syns-a)) acyclic) exp cenv (listof c-this @k) (listof (productof (1 symbol) (2 tword)) @k)) (listof rgen @k))
  (lambda (ps body inner this own)
    (let ((n (c-count-params ps)))
      (begin
        (set r-declined #f)
        (set r-looped #f)
        (set r-spec-at (the (listof rloc @k) nil))
        (set r-own-now (the (listof (productof (1 symbol) (2 tword) (3 int) (4 int)) @k) nil))
        (set r-own-name (if (null? own) (the (listof (pairof symbol int @k) @k) nil) (cons (the (pairof symbol int @k) (cons (extract (car own) 1) n)) nil)))
        ;; Past `register-regs` parameters, the rest come as a list in the
        ;; last register, taken apart into the frame.
        (let* ((leaf (and (<= n register-regs) (not (r-collects body inner this #t))))
               (g (the rgen
                    (product (items (new (the (listof ritem @k) nil))) (leaf leaf) (nreg (new 0)) (nslot (new 0))
                             (mslot (new 0)) (labels (new (+ (if (null? this) 0 1) (+ (if (null? (get c-spec-now)) 0 1) (if (null? own) 0 1)))))
                             (this this) (start 0)))))
          (begin
                (r-opn g rop-args n)
                (let ((env (r-env-of inner leaf)))
                  (begin
                    (if leaf
                        (set (extract g nreg) n)
                        (begin (r-op0 g rop-save) (r-emit g (r-frame)) (r-store-params g 0 n)))
                    (if (null? this) #u (r-emit g (r-label 0)))
                    ;; A procedure specialized at a lambda: where the
                    ;; parameter is, and a label at the start.
                    (if (null? (get c-spec-now))
                        #u
                        (let ((l (r-where env (extract (car (get c-spec-now)) 5))) (start (if (null? this) 0 1)))
                          (if (null? l)
                              (r-decline)
                              (begin (set r-spec-at (the (listof rloc @k) (cons (car l) nil)))
                                     (set r-spec-start start)
                                     (r-emit g (r-label start))))))
                    ;; A top-level definition's procedure: a label at the
                    ;; start, for its calls of itself.
                    (if (null? own)
                        #u
                        (let ((start (+ (if (null? this) 0 1) (if (null? (get c-spec-now)) 0 1))))
                          (begin (set r-own-now (cons (product (1 (extract (car own) 1)) (2 (extract (car own) 2)) (3 n) (4 start)) nil))
                                 (r-emit g (r-label start)))))
                    (r-exp g body env inner #t)
                    (if (get r-declined) (the (listof rgen @k) nil) (the (listof rgen @k) (cons g nil)))))))))))
;; The body compiled once, as ever.
(define r-plain-code
  (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syns-a)) acyclic) exp cenv (listof c-this @k) (listof (productof (1 symbol) (2 tword)) @k)) (listof wcell @k))
  (lambda (ps body inner this own)
    (let ((g (r-register-body ps body inner this own)))
      (if (null? g) (the (listof wcell @k) nil) (r-assemble (car g))))))
;; The two versions as one: `args n`, the guards, the fast body, the plain
;; one; both with the larger frame.
(define r-versions (subr (maxeff compiles spin) (rgen rgen r-assumptions) (listof wcell @k))
  (lambda (fast plain assumptions)
    (let ((frame (if (> (get (extract fast mslot)) (get (extract plain mslot))) (get (extract fast mslot)) (get (extract plain mslot)))))
      (begin
        (set (extract fast mslot) frame)
        (set (extract plain mslot) frame)
        (let* ((fc (r-assemble fast)) (pc (r-assemble plain))
               (plain-at (+ 2 (+ (* 4 (r-assumptions-length assumptions 0)) (- (r-cells-length fc 0) 2))))
               (bodies (r-rev-cells (r-rev-cells (cdr (cdr fc)) nil) (cdr (cdr pc)))))
          (cons (car fc) (cons (car (cdr fc)) (r-guard-cells assumptions 2 plain-at bodies))))))))
;; Register code for a standard operation as a value (`c-standard-value`),
;; as the Rust compiler's `r_standard_word`: its operands are its
;; parameters, in REG1…REGn already, and a call-out, if it is one, is made in
;; a frame. None for one done in several instructions, or that takes
;; control (the closure then has stack code only).
(define r-standard-word (subr (maxeff compiles spin) (string int) (listof wcell @k))
  (lambda (name n)
    (let* ((std (r-standard name n))
           (callout (tagcase std (s-prim (p) #t) (s-cellular (r) (= r routine-cons)) (else y #f)))
           (g (the rgen
                (product (items (new (the (listof ritem @k) nil))) (leaf (not callout)) (nreg (new n)) (nslot (new 0))
                         (mslot (new 0)) (labels (new 0)) (this (the (listof c-this @k) nil)) (start 0))))
           (none (the (listof wcell @k) nil)))
      (begin
        (r-opn g rop-args n)
        (if callout (begin (r-op0 g rop-save) (r-emit g (r-frame))) #u)
        (let ((made
               (tagcase std
                 (s-op2 (r swap negate)
                   (begin (r-opn g rop-reg (if swap 2 1))
                          (r-opnn g rop-op2 r (if swap 1 2))
                          (if negate (r-op2 g rop-op2imm (wcell-int routine-eq) (wcell-bool #f)) #u)
                          #t))
                 (s-op1 (r) (begin (r-opn g rop-reg 1) (r-opn g rop-op1 r) #t))
                 (s-op2imm (r v) (begin (r-opn g rop-reg 1) (r-op2 g rop-op2imm (wcell-int r) v) #t))
                 (s-field (k) (begin (r-opn g rop-reg 1) (r-opn g rop-field k) #t))
                 (s-identity () (begin (r-opn g rop-reg 1) #t))
                 (s-prim (p) (begin (r-opnn g rop-prim p n) #t))
                 (s-cellular (r) (if callout (begin (r-opnn g rop-cellular r n) #t) #f))
                 (else y #f))))
          (if made (begin (r-done g #t) (r-assemble g)) none))))))
;; A lambda's register code, whose closure captures what `inner` says, or
;; none where this compiler declines: in two versions where that is sound
;; and something is gained, as the Rust compiler's `register_code` says. Its
;; body compiled assuming every global it inlines, specializes or calls
;; itself through holds what it held when compiled, behind one guard for
;; each at its start; and, where a guard fails, compiled as ever. Sound where
;; no global can change during a run of the body: its effect summary is less
;; than 3. Only where the body makes no closure, so that compiling it twice
;; compiles nothing else twice.
(define r-register-code
  (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syns-a)) acyclic) exp cenv (listof c-this @k)) (listof wcell @k))
  (lambda (ps body inner this)
    (let ((outer (get r-declined))
          (outer-at (get r-spec-at)) (outer-start (get r-spec-start))
          (outer-own (get r-own-now)) (outer-name (get r-own-name)) (own (get c-own-now)))
      (begin
        (set c-own-now (the (listof (productof (1 symbol) (2 tword)) @k) nil))
        (let ((cells
               (if (and (< (c-summary-at (exp-start body) (exp-end body)) 3)
                        (and (>= (c-inline-room body 1000000000) 0) (r-fast-may-pay? ps body inner this own)))
                   (let* ((outer-assuming (get r-assuming)) (outer-assumed (get r-assumed))
                          (fast (begin (set r-assuming #t) (set r-assumed (the r-assumptions nil))
                                       (r-register-body ps body inner this own)))
                          (assumptions (r-rev-assumptions (get r-assumed) (the r-assumptions nil))))
                     (begin
                       (set r-assuming outer-assuming)
                       (set r-assumed outer-assumed)
                       ;; Worth it where the fast version is a leaf, or loops
                       ;; where the plain one calls: else its guards, all run
                       ;; on entry, cost more than the plain version's, each
                       ;; run where its call is.
                       (if (or (null? fast) (or (null? assumptions) (not (or (extract (car fast) leaf) (get r-looped)))))
                           (r-plain-code ps body inner this own)
                           (let ((plain (r-register-body ps body inner this own)))
                             (if (null? plain) (the (listof wcell @k) nil) (r-versions (car fast) (car plain) assumptions))))))
                   (r-plain-code ps body inner this own))))
          (begin (set r-declined outer) (set r-spec-at outer-at) (set r-spec-start outer-start)
                 (set r-own-now outer-own) (set r-own-name outer-name)
                 cells))))))

(set c-register-code r-register-code)
(set c-standard-register-code r-standard-word)

;; Whether the compiler makes register code from now on: for a driver.
(define compile-registers! (subr (maxeff (read @globals) (write @k)) (bool) unit) (lambda (on) (set c-registers on)))
