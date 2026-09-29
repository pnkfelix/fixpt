;;; LOGIC -- a Prolog-style solver in continuation-passing style, with a
;;; trail of bindings to undo: peg solitaire on a triangular board.
;;;
;;; From the SML/NJ benchmark suite.
;;; From MLton's benchmark suite (benchmark/tests/logic.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. MLton's driver was not fetched; the
;;; iteration count, 2 solves of `solution2`, is this port's. MLton's
;;; `doit n` runs n solves.
;;; Answer: 2, the number of solves that found a solution (each raises
;;; Done, which `doit` handles).
;;;
;;; What changed:
;;; - `term option ref` is a `(ref term-option @heap)`, `term-option` a
;;;   sum of NONE and SOME, and PROBE, which no term ever holds: SML
;;;   compares refs by identity (`same_ref`, the occurs check), and FX-26
;;;   has no identity test, so `same-var?` writes PROBE into one reference,
;;;   reads the other, and writes back what the first held.
;;; - The exception Done is an abort to a prompt in `doit`; BadArg, which
;;;   `unwind_trail` raises only on a trail shorter than its count (never),
;;;   is not there: that case gives back the empty trail.
;;; - Curried procedures (`unify (s, t) sc`, `move_horiz (T_1, T_2) sc`, …)
;;;   take all their arguments at once.
;;; - The data: the relations (`move_horiz`, `rotate`, `move`, `solitaire`,
;;;   `solution1`, `solution2`) were translated from the SML text by a
;;;   script, clause for clause; `[a, b]` is `(list2 a b)` and `[a]` is
;;;   `(list1 a)`, lists made at @heap.
;;; - `rotate` makes its fifteen fresh variables with one `exists15`, which
;;;   hands them over in a product of the board's rows, where SML nests
;;;   fifteen `exists`: the innermost of those closures would capture
;;;   seventeen variables, and a closure over more than `register-regs` (8)
;;;   has no register code, so the whole group ran as cellular code, and the
;;;   abort of Done, from native code, found no prompt. (One product of
;;;   fifteen fields has no register code either: hence the rows.) The
;;;   variables are the same, made in the same order; six products are
;;;   made, and fourteen closures are not.

;;; ------------------------------------------------------------ term.sml

;; `term` and `term-option` refer to each other, which neither
;; `define-datatype` nor `define-type` can say (each sees only the types
;; before it), so `term` is written as `define-datatype` would expand it,
;; a sum of products with a constructor per variant, with the option
;; written out inside it; `term-option` then names that option (types are
;; structural, so the two are one).
(define-type term
  (sumof (STR (productof (1 string) (2 (listof term @heap))))
         (INT (productof (1 int)))
         (CON (productof (1 string)))
         (REF (productof (1 (ref (sumof (NONE (productof)) (SOME (productof (1 term))) (PROBE (productof))) @heap))))))
(define-type term-option (sumof (NONE (productof)) (SOME (productof (1 term))) (PROBE (productof))))
(define STR (subr pure (string (listof term @heap)) term) (lambda (f ts) (sum STR (product (1 f) (2 ts)))))
(define INT (subr pure (int) term) (lambda (n) (sum INT (product (1 n)))))
(define CON (subr pure (string) term) (lambda (s) (sum CON (product (1 s)))))
(define REF (subr pure ((ref term-option @heap)) term) (lambda (r) (sum REF (product (1 r)))))
(define NONE (subr pure () term-option) (lambda () (sum NONE (product))))
(define SOME (subr pure (term) term-option) (lambda (t) (sum SOME (product (1 t)))))
(define PROBE (subr pure () term-option) (lambda () (sum PROBE (product))))
(define-type terms (listof term @heap))
(define-type var (ref term-option @heap))
(define-type vars (listof var @heap))

;; Everything solving does; Done aborts to @z.
(define-effect solving (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals) (goto @z)))

;;; ----------------------------------------------------------- trail.sml

(define global-trail (ref vars @heap) (new (the vars nil)))
(define trail-counter (ref int @heap) (new 0))

(define* unwind-trail (subr (maxeff (read @heap) (write @heap) spin) (int vars) vars)
  (lambda (n tr)
    (if (= n 0)
        tr
        (if (null? tr)
            tr
            (begin (set (car tr) (NONE)) (unwind-trail (- n 1) (cdr tr)))))))

(define* reset-trail (subr (maxeff (write @heap) (read @globals)) () unit)
  (lambda () (set global-trail (the vars nil))))

(define* trail (subr solving ((subr solving () unit)) unit)
  (lambda (func)
    (let ((tc0 (get trail-counter)))
      (begin
        (func)
        (set global-trail (unwind-trail (- (get trail-counter) tc0) (get global-trail)))
        (set trail-counter tc0)))))

(define* bind (subr (maxeff (read @heap) (write @heap) (alloc @heap) (read @globals)) (var term) unit)
  (lambda (r t)
    (begin
      (set r (SOME t))
      (set global-trail (the vars (cons r (get global-trail))))
      (set trail-counter (+ (get trail-counter) 1)))))

;;; ----------------------------------------------------------- unify.sml

;; Whether two references are one (SML's `r = r'`).
(define* same-var? (subr (maxeff (read @heap) (write @heap) (read @globals)) (var var) bool)
  (lambda (r s)
    (let ((old (get r)))
      (begin
        (set r (PROBE))
        (let ((same (tagcase (get s) (PROBE () #t) (else o #f))))
          (begin (set r old) same))))))

(define* same-ref (subr (maxeff (read @heap) (write @heap) (read @globals)) (var term) bool)
  (lambda (r t) (tagcase t (REF (r2) (same-var? r r2)) (else o #f))))

(define* occurs-check (subr (maxeff (read @heap) (write @heap) spin (read @globals)) (var term) bool)
  (lambda (r t)
    (letrec ((oc (subr (maxeff (read @heap) (write @heap) spin (read @globals)) (term) bool)
               (lambda (t)
                 (tagcase t
                   (STR (f ts) (ocs ts))
                   (REF (r2) (tagcase (get r2) (SOME (s) (oc s)) (else o (not (same-var? r r2)))))
                   (CON (c) #t)
                   (INT (i) #t))))
             (ocs (subr (maxeff (read @heap) (write @heap) spin (read @globals)) (terms) bool)
               (lambda (ts) (if (null? ts) #t (and (oc (car ts)) (ocs (cdr ts)))))))
      (oc t))))

(define* deref (subr (maxeff (read @heap) spin (read @globals)) (term) term)
  (lambda (t)
    (tagcase t
      (REF (x) (tagcase (get x) (SOME (s) (deref s)) (else o t)))
      (else o t))))

(define-rec
  (unify1 (subr solving (term term (subr solving () unit)) unit)
    (lambda (s t sc)
      (tagcase s
        (REF (r) (unify-REF r t sc))
        (else s1
          (tagcase t
            (REF (r) (unify-REF r s sc))
            (else t1
              (tagcase s
                (STR (f ts) (tagcase t (STR (g ss) (if (string=? f g) (unifys ts ss sc) #u)) (else o #u)))
                (CON (f) (tagcase t (CON (g) (if (string=? f g) (sc) #u)) (else o #u)))
                (INT (f) (tagcase t (INT (g) (if (= f g) (sc) #u)) (else o #u)))
                (else o #u))))))))
  (unifys (subr solving (terms terms (subr solving () unit)) unit)
    (lambda (ts ss sc)
      (if (null? ts)
          (if (null? ss) (sc) #u)
          (if (null? ss)
              #u
              (unify1 (deref (car ts)) (deref (car ss)) (lambda () (unifys (cdr ts) (cdr ss) sc)))))))
  (unify-REF (subr solving (var term (subr solving () unit)) unit)
    (lambda (r t sc)
      (if (same-ref r t)
          (sc)
          (if (occurs-check r t)
              (begin (bind r t) (sc))
              #u)))))

(define* unify (subr solving (term term (subr solving () unit)) unit)
  (lambda (s t sc) (unify1 (deref s) (deref t) sc)))

;;; ------------------------------------------------------------ data.sml

(define cons-s string "cons")
(define x-s string "x")
(define nil-s string "nil")
(define o-s string "o")
(define s-s string "s")
(define con-o-s term (CON o-s))
(define con-nil-s term (CON nil-s))
(define con-x-s term (CON x-s))

(define list1 (subr (alloc @heap) (term) terms) (lambda (a) (cons a nil)))
(define list2 (subr (alloc @heap) (term term) terms) (lambda (a b) (cons a (cons b nil))))

(define* exists (subr solving ((subr solving (term) unit)) unit)
  (lambda (sc) (sc (REF (the var (new (NONE)))))))

;; The board's pegs, by row, as the triangle is laid out.
(define-type pegs
  (productof (r1 (productof (P11 term) (P12 term) (P13 term) (P14 term) (P15 term)))
             (r2 (productof (P21 term) (P22 term) (P23 term) (P24 term)))
             (r3 (productof (P31 term) (P32 term) (P33 term)))
             (r4 (productof (P41 term) (P42 term)))
             (r5 (productof (P51 term)))))
(define* fresh (subr (maxeff (alloc @heap) (read @globals)) () term)
  (lambda () (REF (the var (new (NONE))))))
(define* exists15 (subr solving ((subr solving (pegs) unit)) unit)
  (lambda (sc)
    (sc (product (r1 (product (P11 (fresh)) (P12 (fresh)) (P13 (fresh)) (P14 (fresh)) (P15 (fresh))))
                 (r2 (product (P21 (fresh)) (P22 (fresh)) (P23 (fresh)) (P24 (fresh))))
                 (r3 (product (P31 (fresh)) (P32 (fresh)) (P33 (fresh))))
                 (r4 (product (P41 (fresh)) (P42 (fresh))))
                 (r5 (product (P51 (fresh))))))))

(define-rec
  (move-horiz (subr solving (term term (subr solving () unit)) unit)
   (lambda (T-1 T-2 sc)
  (begin
   (trail (lambda ()
    (begin
     (trail (lambda ()
      (begin
       (trail (lambda ()
        (begin
         (trail (lambda ()
          (begin
           (trail (lambda ()
            (begin
             (trail (lambda ()
              (begin
               (trail (lambda ()
                (begin
                 (trail (lambda ()
                  (begin
                   (trail (lambda ()
                    (begin
                     (trail (lambda ()
                      (begin
                       (trail (lambda ()
                        (exists (lambda ((T term))
                        (exists (lambda ((TT term))
                        (unify T-1 (STR cons-s (list2 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-o-s T)))))) TT)) (lambda ()
                        (unify T-2 (STR cons-s (list2 (STR cons-s (list2 con-o-s (STR cons-s (list2 con-o-s (STR cons-s (list2 con-x-s T)))))) TT)) (lambda ()
                        (sc)))))))))))
                       (exists (lambda ((P1 term))
                       (exists (lambda ((P5 term))
                       (exists (lambda ((TT term))
                       (unify T-1 (STR cons-s (list2 (STR cons-s (list2 P1 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-o-s (STR cons-s (list2 P5 con-nil-s)))))))))) TT)) (lambda ()
                       (unify T-2 (STR cons-s (list2 (STR cons-s (list2 P1 (STR cons-s (list2 con-o-s (STR cons-s (list2 con-o-s (STR cons-s (list2 con-x-s (STR cons-s (list2 P5 con-nil-s)))))))))) TT)) (lambda ()
                       (sc))))))))))))))
                     (exists (lambda ((P1 term))
                     (exists (lambda ((P2 term))
                     (exists (lambda ((TT term))
                     (unify T-1 (STR cons-s (list2 (STR cons-s (list2 P1 (STR cons-s (list2 P2 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-o-s con-nil-s)))))))))) TT)) (lambda ()
                     (unify T-2 (STR cons-s (list2 (STR cons-s (list2 P1 (STR cons-s (list2 P2 (STR cons-s (list2 con-o-s (STR cons-s (list2 con-o-s (STR cons-s (list2 con-x-s con-nil-s)))))))))) TT)) (lambda ()
                     (sc))))))))))))))
                   (exists (lambda ((L1 term))
                   (exists (lambda ((P4 term))
                   (exists (lambda ((TT term))
                   (unify T-1 (STR cons-s (list2 L1 (STR cons-s (list2 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-o-s (STR cons-s (list2 P4 con-nil-s)))))))) TT)))) (lambda ()
                   (unify T-2 (STR cons-s (list2 L1 (STR cons-s (list2 (STR cons-s (list2 con-o-s (STR cons-s (list2 con-o-s (STR cons-s (list2 con-x-s (STR cons-s (list2 P4 con-nil-s)))))))) TT)))) (lambda ()
                   (sc))))))))))))))
                 (exists (lambda ((L1 term))
                 (exists (lambda ((P1 term))
                 (exists (lambda ((TT term))
                 (unify T-1 (STR cons-s (list2 L1 (STR cons-s (list2 (STR cons-s (list2 P1 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-o-s con-nil-s)))))))) TT)))) (lambda ()
                 (unify T-2 (STR cons-s (list2 L1 (STR cons-s (list2 (STR cons-s (list2 P1 (STR cons-s (list2 con-o-s (STR cons-s (list2 con-o-s (STR cons-s (list2 con-x-s con-nil-s)))))))) TT)))) (lambda ()
                 (sc))))))))))))))
               (exists (lambda ((L1 term))
               (exists (lambda ((L2 term))
               (exists (lambda ((TT term))
               (unify T-1 (STR cons-s (list2 L1 (STR cons-s (list2 L2 (STR cons-s (list2 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-o-s con-nil-s)))))) TT)))))) (lambda ()
               (unify T-2 (STR cons-s (list2 L1 (STR cons-s (list2 L2 (STR cons-s (list2 (STR cons-s (list2 con-o-s (STR cons-s (list2 con-o-s (STR cons-s (list2 con-x-s con-nil-s)))))) TT)))))) (lambda ()
               (sc))))))))))))))
             (exists (lambda ((T term))
             (exists (lambda ((TT term))
             (unify T-1 (STR cons-s (list2 (STR cons-s (list2 con-o-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s T)))))) TT)) (lambda ()
             (unify T-2 (STR cons-s (list2 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-o-s (STR cons-s (list2 con-o-s T)))))) TT)) (lambda ()
             (sc))))))))))))
           (exists (lambda ((P1 term))
           (exists (lambda ((P5 term))
           (exists (lambda ((TT term))
           (unify T-1 (STR cons-s (list2 (STR cons-s (list2 P1 (STR cons-s (list2 con-o-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 P5 con-nil-s)))))))))) TT)) (lambda ()
           (unify T-2 (STR cons-s (list2 (STR cons-s (list2 P1 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-o-s (STR cons-s (list2 con-o-s (STR cons-s (list2 P5 con-nil-s)))))))))) TT)) (lambda ()
           (sc))))))))))))))
         (exists (lambda ((P1 term))
         (exists (lambda ((P2 term))
         (exists (lambda ((TT term))
         (unify T-1 (STR cons-s (list2 (STR cons-s (list2 P1 (STR cons-s (list2 P2 (STR cons-s (list2 con-o-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s con-nil-s)))))))))) TT)) (lambda ()
         (unify T-2 (STR cons-s (list2 (STR cons-s (list2 P1 (STR cons-s (list2 P2 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-o-s (STR cons-s (list2 con-o-s con-nil-s)))))))))) TT)) (lambda ()
         (sc))))))))))))))
       (exists (lambda ((L1 term))
       (exists (lambda ((P4 term))
       (exists (lambda ((TT term))
       (unify T-1 (STR cons-s (list2 L1 (STR cons-s (list2 (STR cons-s (list2 con-o-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 P4 con-nil-s)))))))) TT)))) (lambda ()
       (unify T-2 (STR cons-s (list2 L1 (STR cons-s (list2 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-o-s (STR cons-s (list2 con-o-s (STR cons-s (list2 P4 con-nil-s)))))))) TT)))) (lambda ()
       (sc))))))))))))))
     (exists (lambda ((L1 term))
     (exists (lambda ((P1 term))
     (exists (lambda ((TT term))
     (unify T-1 (STR cons-s (list2 L1 (STR cons-s (list2 (STR cons-s (list2 P1 (STR cons-s (list2 con-o-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s con-nil-s)))))))) TT)))) (lambda ()
     (unify T-2 (STR cons-s (list2 L1 (STR cons-s (list2 (STR cons-s (list2 P1 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-o-s (STR cons-s (list2 con-o-s con-nil-s)))))))) TT)))) (lambda ()
     (sc))))))))))))))
   (exists (lambda ((L1 term))
   (exists (lambda ((L2 term))
   (exists (lambda ((TT term))
   (unify T-1 (STR cons-s (list2 L1 (STR cons-s (list2 L2 (STR cons-s (list2 (STR cons-s (list2 con-o-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s con-nil-s)))))) TT)))))) (lambda ()
   (unify T-2 (STR cons-s (list2 L1 (STR cons-s (list2 L2 (STR cons-s (list2 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-o-s (STR cons-s (list2 con-o-s con-nil-s)))))) TT)))))) (lambda ()
   (sc))))))))))))))
  (rotate (subr solving (term term (subr solving () unit)) unit)
   (lambda (T-1 T-2 sc)
  (exists15 (lambda ((p pegs))
  (unify T-1 (STR cons-s (list2 (STR cons-s (list2 (extract (extract p r1) P11) (STR cons-s (list2 (extract (extract p r1) P12) (STR cons-s (list2 (extract (extract p r1) P13) (STR cons-s (list2 (extract (extract p r1) P14) (STR cons-s (list2 (extract (extract p r1) P15) con-nil-s)))))))))) (STR cons-s (list2 (STR cons-s (list2 (extract (extract p r2) P21) (STR cons-s (list2 (extract (extract p r2) P22) (STR cons-s (list2 (extract (extract p r2) P23) (STR cons-s (list2 (extract (extract p r2) P24) con-nil-s)))))))) (STR cons-s (list2 (STR cons-s (list2 (extract (extract p r3) P31) (STR cons-s (list2 (extract (extract p r3) P32) (STR cons-s (list2 (extract (extract p r3) P33) con-nil-s)))))) (STR cons-s (list2 (STR cons-s (list2 (extract (extract p r4) P41) (STR cons-s (list2 (extract (extract p r4) P42) con-nil-s)))) (STR cons-s (list2 (STR cons-s (list2 (extract (extract p r5) P51) con-nil-s)) con-nil-s)))))))))) (lambda ()
  (unify T-2 (STR cons-s (list2 (STR cons-s (list2 (extract (extract p r5) P51) (STR cons-s (list2 (extract (extract p r4) P41) (STR cons-s (list2 (extract (extract p r3) P31) (STR cons-s (list2 (extract (extract p r2) P21) (STR cons-s (list2 (extract (extract p r1) P11) con-nil-s)))))))))) (STR cons-s (list2 (STR cons-s (list2 (extract (extract p r4) P42) (STR cons-s (list2 (extract (extract p r3) P32) (STR cons-s (list2 (extract (extract p r2) P22) (STR cons-s (list2 (extract (extract p r1) P12) con-nil-s)))))))) (STR cons-s (list2 (STR cons-s (list2 (extract (extract p r3) P33) (STR cons-s (list2 (extract (extract p r2) P23) (STR cons-s (list2 (extract (extract p r1) P13) con-nil-s)))))) (STR cons-s (list2 (STR cons-s (list2 (extract (extract p r2) P24) (STR cons-s (list2 (extract (extract p r1) P14) con-nil-s)))) (STR cons-s (list2 (STR cons-s (list2 (extract (extract p r1) P15) con-nil-s)) con-nil-s)))))))))) (lambda ()
  (sc)))))))))
  (move (subr solving (term term (subr solving () unit)) unit)
   (lambda (T-1 T-2 sc)
  (begin
   (trail (lambda ()
    (begin
     (trail (lambda ()
      (exists (lambda ((X term))
      (exists (lambda ((Y term))
      (unify T-1 X (lambda ()
      (unify T-2 Y (lambda ()
      (move-horiz X Y sc)))))))))))
     (exists (lambda ((X term))
     (exists (lambda ((X1 term))
     (exists (lambda ((Y term))
     (exists (lambda ((Y1 term))
     (unify T-1 X (lambda ()
     (unify T-2 Y (lambda ()
     (rotate X X1 (lambda ()
     (move-horiz X1 Y1 (lambda ()
     (rotate Y Y1 sc))))))))))))))))))))
   (exists (lambda ((X term))
   (exists (lambda ((X1 term))
   (exists (lambda ((Y term))
   (exists (lambda ((Y1 term))
   (unify T-1 X (lambda ()
   (unify T-2 Y (lambda ()
   (rotate X1 X (lambda ()
   (move-horiz X1 Y1 (lambda ()
   (rotate Y1 Y sc))))))))))))))))))))
  (solitaire (subr solving (term term term (subr solving () unit)) unit)
   (lambda (T-1 T-2 T-3 sc)
  (begin
   (trail (lambda ()
    (exists (lambda ((X term))
    (unify T-1 X (lambda ()
    (unify T-2 (STR cons-s (list2 X con-nil-s)) (lambda ()
    (unify T-3 (INT 0) (lambda ()
    (sc)))))))))))
   (exists (lambda ((N term))
   (exists (lambda ((X term))
   (exists (lambda ((Y term))
   (exists (lambda ((Z term))
   (unify T-1 X (lambda ()
   (unify T-2 (STR cons-s (list2 X Z)) (lambda ()
   (unify T-3 (STR s-s (list1 N)) (lambda ()
   (move X Y (lambda ()
   (solitaire Y Z N sc))))))))))))))))))))
  (solution1 (subr solving (term (subr solving () unit)) unit)
   (lambda (T-1 sc)
  (exists (lambda ((X term))
  (unify T-1 X (lambda ()
  (solitaire (STR cons-s (list2 (STR cons-s (list2 con-o-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s con-nil-s)))))))))) (STR cons-s (list2 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s con-nil-s)))))))) (STR cons-s (list2 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s con-nil-s)))))) (STR cons-s (list2 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s con-nil-s)))) (STR cons-s (list2 (STR cons-s (list2 con-x-s con-nil-s)) con-nil-s)))))))))) X (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (INT 0))))))))))))))))))))))))))) sc)))))))
  (solution2 (subr solving (term (subr solving () unit)) unit)
   (lambda (T-1 sc)
  (exists (lambda ((X term))
  (unify T-1 X (lambda ()
  (solitaire (STR cons-s (list2 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s con-nil-s)))))))))) (STR cons-s (list2 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s con-nil-s)))))))) (STR cons-s (list2 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-o-s (STR cons-s (list2 con-x-s con-nil-s)))))) (STR cons-s (list2 (STR cons-s (list2 con-x-s (STR cons-s (list2 con-x-s con-nil-s)))) (STR cons-s (list2 (STR cons-s (list2 con-x-s con-nil-s)) con-nil-s)))))))))) X (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (STR s-s (list1 (INT 0))))))))))))))))))))))))))) sc))))))))

;;; ------------------------------------------------------------ main.sml

(define done-tag (prompt-tag int unit (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)) @z)
  (make-continuation-prompt-tag))

(define* doit (subr solving () int)
  (lambda ()
    (prompt done-tag
      (begin
        (exists (lambda ((Z term)) (solution2 Z (lambda () (abort-current-continuation done-tag #u)))))
        0)
      (lambda (u) 1))))

;; The input, where no compiler can fold it: a global, which a later
;; definition may replace.
(define iterations int 2)

(define* run (subr solving (int int) int)
  (lambda (i solved) (if (= i 0) solved (run (- i 1) (+ solved (doit))))))
(run iterations 0)
