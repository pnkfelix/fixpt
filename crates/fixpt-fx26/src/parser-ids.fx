;;; The FX-26 parser, in FX-26: each expression's identity
;;; (`parser-types.fx`): its position, its number in a walk of the
;;; program's trees that takes each expression before what is in it, the
;;; forms in order, from 0. Where it starts and ends are its provenance,
;;; kept beside. What the checkers find of an expression is kept by it, so
;;; two are never taken for one, not a desugaring's made where what it
;;; desugars is, nor a macro's argument placed twice
;;; (`docs/research/loads-and-places.md`, "Decided: identity by
;;; position"); the Rust front end numbers its trees alike (`ids.rs`).
;;; Part of the parser, after `parser-exps.fx`, before `parser-top.fx`.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define parser-types ((proj (load-module "fx26:parser-types.fx") rs re rm rc rp)))
(define tables (load-module "fx26:table.fx"))
(import tables make-table table-ref table-set! (type table))
(import parser-types e-var e-int e-bool e-str e-char e-float e-sym e-unit e-lambda e-app e-plambda
        e-proj e-if e-letrec e-let e-begin e-prompt e-letregion e-rlambda e-the e-convention
        e-bloblet e-product e-extract e-sum e-tagcase e-module e-with t-define t-define-rec t-exp
        (type exp top exp-list let-list letrec-list arm-list mod-items top-list))

;; How many expressions of the reading have been walked.
(define-type seen (ref int rs))
;; The readings so far: each `number-tops` is one, the reading every
;; expression it numbers is of, in a field of its own beside its number,
;; so that the two tell it from every other expression of the session
;; (`docs/research/loads-and-places.md`, "Decided: three keys").
(define readings (ref int rs) (new 0))
(define-effect counts (maxeff (read @globals) spin (read rs) (write rs) (alloc rs)))

;; The next expression's number, the one walked next (at `a`..`b`, which
;; does not matter: its provenance).
(define next-kth (->* (seen int int) int)
  (lambda (t a b) (let ((n (get t))) (begin (set t (+ n 1)) n))))

;; Each `number-` gives what it was given, not a copy, where nothing in it
;; changed: as the parser numbers every expression 0, the first.
(define-rec
  ;; `x` and what is in it, numbered.
  (number-exp (->* (seen exp) exp)
    (lambda (t x)
      (let ((reading (get readings)))
      (tagcase x
        (e-var (s a b k kr)
               (let ((n (next-kth t a b)))
                    (if (and (= n k) (= reading kr)) x (e-var s a b n reading))))
        (e-int (v a b k kr)
               (let ((n (next-kth t a b)))
                    (if (and (= n k) (= reading kr)) x (e-int v a b n reading))))
        (e-bool (v a b k kr)
                (let ((n (next-kth t a b)))
                     (if (and (= n k) (= reading kr)) x (e-bool v a b n reading))))
        (e-str (v a b k kr)
               (let ((n (next-kth t a b)))
                    (if (and (= n k) (= reading kr)) x (e-str v a b n reading))))
        (e-char (v a b k kr)
                (let ((n (next-kth t a b)))
                     (if (and (= n k) (= reading kr)) x (e-char v a b n reading))))
        (e-float (v a b k kr)
                 (let ((n (next-kth t a b)))
                      (if (and (= n k) (= reading kr)) x (e-float v a b n reading))))
        (e-sym (v a b k kr)
               (let ((n (next-kth t a b)))
                    (if (and (= n k) (= reading kr)) x (e-sym v a b n reading))))
        (e-unit (a b k kr)
                (let ((n (next-kth t a b)))
                     (if (and (= n k) (= reading kr)) x (e-unit a b n reading))))
        (e-lambda (ps body a b k kr)
          (let* ((n (next-kth t a b)) (body2 (number-exp t body)))
            (if (and (= n k) (= reading kr) (eq? body body2)) x (e-lambda ps body2 a b n reading))))
        (e-app (f xs a b k kr)
          (let* ((n (next-kth t a b)) (f2 (number-exp t f)) (xs2 (number-exps t xs)))
            (if (and (= n k) (= reading kr) (eq? f f2) (eq? xs xs2)) x
                (e-app f2 xs2 a b n reading))))
        (e-plambda (d body a b k kr)
          (let* ((n (next-kth t a b)) (body2 (number-exp t body)))
            (if (and (= n k) (= reading kr) (eq? body body2)) x (e-plambda d body2 a b n reading))))
        (e-proj (body ds a b k kr)
          (let* ((n (next-kth t a b)) (body2 (number-exp t body)))
            (if (and (= n k) (= reading kr) (eq? body body2)) x (e-proj body2 ds a b n reading))))
        (e-if (p c d a b k kr)
          (let* ((n (next-kth t a b)) (p2 (number-exp t p)) (c2 (number-exp t c))
                 (d2 (number-exp t d)))
            (if (and (= n k) (= reading kr) (eq? p p2) (eq? c c2) (eq? d d2)) x
                (e-if p2 c2 d2 a b n reading))))
        (e-letrec (bs body a b k kr)
          (let* ((n (next-kth t a b)) (bs2 (number-recs t bs)) (body2 (number-exp t body)))
            (if (and (= n k) (= reading kr) (eq? bs bs2) (eq? body body2)) x
                (e-letrec bs2 body2 a b n reading))))
        (e-let (bs body a b k kr)
          (let* ((n (next-kth t a b)) (bs2 (number-lets t bs)) (body2 (number-exp t body)))
            (if (and (= n k) (= reading kr) (eq? bs bs2) (eq? body body2)) x
                (e-let bs2 body2 a b n reading))))
        (e-begin (xs a b k kr)
          (let* ((n (next-kth t a b)) (xs2 (number-exps t xs)))
            (if (and (= n k) (= reading kr) (eq? xs xs2)) x (e-begin xs2 a b n reading))))
        (e-prompt (g body h a b k kr)
          (let* ((n (next-kth t a b)) (g2 (number-exp t g)) (body2 (number-exp t body))
                 (h2 (number-exp t h)))
            (if (and (= n k) (= reading kr) (eq? g g2) (eq? body body2) (eq? h h2))
                x
                (e-prompt g2 body2 h2 a b n reading))))
        (e-letregion (f r i body a b k kr)
          (let* ((n (next-kth t a b)) (body2 (number-exp t body)))
            (if (and (= n k) (= reading kr) (eq? body body2)) x
                (e-letregion f r i body2 a b n reading))))
        (e-rlambda (r l a b k kr)
          (let* ((n (next-kth t a b)) (r2 (number-exp t r)) (l2 (number-exp t l)))
            (if (and (= n k) (= reading kr) (eq? r r2) (eq? l l2)) x
                (e-rlambda r2 l2 a b n reading))))
        (e-the (d e a b k kr)
          (let* ((n (next-kth t a b)) (e2 (number-exp t e)))
            (if (and (= n k) (= reading kr) (eq? e e2)) x (e-the d e2 a b n reading))))
        (e-convention (c e a b k kr)
          (let* ((n (next-kth t a b)) (e2 (number-exp t e)))
            (if (and (= n k) (= reading kr) (eq? e e2)) x (e-convention c e2 a b n reading))))
        (e-bloblet (o i xs g a b k kr)
          (let* ((n (next-kth t a b)) (xs2 (number-exps t xs)))
            (if (and (= n k) (= reading kr) (eq? xs xs2)) x (e-bloblet o i xs2 g a b n reading))))
        (e-product (fs a b k kr)
          (let* ((n (next-kth t a b)) (fs2 (number-lets t fs)))
            (if (and (= n k) (= reading kr) (eq? fs fs2)) x (e-product fs2 a b n reading))))
        (e-extract (e l g a b k kr)
          (let* ((n (next-kth t a b)) (e2 (number-exp t e)))
            (if (and (= n k) (= reading kr) (eq? e e2)) x (e-extract e2 l g a b n reading))))
        (e-sum (l e a b k kr)
          (let* ((n (next-kth t a b)) (e2 (number-exp t e)))
            (if (and (= n k) (= reading kr) (eq? e e2)) x (e-sum l e2 a b n reading))))
        (e-tagcase (s arms els g a b k kr)
          (let* ((n (next-kth t a b)) (s2 (number-exp t s)) (arms2 (number-arms t arms))
                 (els2 (number-lets t els)))
            (if (and (= n k) (= reading kr) (eq? s s2) (eq? arms arms2) (eq? els els2))
                x
                (e-tagcase s2 arms2 els2 g a b n reading))))
        (e-module (items a b k kr)
          (let* ((n (next-kth t a b)) (items2 (number-items t items)))
            (if (and (= n k) (= reading kr) (eq? items items2)) x (e-module items2 a b n reading))))
        (e-with (m body a b k kr)
          (let* ((n (next-kth t a b)) (body2 (number-exp t body)))
            (if (and (= n k) (= reading kr) (eq? body body2)) x
                (e-with m body2 a b n reading))))))))
  (number-exps (->* (seen exp-list) exp-list)
    (lambda (t xs)
      (if (null? xs)
          xs
          (let* ((x (number-exp t (car xs))) (rest (number-exps t (cdr xs))))
            (if (and (eq? x (car xs)) (eq? rest (cdr xs))) xs (cons x rest))))))
  ;; A `let`'s bindings, a product's fields, a `tagcase`'s `else`.
  (number-lets (->* (seen let-list) let-list)
    (lambda (t bs)
      (if (null? bs)
          bs
          (let* ((x (number-exp t (extract (car bs) 2))) (rest (number-lets t (cdr bs))))
            (if (and (eq? x (extract (car bs) 2)) (eq? rest (cdr bs)))
                bs
                (cons (product (1 (extract (car bs) 1)) (2 x)) rest))))))
  (number-recs (->* (seen letrec-list) letrec-list)
    (lambda (t bs)
      (if (null? bs)
          bs
          (let* ((x (number-exp t (extract (car bs) 3))) (rest (number-recs t (cdr bs))))
            (if (and (eq? x (extract (car bs) 3)) (eq? rest (cdr bs)))
                bs
                (cons (product (1 (extract (car bs) 1)) (2 (extract (car bs) 2)) (3 x)) rest))))))
  (number-arms (->* (seen arm-list) arm-list)
    (lambda (t arms)
      (if (null? arms)
          arms
          (let* ((arm (car arms)) (x (number-exp t (extract arm 4)))
                 (rest (number-arms t (cdr arms))))
            (if (and (eq? x (extract arm 4)) (eq? rest (cdr arms)))
                arms
                (cons (product (1 (extract arm 1)) (2 (extract arm 2)) (3 (extract arm 3)) (4 x))
                      rest))))))
  (number-items (->* (seen mod-items) mod-items)
    (lambda (t items)
      (if (null? items)
          items
          (let* ((it (car items)) (xs (number-exps t (extract it 4)))
                 (rest (number-items t (cdr items))))
            (if (and (eq? xs (extract it 4)) (eq? rest (cdr items)))
                items
                (cons (product (1 (extract it 1)) (2 (extract it 2)) (3 (extract it 3)) (4 xs))
                      rest)))))))

;; Form `x`, its expressions numbered.
(define number-top (->* (seen top) top)
  (lambda (t x)
    (tagcase x
      (t-define (n ty e a b) (let ((e2 (number-exp t e))) (if (eq? e e2) x (t-define n ty e2 a b))))
      (t-define-rec (bs a b)
        (let ((bs2 (number-recs t bs))) (if (eq? bs bs2) x (t-define-rec bs2 a b))))
      (t-exp (e) (let ((e2 (number-exp t e))) (if (eq? e e2) x (t-exp e2))))
      (else y x))))
(define number-each (->* (seen top-list) top-list)
  (lambda (t ts)
    (if (null? ts) nil (let* ((x (number-top t (car ts)))) (cons x (number-each t (cdr ts)))))))
;; A program's forms, each expression in them numbered, the forms in order.
(define number-tops (->* (top-list) top-list)
  (lambda (ts)
    (begin (set readings (+ (get readings) 1)) (number-each (the seen (new 0)) ts))))
