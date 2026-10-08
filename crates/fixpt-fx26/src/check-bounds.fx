;;; The checker, in FX-26: what has been said of a type binder, as bounds
;;; (`TODO.md` §66; Pierce and Turner's local type inference; the Rust
;;; checker's `infer.rs`, `Bounds`). At least what the arguments are,
;;; joined; at most what the context expects, met; and, inside something
;;; mutable, so invariant, exactly what is there. Where the bounds meet, or
;;; it is exact, the binder is known, and tells the arguments still to be
;;; checked what they are; until then its solution is the exact type, else
;;; the lower bound, else the upper. After `check-subtype.fx`, before
;;; `check-infer.fx`, whose `k-unify-var` keeps them.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-bounds-module (module
;; At least `1`, at most `2`, exactly `3`: types, -1 where nothing has said.
(define-type k-bound (productof (1 int) (2 int) (3 int)))
(define-type k-bound-map (ref (listof (pairof int k-bound @t) @t) @t))
;; Each instantiation's solution so far, and its binders' bounds, innermost
;; first. An instantiation that fails leaves its entry, found by no one.
(define-type k-bound-entry (pairof (ref k-map @t) k-bound-map @t))
(define k-bounds-stack (ref (listof k-bound-entry @t) @t) (new nil))
;; Whether `k-unify` bounds from above: matching what is expected of a call's
;; result, flipped inside a subroutine's parameters (Rust `unify_upper`).
(define k-unify-upper (ref bool @t) (new #f))
(define k-no-bound k-bound (product (1 -1) (2 -1) (3 -1)))

;; A new solution, with bounds kept for it.
(define* k-new-bounded-solved (subr (maxeff (read @t) (write @t) (alloc @t)) () (ref k-map @t))
  (lambda ()
    (let ((s (the (ref k-map @t) (new nil))))
      (begin (set k-bounds-stack (cons (cons s (the k-bound-map (new nil))) (get k-bounds-stack)))
             s))))
;; `x`, the bounds of `solved` dropped, and of any left inside it.
(define* k-drop-bounds (subr (maxeff (read @t) (write @t) spin) ((ref k-map @t) int) int)
  (lambda (solved x)
    (let ((st (get k-bounds-stack)))
      (if (null? st)
          x
          (begin (set k-bounds-stack (cdr st))
                 (if (eq? (car (car st)) solved) x (k-drop-bounds solved x)))))))
;; The bounds kept for `solved`, in a list of one; none if none are.
(define-type k-maybe-bounds (listof k-bound-map @t))
(define* k-bounds-in (subr (maxeff (read @t) (alloc @t) spin)
                           ((ref k-map @t) (listof k-bound-entry @t)) k-maybe-bounds)
  (lambda (solved st)
    (cond ((null? st) nil)
          ((eq? (car (car st)) solved) (the k-maybe-bounds (cons (cdr (car st)) nil)))
          (else (k-bounds-in solved (cdr st))))))
(define* k-bounds-of (subr (maxeff (read @t) (alloc @t) spin) ((ref k-map @t)) k-maybe-bounds)
  (lambda (solved) (k-bounds-in solved (get k-bounds-stack))))
(define* k-bound-get (subr (maxeff (read @t) spin) (k-bound-map int) k-bound)
  (lambda (m v)
    (letrec ((go (subr (maxeff (read @t) spin) ((listof (pairof int k-bound @t) @t)) k-bound)
               (lambda (bs) (cond ((null? bs) k-no-bound) ((= (car (car bs)) v) (cdr (car bs)))
                                  (else (go (cdr bs)))))))
      (go (get m)))))
;; The bounds `solved` keeps for type binder `v`, if they have not met:
;; neither fixed, nor at least and at most one type (the Rust checker's
;; `unsettled`); in a list of one, or none.
(define-type k-maybe-bound (listof k-bound @t))
(define* k-unsettled (subr (maxeff kstate spin) ((ref k-map @t) int) k-maybe-bound)
  (lambda (solved v)
    (let ((m (k-bounds-of solved)))
      (if (null? m)
          nil
          (let* ((b (k-bound-get (car m) v)) (lo (extract b 1)) (up (extract b 2)))
            (if (or (>= (extract b 3) 0) (and (< lo 0) (< up 0))
                    (and (>= lo 0) (>= up 0) (k-subtype up lo)))
                nil
                (the k-maybe-bound (cons b nil))))))))
;; `solved`'s solutions, but none of binders whose bounds have not met; or,
;; if `uppers`, those of them that have an upper bound at it.
(define* k-map-unsettled (subr (maxeff kstate spin) ((ref k-map @t) k-map bool) k-map)
  (lambda (solved m uppers)
    (if (null? m)
        m
        (let ((b (k-unsettled solved (car (car m))))
              (rest (k-map-unsettled solved (cdr m) uppers)))
          (cond ((null? b) (the k-map (cons (car m) rest)))
                ((not uppers) rest)
                ((< (extract (car b) 2) 0) (the k-map (cons (car m) rest)))
                (else (the k-map (cons (cons (car (car m)) (dt (extract (car b) 2))) rest))))))))

;; `k-unify`'s flags, set for `f`: in something invariant; matching what is
;; expected (from above); in a subroutine's parameters (the other way).
(define-type k-unifying (subr (maxeff kstate spin) () unit))
(define* k-exactly (subr (maxeff kstate spin) (k-unifying) unit)
  (lambda (f)
    (let ((outer (get k-unify-exact)))
      (begin (set k-unify-exact #t) (f) (set k-unify-exact outer)))))
(define* k-from-above (subr (maxeff kstate spin) (k-unifying) unit)
  (lambda (f)
    (let ((outer (get k-unify-upper)))
      (begin (set k-unify-upper #t) (f) (set k-unify-upper outer)))))
(define* k-flipped (subr (maxeff kstate spin) (k-unifying) unit)
  (lambda (f)
    (let ((outer (get k-unify-upper)))
      (begin (set k-unify-upper (not outer)) (f) (set k-unify-upper outer)))))

;; Whether `a` and `b` are the one below the other.
(define* k-related? (subr (maxeff kstate spin) (int int) bool)
  (lambda (a b) (or (k-subtype a b) (k-subtype b a))))
;; Bounds `b`, and what `a` says, as `k-unify` says it: exactly, from above,
;; or from below.
(define* k-bound-with (subr (maxeff kstate spin) (k-bound int) k-bound)
  (lambda (b a)
    (let ((lo (extract b 1)) (up (extract b 2)) (ex (extract b 3)))
      (cond ((get k-unify-exact)
             ;; What it meets there, where two are said.
             (product (1 lo) (2 up)
                      (3 (if (and (>= ex 0) (or (= ex a) (not (k-related? a ex)))) ex a))))
            ;; At most both: the smaller.
            ((get k-unify-upper)
             (product (1 lo) (2 (if (and (>= up 0) (not (k-subtype a up))) up a)) (3 ex)))
            ;; At least both: the larger.
            (else
             (product (1 (if (and (>= lo 0) (or (k-subtype a lo) (not (k-subtype lo a)))) lo a))
                      (2 up) (3 ex)))))))
(define* k-bound-set! (subr (maxeff (read @t) (write @t) (alloc @t)) (k-bound-map int k-bound) unit)
  (lambda (m v b) (set m (cons (cons v b) (get m)))))
;; What type binder `v` of `solved`, solved as `was` so far (-1: not), is
;; now that `a` has been said of it; -1 if it stays as it was. Where no
;; bounds are kept (a hint's matching), the larger, or in a pair's
;; contents what it meets.
(define* k-bound-solution (subr (maxeff kstate spin) ((ref k-map @t) int int int) int)
  (lambda (solved v a was)
    (let ((m (k-bounds-of solved)))
      (if (null? m)
          (cond ((< was 0) a)
                ((if (get k-unify-exact)
                     (and (not (= was a)) (k-related? a was))
                     (and (not (k-subtype a was)) (k-subtype was a)))
                 a)
                (else -1))
          (let ((b (k-bound-with (k-bound-get (car m) v) a)))
            (begin (k-bound-set! (car m) v b)
                   (cond ((>= (extract b 3) 0) (extract b 3))
                         ((>= (extract b 1) 0) (extract b 1))
                         (else (extract b 2)))))))))))

(define-type k-unifying (select check-bounds-module k-unifying))
(define k-exactly (with check-bounds-module k-exactly))
(define k-from-above (with check-bounds-module k-from-above))
(define k-flipped (with check-bounds-module k-flipped))
(define k-new-bounded-solved (with check-bounds-module k-new-bounded-solved))
(define k-drop-bounds (with check-bounds-module k-drop-bounds))
(define k-map-unsettled (with check-bounds-module k-map-unsettled))
(define k-bound-solution (with check-bounds-module k-bound-solution))
