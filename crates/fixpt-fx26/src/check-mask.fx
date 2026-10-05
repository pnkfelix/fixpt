;;; The checker, in FX-26: masking an expression's effect. Part of the
;;; checker, `check-types.fx` first (moved out of `check-resolve.fx`,
;;; 2026-10-04).

;;; ------------------------------------------------------------ masking
;;; What cannot be observed outside `x`, whose type is `result`, is removed:
;;; everything on a region that no free variable's type mentions, except
;;; that `alloc`, `goto` and `comefrom` on a region the result mentions stay
;;; (ranks 2 to 4; `await`, like `read`, does not).

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-mask-module (module
;; Whether an atom is on `const`, the frozen region.
(define k-frozen-atom? (subr (read @globals) (k-atom) bool)
  (lambda (a) (and (k-has-region? a) (tagcase (k-atom-region a) (r-frozen (p f) #t) (else y #f)))))
;; Whether an atom is on data frozen into a place, other than a write: it is
;; masked as what is done to the place is
;; (`docs/research/soundness-findings.md`, F2).
(define k-place-frozen-atom? (subr (read @globals) (k-atom) bool)
  (lambda (a)
    (and (k-has-region? a) (not (= (k-atom-rank a) 1))
         (tagcase (k-atom-region a) (r-frozen (p f) (>= p 0)) (else y #f)))))
;; The region an atom is masked by: a place-frozen atom's place.
(define k-mask-region (subr (read @globals) (k-atom) k-region)
  (lambda (a)
    (if (k-place-frozen-atom? a)
        (tagcase (k-atom-region a) (r-frozen (p f) (r-var p)) (else y (k-atom-region a)))
        (k-atom-region a))))
;; Whether an atom stays because the result mentions its region: `alloc`,
;; `goto` and `comefrom` (ranks 2 to 4); only `alloc`, for a place-frozen
;; one.
(define k-result-keeps? (subr (read @globals) (k-atom) bool)
  (lambda (a)
    (let ((rank (k-atom-rank a)))
      (if (k-place-frozen-atom? a) (= rank 2) (and (> rank 1) (< rank 5))))))
;; Whether an atom stays because the result, whose regions are
;; `in-result`, mentions its region.
(define k-stays-for-result? (subr (maxeff kreads spin) (k-atom k-regions) bool)
  (lambda (a in-result)
    (and (k-has-region-in? in-result (k-mask-region a)) (k-result-keeps? a))))
;; Whether an atom is on frozen data in no place: it is never masked.
(define k-unplaced-frozen-atom? (subr (read @globals) (k-atom) bool)
  (lambda (a) (and (k-frozen-atom? a) (not (k-place-frozen-atom? a)))))
;; The regions of `e`'s atoms that stay only if a free variable sees them.
(define k-sought (subr (maxeff kmakes spin) (k-eff k-regions k-regions) k-regions)
  (lambda (e in-result out)
    (if (null? e)
        out
        (let ((a (car e)))
          (k-sought (cdr e) in-result
                    (if (and (k-has-region? a) (not (k-globals-atom? a))
                             (not (k-unplaced-frozen-atom? a))
                             (not (k-stays-for-result? a in-result)))
                        (k-add-region out (k-mask-region a))
                        out))))))
(define k-drop-regions (subr (maxeff kmakes spin) (k-regions k-regions) k-regions)
  (lambda (rs seen)
    (cond ((null? rs) nil)
          ((k-has-region-in? seen (car rs)) (k-drop-regions (cdr rs) seen))
          (else (cons (car rs) (k-drop-regions (cdr rs) seen))))))

;; Of the regions `rs`, those no variable free in `x` sees: a walk of `x`
;; as `k-free-into`'s, that stops once each has been seen, as most are.
(define-rec
  (k-unseen-list (subr (maxeff kstate spin) (kxs k-names k-regions) k-regions)
    (lambda (xs bound rs)
      (if (or (null? xs) (null? rs))
          rs
          (k-unseen-list (cdr xs) bound (k-unseen (car xs) bound rs)))))
  (k-unseen (subr (maxeff kstate spin) (kx k-names k-regions) k-regions)
    (lambda (x bound rs)
      (if (null? rs)
          rs
          (tagcase x
            (x-var (s a b)
              (let ((t (if (k-has-name? bound s) -1 (k-lookup s))))
                (if (< t 0) rs (k-drop-regions rs (k-regions-in t)))))
            (x-const (t v a b) rs)
            (x-lambda (ps body a b) (k-unseen body (k-param-names ps bound) rs))
            (x-app (f args a b) (k-unseen-list args bound (k-unseen f bound rs)))
            (x-plambda (bs body a b) (k-unseen body bound rs))
            (x-letregion (k r i body a b) (k-unseen body (cons (k-dvar-name r) bound) rs))
            (x-rlambda (r l a b) (k-unseen l bound (k-unseen r bound rs)))
            (x-proj (body ds a b) (k-unseen body bound rs))
            (x-if (p c d a b) (k-unseen d bound (k-unseen c bound (k-unseen p bound rs))))
            (x-letrec (bs body a b)
              (let ((inner (k-letrec-names bs bound)))
                (k-unseen body inner (k-unseen-letrec bs inner rs))))
            (x-let (bs body a b) (k-unseen body (k-let-names bs bound) (k-unseen-let bs bound rs)))
            (x-begin (xs a b) (k-unseen-list xs bound rs))
            (x-prompt (t body h a b) (k-unseen h bound (k-unseen body bound (k-unseen t bound rs))))
            (x-the (t body a b) (k-unseen body bound rs))
            (x-convention (c body a b) (k-unseen body bound rs))
            (x-bloblet (o i xs a b) (k-unseen-list xs bound rs))
            ;; A product's fields are as a `let`'s bindings.
            (x-product (fs a b) (k-unseen-let fs bound rs))
            (x-extract (body l a b) (k-unseen body bound rs))
            (x-sum (l body a b) (k-unseen body bound rs))
            (x-tagcase (s arms els a b)
              (let ((o (k-unseen-arms arms bound (k-unseen s bound rs))))
                (k-unseen-else els bound o)))
            (x-module (items a b) (k-unseen-module items bound rs))
            (x-with (m body a b)
              (let ((o (k-unseen (x-var m a b) bound rs)))
                (k-unseen body (k-names-onto (k-with-names a b) bound) o)))))))
  ;; The same walk of a module's items, every item's names bound, as a
  ;; `letrec*`'s.
  (k-unseen-module (subr (maxeff kstate spin) (k-items k-names k-regions) k-regions)
    (lambda (items bound rs) (k-unseen-items items (k-items-bound items bound) rs)))
  (k-unseen-items (subr (maxeff kstate spin) (k-items k-names k-regions) k-regions)
    (lambda (items bound rs)
      (if (null? items)
          rs
          (k-unseen-items (cdr items) bound (k-unseen-list (extract (car items) 5) bound rs)))))
  (k-unseen-letrec (subr (maxeff kstate spin) (k-letrec-bs k-names k-regions) k-regions)
    (lambda (bs bound rs)
      (if (null? bs)
          rs
          (k-unseen-letrec (cdr bs) bound (k-unseen (extract (car bs) 3) bound rs)))))
  (k-unseen-let (subr (maxeff kstate spin) (k-let-bs k-names k-regions) k-regions)
    (lambda (bs bound rs)
      (if (null? bs)
          rs
          (k-unseen-let (cdr bs) bound (k-unseen (extract (car bs) 2) bound rs)))))
  (k-unseen-arms (subr (maxeff kstate spin) (k-arms k-names k-regions) k-regions)
    (lambda (arms bound rs)
      (if (null? arms)
          rs
          (let ((arm (car arms)))
            (k-unseen-arms (cdr arms) bound
                           (k-unseen (extract arm 4) (k-names-onto (extract arm 3) bound) rs))))))
  ;; A `tagcase`'s `else` arm, if any, its variable bound.
  (k-unseen-else (subr (maxeff kstate spin) (k-let-bs k-names k-regions) k-regions)
    (lambda (els bound rs)
      (if (null? els)
          rs
          (k-unseen (extract (car els) 2) (cons (extract (car els) 1) bound) rs)))))

;; What stays of `e`: an atom on a region no free variable sees goes.
(define k-keep (subr (maxeff kmakes spin) (k-eff k-regions k-regions) k-eff)
  (lambda (e unseen in-result)
    (if (null? e)
        nil
        (let* ((a (car e)) (rest (k-keep (cdr e) unseen in-result)))
          (cond ((not (k-has-region? a)) (cons a rest))
                ((k-unplaced-frozen-atom? a) (cons a rest))
                ((not (k-has-region-in? unseen (k-mask-region a))) (cons a rest))
                ((k-stays-for-result? a in-result) (cons a rest))
                (else rest))))))

;; Note that region variable `v` is written, if a `letfreeze` is freezing
;; it.
(define k-note-written (subr kstate (int) unit)
  (lambda (v)
    (if (and (k-has-id? (get k-freezing) v) (not (k-has-id? (get k-written) v)))
        (set k-written (cons v (get k-written)))
        #u)))
;; A write to a region a `letfreeze` is freezing, noted before masking could
;; hide it: that region's data may be cyclic.
(define k-note-writes (subr kstate (k-eff) unit)
  (lambda (e)
    (if (null? e)
        #u
        (begin
          (tagcase (car e)
            (a-write (r) (tagcase r (r-var (v) (k-note-written v)) (else y #u)))
            (else x #u))
          (k-note-writes (cdr e))))))
(define k-mask (subr (maxeff kstate spin) (kx k-eff int) k-eff)
  (lambda (x e result)
    (if (begin (k-note-writes e) (null? e))
        e
        (let* ((in-result (k-regions-in result))
               (sought (k-sought e in-result nil)))
          (if (null? sought)
              e
              (k-keep e (k-unseen x nil sought) in-result))))))))

(define k-frozen-atom? (with check-mask-module k-frozen-atom?))
(define k-mask (with check-mask-module k-mask))
