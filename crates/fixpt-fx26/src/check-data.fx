;;; The `data` kind (`docs/fx26.md`, "The `data` kind"): what a `data`
;;; binder takes, and at which place. `(t data p)` takes data whose frozen
;;; parts are in the heap or in place `p`; plain `(t data)`, data in the heap
;;; only (`docs/research/shapes.md`; `soundness-findings.md`, F13). The
;;; Rust checker's `is_data`, `is_data_at` and `data_places`, rule for rule.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-expect-types (load-module "fx26:check-expect-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-print (select check-print-types check-print-sig))
           (check-expect (select check-expect-types check-expect-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module

;; The types it uses of the files before it.
(define-effect checks (select check-types-types checks))
(define dr (with check-types-types dr))
(define dt (with check-types-types dt))
(define-type k-binders (select check-types-types k-binders))
(define-type k-desc (select check-types-types k-desc))
(define-type k-ids (select check-types-types k-ids))
(define-type k-map (select check-types-types k-map))
(define-type k-parts (select check-types-types k-parts))
(define-type k-region (select check-types-types k-region))
(define-type k-regions (select check-types-types k-regions))
(define-effect kreads (select check-types-types kreads))
(define-effect kstate (select check-types-types kstate))
(define r-frozen (with check-types-types r-frozen))
(define r-heap (with check-types-types r-heap))
(define r-var (with check-types-types r-var))
(define ty-base (with check-types-types ty-base))
(define ty-bloblet (with check-types-types ty-bloblet))
(define ty-nat (with check-types-types ty-nat))
(define ty-nil (with check-types-types ty-nil))
(define ty-nlist (with check-types-types ty-nlist))
(define ty-pair (with check-types-types ty-pair))
(define ty-product (with check-types-types ty-product))
(define ty-sum (with check-types-types ty-sum))
(define ty-union (with check-types-types ty-union))
(define ty-var (with check-types-types ty-var))
(define ty-void (with check-types-types ty-void))
;; What it uses of the modules it is given.
(define k-bound-of (with check-types k-bound-of))
(define k-cat3 (with check-types k-cat3))
(define k-cat4 (with check-types k-cat4))
(define k-cat5 (with check-types k-cat5))
(define k-data-var? (with check-types k-data-var?))
(define k-fail (with check-types k-fail))
(define k-get (with check-types k-get))
(define k-new-epoch (with check-types k-new-epoch))
(define k-resolve (with check-types k-resolve))
(define k-visit? (with check-types k-visit?))
(define k-map-find (with check-print-parts k-map-find))
(define k-region-show (with check-print-parts k-region-show))
(define k-show-ty (with check-print k-show-ty))
(define k-quote-dvar (with check-expect k-quote-dvar))
(define k-region=? (with check-effects k-region=?))
(define k-subst-region (with check-subst k-subst-region))

;; Whether `r` is frozen data's region.
(define k-frozen-region? (subr pure (k-region) bool)
  (lambda (r) (tagcase r (r-frozen (p f) #t) (else y #f))))
;; Where data at region `r` is: the place it is frozen into, or the place or
;; region it was made at, or else the heap.
(define* k-data-place (subr pure (k-region) k-region)
  (lambda (r)
    (tagcase r
      (r-frozen (p f) (if (< p 0) (r-heap) (r-var p)))
      (r-var (v) (r-var v))
      (else y (r-heap)))))
;; Where the data a `data` variable stands for is: its bound, or the heap.
(define* k-data-var-place (subr (maxeff kreads (alloc @t)) (int) k-region)
  (lambda (v) (let ((b (k-bound-of v))) (if (null? b) (r-heap) (car b)))))
;; Whether data at `q` may be taken where data at `place` is wanted: `place`
;; empty for anywhere, or else the heap or the one place it holds.
(define* k-data-here? (subr (maxeff (read @globals) spin) (k-regions k-region) bool)
  (lambda (place q) (or (null? place) (k-region=? q (r-heap)) (k-region=? q (car place)))))

;; Whether `t` is data: built only from base types, `datum`, products and
;; sums, and pairs and bloblets that are frozen, of data; and type variables
;; of kind `data`. With `place` naming one, each frozen part is also in the
;; heap or in that place.
(define-rec
  (k-data-walk (subr (maxeff kstate spin) (int int k-regions) bool)
    (lambda (t seen place)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #t
            (tagcase (k-get t)
              (ty-base (s) #t)
              (ty-void () #t)
              (ty-var (v) (and (k-data-var? v) (k-data-here? place (k-data-var-place v))))
              (ty-product (ps) (k-data-parts ps seen place))
              (ty-sum (ps) (k-data-parts ps seen place))
              (ty-nil () #t)
              (ty-union (ms) (k-data-list ms seen place))
              (ty-pair (a b r nl)
                (and (k-frozen-region? r) (k-data-here? place (k-data-place r))
                     (k-data-walk a seen place) (k-data-walk b seen place)))
              (ty-bloblet (fs z r)
                (and z (k-data-here? place (k-data-place r)) (k-data-list fs seen place)))
              (ty-nlist (e z r)
                (and (k-data-here? place (k-data-place r)) (k-data-walk e seen place)))
              (ty-nat (z) #t)
              (else y #f))))))
  (k-data-parts (subr (maxeff kstate spin) (k-parts int k-regions) bool)
    (lambda (ps seen place)
      (or (null? ps)
          (and (k-data-walk (extract (car ps) 2) seen place) (k-data-parts (cdr ps) seen place)))))
  (k-data-list (subr (maxeff kstate spin) (k-ids int k-regions) bool)
    (lambda (ts seen place)
      (or (null? ts) (and (k-data-walk (car ts) seen place) (k-data-list (cdr ts) seen place))))))
(define k-is-data? (subr (maxeff kstate spin) (int) bool)
  (lambda (t) (k-data-walk t (k-new-epoch) nil)))
;; Whether `t` is data at `place`, a place variable or the heap.
(define k-is-data-at? (subr (maxeff kstate spin) (int k-region) bool)
  (lambda (t place) (k-data-walk t (k-new-epoch) (the k-regions (cons place nil)))))

(define k-region-in? (subr (maxeff (read @globals) spin) (k-regions k-region) bool)
  (lambda (rs q) (and (not (null? rs)) (or (k-region=? (car rs) q) (k-region-in? (cdr rs) q)))))
;; `q` added to `out`, unless it is the heap or there already.
(define* k-note-place (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin)
                            ((ref k-regions @t) k-region) unit)
  (lambda (out q)
    (if (or (k-region=? q (r-heap)) (k-region-in? (get out) q))
        #u
        (set out (cons q (get out))))))
;; The places, other than the heap, that data `t`'s parts are in, into `out`.
(define-rec
  (k-data-places (subr (maxeff kstate spin) (int int (ref k-regions @t)) unit)
    (lambda (t seen out)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #u
            (tagcase (k-get t)
              (ty-var (v) (if (k-data-var? v) (k-note-place out (k-data-var-place v)) #u))
              (ty-product (ps) (k-data-places-parts ps seen out))
              (ty-sum (ps) (k-data-places-parts ps seen out))
              (ty-union (ms) (k-data-places-list ms seen out))
              (ty-pair (a b r nl)
                (begin (k-note-place out (k-data-place r)) (k-data-places a seen out)
                       (k-data-places b seen out)))
              (ty-bloblet (fs z r)
                (begin (k-note-place out (k-data-place r)) (k-data-places-list fs seen out)))
              (ty-nlist (e z r)
                (begin (k-note-place out (k-data-place r)) (k-data-places e seen out)))
              (else y #u))))))
  (k-data-places-parts (subr (maxeff kstate spin) (k-parts int (ref k-regions @t)) unit)
    (lambda (ps seen out)
      (if (null? ps)
          #u
          (begin (k-data-places (extract (car ps) 2) seen out)
                 (k-data-places-parts (cdr ps) seen out)))))
  (k-data-places-list (subr (maxeff kstate spin) (k-ids int (ref k-regions @t)) unit)
    (lambda (ts seen out)
      (if (null? ts)
          #u
          (begin (k-data-places (car ts) seen out) (k-data-places-list (cdr ts) seen out))))))

;; The variable a binder's bound names, or -1.
(define k-bound-var (subr pure (k-regions) int)
  (lambda (bd) (if (null? bd) -1 (tagcase (car bd) (r-var (p) p) (else y -1)))))
;; The type a description is, or -1.
(define k-desc-type-id (subr pure (k-desc) int)
  (lambda (d) (tagcase d (dt (t) t) (else z -1))))
;; Whether `v` is among binders `bs`.
(define k-binder-in? (subr (read @globals) (k-binders int) bool)
  (lambda (bs v)
    (and (not (null? bs)) (or (= (extract (car bs) 1) v) (k-binder-in? (cdr bs) v)))))
;; `m` with place binder `p` solved as where data `t` is: the one place its
;; parts are in, or the heap; unsolved if they are in two.
(define* k-solve-data-place (subr (maxeff checks spin) (int int k-map) k-map)
  (lambda (p t m)
    (let ((out (the (ref k-regions @t) (new nil))))
      (begin
        (k-data-places t (k-new-epoch) out)
        (let ((ps (get out)))
          (cond ((null? ps) (cons (cons p (dr (r-heap))) m))
                ((null? (cdr ps)) (cons (cons p (dr (car ps))) m))
                (else m)))))))
;; `m`, with each `data` binder's place that nothing else says solved as where
;; its data is (F13).
(define* k-data-places-solved (subr (maxeff checks spin) (k-binders k-binders k-map) k-map)
  (lambda (kinds all m)
    (if (null? kinds)
        m
        (let* ((v (extract (car kinds) 1))
               (p (if (= (extract (car kinds) 2) 4) (k-bound-var (k-bound-of v)) -1))
               (f (k-map-find m v))
               (t (if (null? f) -1 (k-desc-type-id (cdr (car f))))))
          (k-data-places-solved
           (cdr kinds) all
           (if (and (>= p 0) (>= t 0) (null? (k-map-find m p)) (k-binder-in? all p))
               (k-solve-data-place p t m)
               m))))))
;; `data` binder `v`, bound `bd`, as `m` solves it, takes only data, at its
;; place; or an error.
(define* k-check-data (subr (maxeff checks spin) (int k-regions k-map int int) unit)
  (lambda (v bd m a b)
    (let* ((f (k-map-find m v))
           (t (if (null? f) -1 (k-desc-type-id (cdr (car f)))))
           (place (k-subst-region (if (null? bd) (r-heap) (car bd)) m)))
      (cond ((< t 0) #u)
            ((not (k-is-data? t))
             (k-fail (k-cat4 (k-quote-dvar v) " is bound as data, and a " (k-show-ty t)
                             " is not data")
                     a b))
            ((not (k-is-data-at? t place))
             (k-fail (k-cat5 (k-quote-dvar v) " is bound as data at " (k-region-show place)
                             ", and a " (k-cat3 (k-show-ty t) " is data in another place" ""))
                     a b))
            (else #u))))))))
