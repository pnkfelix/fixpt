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
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (check-sub-env-types (load-module "fx26:check-sub-env-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-print (select check-print-types check-print-sig))
           (check-expect (select check-expect-types check-expect-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig))
           (check-sub-env (select check-sub-env-types check-sub-env-sig)))
    (module

;; The types it uses of the files before it.
(hide (include check-types-types))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-print-parts) (include check-print)
      (include check-expect) (include check-effects) (include check-subst))

;; Data, and what a wider bloblet type may forget: `check-sub-env.fx`'s,
;; which the subtype test, before this file, asks.
(define k-data-place (with check-sub-env k-data-place))
(define k-data-var-place (with check-sub-env k-data-var-place))
(define k-is-data? (with check-sub-env k-is-data?))
(define k-is-data-at? (with check-sub-env k-is-data-at?))

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
