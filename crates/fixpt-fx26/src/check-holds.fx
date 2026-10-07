;;; The checker, in FX-26: what a type holds: where a procedure kept in it
;;; could reach itself, and at which polarities a variable occurs in it.
;;; Split from `check-print.fx`, after it (2026-10-06). Part of the checker,
;;; `check-types.fx` first (PLAN.md §11, step 10).

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-holds-module (module
;; Regions storage is kept in, for `k-knot-in`.
(define-type k-kept (listof k-region acyclic))
;; The types in description `d`, for analyses that look through what a
;; value holds: a type itself, or a `dlambda`'s body's (its parameters
;; standing for what it is given).
(define k-d-types (subr (maxeff kreads spin) (k-desc) k-ids)
  (lambda (d)
    (tagcase d
      (dt (t) (the k-ids (cons t nil)))
      (df (f) (tagcase (k-get f) (ty-lam (bs body) (k-d-types body)) (else y nil)))
      (else y nil))))
;; `xs` before `ys`.
(define k-ids-onto (subr (maxeff (read @globals) (alloc @t)) (k-ids k-ids) k-ids)
  (lambda (xs ys) (if (null? xs) ys (the k-ids (cons (car xs) (k-ids-onto (cdr xs) ys))))))
;; The types in descriptions `ds`, each as `k-d-types` finds them.
(define k-ds-types (subr (maxeff kreads (alloc @t) spin) (k-descs) k-ids)
  (lambda (ds) (if (null? ds) nil (k-ids-onto (k-d-types (car ds)) (k-ds-types (cdr ds))))))
(define k-kept-has? (subr (maxeff kreads spin) (k-kept k-region) bool)
  (lambda (rs r) (and (not (null? rs)) (or (k-region=? (car rs) r) (k-kept-has? (cdr rs) r)))))
(define k-kept-add (subr kbuilds (k-kept k-region) k-kept)
  (lambda (rs r) (if (k-kept-has? rs r) rs (cons r rs))))
;; Whether `r` is the region of frozen data.
(define k-frozen? (subr pure (k-region) bool)
  (lambda (r) (tagcase r (r-frozen (q f) #t) (else y #f))))
;; The regions of everything in `t` that can be written: storage a
;; generative type's representation may keep what it was given in.
(define-rec
  (k-storage-walk (subr (maxeff kstate spin) (int int (ref k-kept @t)) unit)
    (lambda (t seen out)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #u
            (letrec ((add (subr (maxeff kstate spin) (k-region) unit)
                          (lambda (r) (set out (k-kept-add (get out) r))))
                     (walk (subr (maxeff kstate spin) (int) unit)
                           (lambda (x) (k-storage-walk x seen out)))
                     (walks (subr (maxeff kstate spin) (k-ids) unit)
                            (lambda (xs) (k-storage-walks xs seen out))))
              (tagcase (k-get t)
                (ty-ref (a r) (begin (add r) (walk a)))
                (ty-array (a r) (begin (add r) (walk a)))
                (ty-icell (a r) (begin (add r) (walk a)))
                (ty-markkey (a r) (begin (add r) (walk a)))
                (ty-pair (a b r) (begin (if (k-frozen? r) #u (add r)) (walk a) (walk b)))
                (ty-bloblet (fs z r) (begin (if z #u (add r)) (walks fs)))
                (ty-subr (e ps r cv) (begin (walks ps) (walk r)))
                (ty-poly (bs body) (walk body))
                (ty-product (ps) (k-storage-parts ps seen out))
                (ty-sum (ps) (k-storage-parts ps seen out))
                (ty-tag (a h e r) (begin (walk a) (walk h)))
                (ty-comp (b a e r) (begin (walk b) (walk a)))
                (ty-named (g ds) (begin (walk (extract (k-gen-of g) 4)) (walks (k-desc-types ds))))
                (ty-nlist (e z r) (walk e))
                (ty-app (f ds) (walks (k-ds-types ds)))
                (else x #u)))))))
  (k-storage-walks (subr (maxeff kstate spin) (k-ids int (ref k-kept @t)) unit)
    (lambda (ts seen out)
      (if (null? ts)
          #u
          (begin (k-storage-walk (car ts) seen out) (k-storage-walks (cdr ts) seen out)))))
  (k-storage-parts (subr (maxeff kstate spin) (k-parts int (ref k-kept @t)) unit)
    (lambda (ps seen out)
      (if (null? ps)
          #u
          (begin (k-storage-walk (extract (car ps) 2) seen out)
                 (k-storage-parts (cdr ps) seen out))))))
(define k-storage-regions (subr (maxeff kstate spin) (int) k-kept)
  (lambda (t)
    (let ((out (the (ref k-kept @t) (new nil))))
      (begin (k-storage-walk t (k-new-epoch) out) (get out)))))
;; `kept`, and each of `rs` that is not a generative type's parameter nor
;; frozen.
(define k-kept-extend (subr kbuilds (k-kept k-regions) k-kept)
  (lambda (kept rs)
    (cond ((null? rs) kept)
          ((or (k-gen-region? (car rs)) (k-frozen? (car rs))) (k-kept-extend kept (cdr rs)))
          (else (k-kept-extend (k-kept-add kept (car rs)) (cdr rs))))))
(define k-append-regions (subr (maxeff (read @globals) (alloc @t)) (k-regions k-regions) k-regions)
  (lambda (xs ys)
    (if (null? xs) ys (the k-regions (cons (car xs) (k-append-regions (cdr xs) ys))))))
;; Whether `a` reads or awaits a region `kept` has.
;; `@globals` among the regions kept stands for every region (no procedure
;; is kept in globals' bindings).
(define k-reads-in? (subr (maxeff kreads spin) (k-kept k-atom) bool)
  (lambda (kept a)
    (letrec ((in? (subr (maxeff kreads spin) (k-region) bool)
                  (lambda (r)
                    (or (k-kept-has? kept r)
                        (and (k-kept-has? kept (r-globals)) (not (k-frozen? r))
                             (not (k-globals-region? r)))))))
      (tagcase a (a-read (r) (in? r)) (a-await (r) (in? r)) (else y #f)))))
;; The region of the first of `xs` that reads or awaits one `kept` has,
;; alone in a list; none if none does.
(define k-first-read-in (subr kbuilds (k-kept k-eff) k-regions)
  (lambda (kept xs)
    (cond ((null? xs) (the k-regions nil))
          ((k-reads-in? kept (car xs)) (the k-regions (cons (k-atom-region (car xs)) nil)))
          (else (k-first-read-in kept (cdr xs))))))
;; Whether `t` keeps, in storage at some region `r`, a procedure whose
;; latent effect reads or awaits `r` and does not say `spin`: a knot tied
;; through the store, a loop with no recursive call, which only its type can
;; show. The region and the procedure's type, if so.
(define k-reads-kept (subr kbuilds (k-eff k-kept) k-regions)
  (lambda (e kept)
    (if (k-contains? e (a-spin)) (the k-regions nil) (k-first-read-in kept e))))
(define k-kept-same? (subr (maxeff kreads spin) (k-kept k-kept) bool)
  (lambda (x y)
    (letrec ((within (subr (maxeff kreads spin) (k-kept k-kept) bool)
               (lambda (a b) (or (null? a) (and (k-kept-has? b (car a)) (within (cdr a) b))))))
      (and (within x y) (within y x)))))
(define-type k-knot (listof (pairof k-region int @t) acyclic))
;; The types a search for a knot has met, each with what it found kept.
(define-type k-kept-seen (listof (pairof int k-kept @t) acyclic))
(define-type k-kseen (ref k-kept-seen @t))
(define k-kseen-has? (subr (maxeff kreads spin) (k-kept-seen int k-kept) bool)
  (lambda (xs t kept)
    (and (not (null? xs))
         (or (and (= (car (car xs)) t) (k-kept-same? (cdr (car xs)) kept))
             (k-kseen-has? (cdr xs) t kept)))))
(define-rec
  (k-knot-in (subr (maxeff kstate spin) (int k-kept k-kseen) k-knot)
    (lambda (t kept seen)
      (let ((t (k-resolve t)))
        (if (k-kseen-has? (get seen) t kept)
            (the k-knot nil)
            (begin
              (set seen (cons (cons t kept) (get seen)))
              (tagcase (k-get t)
                (ty-ref (a r) (k-knot-in a (k-kept-add kept r) seen))
                (ty-array (a r) (k-knot-in a (k-kept-add kept r) seen))
                (ty-icell (a r) (k-knot-in a (k-kept-add kept r) seen))
                (ty-markkey (a r) (k-knot-in a (k-kept-add kept r) seen))
                (ty-pair (a b r)
                  (let ((k (if (k-frozen? r) kept (k-kept-add kept r))))
                    (k-knot-then (k-knot-in a k seen) b k seen)))
                (ty-bloblet (fs z r) (k-knot-list fs (if z kept (k-kept-add kept r)) seen))
                (ty-product (ps) (k-knot-parts ps kept seen))
                (ty-sum (ps) (k-knot-parts ps kept seen))
                (ty-poly (bs body) (k-knot-in body kept seen))
                ;; A procedure: kept where it is, it may not read there
                ;; unsaid; what it takes and gives is kept nowhere yet.
                (ty-subr (e ps r cv)
                  (let ((found (k-reads-kept e kept)))
                    (if (null? found)
                        (k-knot-then (k-knot-list ps nil seen) r nil seen)
                        (the k-knot (cons (cons (car found) t) nil)))))
                (ty-comp (x a e r)
                  (let ((found (k-reads-kept e kept)))
                    (if (null? found)
                        (k-knot-then (k-knot-in x nil seen) a nil seen)
                        (the k-knot (cons (cons (car found) t) nil)))))
                (ty-tag (a h e r) (k-knot-then (k-knot-in a nil seen) h nil seen))
                (ty-nlist (e z r) (k-knot-in e kept seen))
                ;; Transparent to safety: its representation, and what it
                ;; was given, kept, cautiously, wherever its representation
                ;; keeps anything and in every region it was given.
                (ty-named (g ds)
                  (let* ((rep (extract (k-gen-of g) 4))
                         (held (k-storage-regions rep))
                         (k (k-kept-extend kept (k-append-regions held (k-desc-regions ds))))
                         (x (k-knot-in rep kept seen)))
                    (if (null? x) (k-knot-list (k-desc-types ds) k seen) x)))
                ;; A module's abstract type constructor applied: its
                ;; representation, unseen, may keep what it was given
                ;; anywhere. A `poly`'s variable applied is checked as it is
                ;; instantiated.
                (ty-app (f ds)
                  (let ((anywhere (tagcase (k-get f)
                                    (ty-var (v) (k-has-id? (get k-abstract-funs) v))
                                    (else z #f))))
                    (k-knot-list (k-ds-types ds) (if anywhere (k-kept-add kept (r-globals)) kept)
                                 seen)))
                (else y (the k-knot nil))))))))
  ;; `x`, or, if that is none, the knot in `t`.
  (k-knot-then (subr (maxeff kstate spin) (k-knot int k-kept k-kseen) k-knot)
    (lambda (x t kept seen) (if (null? x) (k-knot-in t kept seen) x)))
  (k-knot-list (subr (maxeff kstate spin) (k-ids k-kept k-kseen) k-knot)
    (lambda (ts kept seen)
      (if (null? ts)
          (the k-knot nil)
          (let ((x (k-knot-in (car ts) kept seen)))
            (if (null? x) (k-knot-list (cdr ts) kept seen) x)))))
  (k-knot-parts (subr (maxeff kstate spin) (k-parts k-kept k-kseen) k-knot)
    (lambda (ps kept seen)
      (if (null? ps)
          (the k-knot nil)
          (let ((x (k-knot-in (extract (car ps) 2) kept seen)))
            (if (null? x) (k-knot-parts (cdr ps) kept seen) x))))))
;; What a procedure kept in region `r` that reads it there says, `t` its
;; type.
(define k-knot-message (subr (read @globals) (string string) string)
  (lambda (r t)
    (k-cat5 "a procedure kept in `" r "` reads `" r
            (string-append "`, so it could reach itself: it must say `spin`, and it is a " t))))
(define k-no-knot (subr (maxeff checks spin) (int int int) unit)
  (lambda (t a b)
    (let ((found (k-knot-in t nil (the k-kseen (new nil)))))
      (if (null? found)
          #u
          (let ((r (k-region-show (car (car found)))))
            (k-fail (k-knot-message r (k-show-ty (cdr (car found)))) a b))))))

;; Each polarity (0 covariant, 1 contravariant, 2 invariant) at which `v`
;; occurs in `t`, reached at polarity `at`.
(define k-flip (subr pure (int) int) (lambda (p) (case p ((0) 1) ((1) 0) (else 2))))
(define k-reg-is? (subr pure (k-region int) bool)
  (lambda (r v) (tagcase r (r-var (x) (= x v)) (r-frozen (x f) (= x v)) (else y #f))))
(define k-eff-var? (subr kreads (k-eff int) bool)
  (lambda (e v) (and (not (null? e)) (or (= (k-atom-var (car e)) v) (k-eff-var? (cdr e) v)))))
(define k-eff-region-var? (subr kreads (k-eff int) bool)
  (lambda (e v)
    (and (not (null? e))
         (or (and (k-has-region? (car e)) (k-reg-is? (k-atom-region (car e)) v))
             (k-eff-region-var? (cdr e) v)))))
(define k-eff-regions-of (subr (read @globals) (k-eff) k-regions)
  (lambda (e)
    (cond ((null? e) nil)
          ((k-has-region? (car e)) (cons (k-atom-region (car e)) (k-eff-regions-of (cdr e))))
          (else (k-eff-regions-of (cdr e))))))
;; The regions a description names outright: a region, an effect's atoms',
;; and a `dlambda`'s body's.
(define k-d-regions (subr (maxeff kreads spin) (k-desc) k-regions)
  (lambda (d)
    (tagcase d
      (dr (r) (the k-regions (cons r nil)))
      (de (e) (k-eff-regions-of e))
      (df (f) (tagcase (k-get f) (ty-lam (bs body) (k-d-regions body)) (else y nil)))
      (else y nil))))
;; The effects a description is or names: an effect, or a `dlambda`'s
;; body's.
(define k-d-effects (subr (maxeff kreads spin) (k-desc) (listof k-eff acyclic))
  (lambda (d)
    (tagcase d
      (de (e) (the (listof k-eff acyclic) (cons e nil)))
      (df (f) (tagcase (k-get f) (ty-lam (bs body) (k-d-effects body)) (else y nil)))
      (else y nil))))
(define k-terms-name? (subr (read @globals) (k-terms int) bool)
  (lambda (ts v) (and (not (null? ts)) (or (= (car (car ts)) v) (k-terms-name? (cdr ts) v)))))
;; Whether an effect application in `e` names variable `v`.
(define-rec
  (k-eff-app-var? (subr (maxeff kreads spin) (k-eff int) bool)
    (lambda (e v)
      (and (not (null? e))
           (or (tagcase (car e) (a-app (h ds) (k-app-mentions? h ds v)) (else y #f))
               (k-eff-app-var? (cdr e) v)))))
  (k-app-mentions? (subr (maxeff kreads spin) (int k-descs int) bool)
    (lambda (h ds v) (or (= h v) (k-eargs-mention? ds v))))
  (k-eargs-mention? (subr (maxeff kreads spin) (k-descs int) bool)
    (lambda (ds v)
      (and (not (null? ds))
           (or (tagcase (car ds)
                 (dr (r) (k-reg-is? r v))
                 (de (e) (or (k-eff-var? e v) (k-eff-region-var? e v) (k-eff-app-var? e v)))
                 (dz (z) (tagcase z (sz-lin (k ts) (k-terms-name? ts v)) (else y #f)))
                 (dc (c) (tagcase c (cv-var (w) (= w v)) (else y #f)))
                 (else y #f))
               (k-eargs-mention? (cdr ds) v))))))
(define k-regions-name? (subr (read @globals) (k-regions int) bool)
  (lambda (rs v) (and (not (null? rs)) (or (k-reg-is? (car rs) v) (k-regions-name? (cdr rs) v)))))
(define k-effs-name? (subr kreads ((listof k-eff acyclic) int) bool)
  (lambda (es v) (and (not (null? es)) (or (k-eff-var? (car es) v) (k-effs-name? (cdr es) v)))))
(define-rec
  ;; The kind of description function `f`, where it is known: -1 for a
  ;; `select` not yet resolved.
  (k-fun-kind (subr (maxeff kstate spin) (int) int)
    (lambda (f)
      (tagcase (k-get f)
        (ty-var (v) (k-dvar-kind v))
        (ty-lam (bs body)
          (let ((r (k-d-kind body))) (if (< r 0) -1 (k-arrow (k-binder-kinds bs) r))))
        ;; A function that gives a function, applied.
        (ty-app (g ds) (k-arrow-result (k-fun-kind g)))
        (else x -1))))
  ;; The kind a description is of, where it is known.
  (k-d-kind (subr (maxeff kstate spin) (k-desc) int)
    (lambda (d)
      (tagcase d
        (dr (r) (if (k-place? r) 3 0))
        (de (e) 1)
        (dt (t) 2)
        (dz (z) 5)
        (dc (c) 6)
        (df (f) (k-fun-kind f))))))
))

(define k-d-types (with check-holds-module k-d-types))
(define k-ds-types (with check-holds-module k-ds-types))
(define k-frozen? (with check-holds-module k-frozen?))
(define k-knot-in (with check-holds-module k-knot-in))
(define k-no-knot (with check-holds-module k-no-knot))
(define k-flip (with check-holds-module k-flip))
(define k-reg-is? (with check-holds-module k-reg-is?))
(define k-eff-var? (with check-holds-module k-eff-var?))
(define k-eff-region-var? (with check-holds-module k-eff-region-var?))
(define k-d-regions (with check-holds-module k-d-regions))
(define k-d-effects (with check-holds-module k-d-effects))
(define k-eff-app-var? (with check-holds-module k-eff-app-var?))
(define k-regions-name? (with check-holds-module k-regions-name?))
(define k-effs-name? (with check-holds-module k-effs-name?))
(define k-fun-kind (with check-holds-module k-fun-kind))
