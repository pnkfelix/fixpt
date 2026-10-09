;;; The checker, in FX-26: what synthesis needs of regions that close, of
;;; writes, and of frozen data. Part of the checker, `check-types.fx` first
;;; (moved out of `check-infer.fx`, 2026-10-04).

;;; ------------------------------------------------------------ synthesis

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-holds-types (load-module "fx26:check-holds-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-mask-types (load-module "fx26:check-mask-types.fx"))
       (check-calls-types (load-module "fx26:check-calls-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-holds (select check-holds-types check-holds-sig))
           (check-env (select check-env-types check-env-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (check-mask (select check-mask-types check-mask-sig))
           (check-calls (select check-calls-types check-calls-sig))
           (check-print (select check-print-types check-print-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module

;; The types it uses of the files before it.
(define a-var (with check-types-types a-var))
(define a-write (with check-types-types a-write))
(define-effect checks (select check-types-types checks))
(define de (with check-types-types de))
(define df (with check-types-types df))
(define dr (with check-types-types dr))
(define-type k-atom (select check-types-types k-atom))
(define-type k-desc (select check-types-types k-desc))
(define-type k-descs (select check-types-types k-descs))
(define-type k-eff (select check-types-types k-eff))
(define-type k-ids (select check-types-types k-ids))
(define-type k-map (select check-types-types k-map))
(define-type k-parts (select check-types-types k-parts))
(define-type k-region (select check-types-types k-region))
(define-type k-te (select check-types-types k-te))
(define-effect kreads (select check-types-types kreads))
(define-effect kstate (select check-types-types kstate))
(define-type kx (select check-types-types kx))
(define r-frozen (with check-types-types r-frozen))
(define r-var (with check-types-types r-var))
(define ty-app (with check-types-types ty-app))
(define ty-array (with check-types-types ty-array))
(define ty-bloblet (with check-types-types ty-bloblet))
(define ty-comp (with check-types-types ty-comp))
(define ty-icell (with check-types-types ty-icell))
(define ty-lam (with check-types-types ty-lam))
(define ty-markkey (with check-types-types ty-markkey))
(define ty-named (with check-types-types ty-named))
(define ty-nlist (with check-types-types ty-nlist))
(define ty-pair (with check-types-types ty-pair))
(define ty-poly (with check-types-types ty-poly))
(define ty-product (with check-types-types ty-product))
(define ty-ref (with check-types-types ty-ref))
(define ty-subr (with check-types-types ty-subr))
(define ty-sum (with check-types-types ty-sum))
(define ty-tag (with check-types-types ty-tag))
(define ty-union (with check-types-types ty-union))
(define-type k-facts (select check-env-types k-facts))
(define-effect kmakes (select check-subst-types kmakes))
;; What it uses of the modules it is given.
(define k-cat3 (with check-types k-cat3))
(define k-cat4 (with check-types k-cat4))
(define k-dvar-name (with check-types k-dvar-name))
(define k-fail (with check-types k-fail))
(define k-gen-of (with check-types k-gen-of))
(define k-gen-param? (with check-types k-gen-param?))
(define k-gen-region? (with check-types k-gen-region?))
(define k-get (with check-types k-get))
(define k-new-epoch (with check-types k-new-epoch))
(define k-resolve (with check-types k-resolve))
(define k-te (with check-types k-te))
(define k-visit? (with check-types k-visit?))
(define k-atom-rank (with check-effects k-atom-rank))
(define k-atom-region (with check-effects k-atom-region))
(define k-region=? (with check-effects k-region=?))
(define k-ds-types (with check-holds k-ds-types))
(define k-effect-notes (with check-env k-effect-notes))
(define k-summary (with check-env k-summary))
(define k-end (with check-resolve k-end))
(define k-has-region-in? (with check-resolve k-has-region-in?))
(define k-regions-in (with check-resolve k-regions-in))
(define k-start (with check-resolve k-start))
(define k-frozen-atom? (with check-mask k-frozen-atom?))
(define k-mask (with check-mask k-mask))
(define k-has-comefrom? (with check-calls k-has-comefrom?))
(define k-show-effect (with check-print-parts k-show-effect))
(define k-show-ty (with check-print k-show-ty))
(define k-subst (with check-subst k-subst))

;; `(letrena r …)`'s or `(letreap r …)`'s body, of type `t` and effect `e`,
;; closed: its value
;; may not mention `r`, and no continuation captured in it may outlive it;
;; what it does to `r` is masked, as nothing outside can name `r`.
(define k-close-region (subr (maxeff checks spin) (kx string int int k-eff int int) k-te)
  (lambda (x form r t e a b)
    (let ((name (k-cat3 form " " (symbol->string (k-dvar-name r)))))
      (if (k-has-region-in? (k-regions-in t) (r-var r))
          (k-fail (k-cat4 "the value of `" name "` would outlive its region: its type is "
                          (k-show-ty t))
                  a b)
          (let ((masked (k-mask x e t)))
            (if (k-has-comefrom? masked)
                (k-fail (k-cat4 "a continuation captured in `" name
                                "` could outlive its region: its effect is "
                                (k-show-effect masked))
                        a b)
                (k-te t masked)))))))

;; Whether an effect writes region `r`.
(define k-eff-writes? (subr (maxeff kreads spin) (k-eff k-region) bool)
  (lambda (e r)
    (and (not (null? e))
         (or (tagcase (car e) (a-write (x) (k-region=? x r)) (else y #f))
             (k-eff-writes? (cdr e) r)))))
;; A generative type's representation writing one of its parameters writes
;; whatever it was given: cautiously, any region given any. Whether some
;; effect in a walk wrote a parameter, and whether some generative type was
;; given the region.
(define k-wrote-param (ref bool @t) (new #f))
(define k-given (ref bool @t) (new #f))
(define k-eff-writes-param? (subr kreads (k-eff) bool)
  (lambda (e)
    (and (not (null? e))
         (or (tagcase (car e)
               (a-write (x) (k-gen-region? x))
               (a-var (v) (k-gen-param? v))
               (else y #f))
             (k-eff-writes-param? (cdr e))))))
(define k-eff-writes-noting? (subr (maxeff kstate spin) (k-eff k-region) bool)
  (lambda (e r)
    (begin
      (if (k-eff-writes-param? e) (set k-wrote-param #t) #u)
      (k-eff-writes? e r))))
;; Whether description `d` writes `r`: is it, writes it, or is a function
;; whose body does.
(define k-d-writes? (subr (maxeff kreads spin) (k-desc k-region) bool)
  (lambda (d r)
    (tagcase d
      (dr (x) (k-region=? x r))
      (de (e) (k-eff-writes? e r))
      (df (f) (tagcase (k-get f) (ty-lam (bs body) (k-d-writes? body r)) (else y #f)))
      (else y #f))))
;; Whether any of `ds` writes `r`.
(define k-ds-write? (subr (maxeff kreads spin) (k-descs k-region) bool)
  (lambda (ds r) (and (not (null? ds)) (or (k-d-writes? (car ds) r) (k-ds-write? (cdr ds) r)))))
(define k-note-given (subr (maxeff kstate spin) (k-descs k-region) unit)
  (lambda (ds r) (if (k-ds-write? ds r) (set k-given #t) #u)))
;; Whether a latent effect anywhere in `t` writes `r`: what a `letfreeze`'s
;; value may not do to its region.
(define-rec
  (k-writes-in (subr (maxeff kstate spin) (int k-region int) bool)
    (lambda (t r seen)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #f
            (tagcase (k-get t)
              (ty-subr (e ps x cv)
                (or (k-eff-writes-noting? e r) (k-writes-list ps r seen) (k-writes-in x r seen)))
              (ty-tag (a h e x)
                (or (k-eff-writes-noting? e r) (k-writes-in a r seen) (k-writes-in h r seen)))
              (ty-comp (b a e x)
                (or (k-eff-writes-noting? e r) (k-writes-in a r seen) (k-writes-in b r seen)))
              (ty-poly (bs body) (k-writes-in body r seen))
              (ty-ref (a x) (k-writes-in a r seen))
              (ty-array (a x) (k-writes-in a r seen))
              (ty-icell (a x) (k-writes-in a r seen))
              (ty-markkey (a x) (k-writes-in a r seen))
              (ty-pair (a b x nl) (or (k-writes-in a r seen) (k-writes-in b r seen)))
              (ty-bloblet (fs z x) (k-writes-list fs r seen))
              (ty-product (ps) (k-writes-parts ps r seen))
              (ty-sum (ps) (k-writes-parts ps r seen))
              (ty-union (ms) (k-writes-list ms r seen))
              (ty-nlist (e z x) (k-writes-in e r seen))
              (ty-named (g ds)
                (begin (k-note-given ds r)
                       (or (k-writes-in (extract (k-gen-of g) 4) r seen)
                           (k-writes-list (k-ds-types ds) r seen))))
              ;; A description function applied, unseen: it may write
              ;; whatever it was given.
              (ty-app (f ds)
                (begin (if (k-ds-write? ds r) (begin (set k-given #t) (set k-wrote-param #t)) #u)
                       (k-writes-list (k-ds-types ds) r seen)))
              (else x #f))))))
  (k-writes-list (subr (maxeff kstate spin) (k-ids k-region int) bool)
    (lambda (ts r seen)
      (and (not (null? ts)) (or (k-writes-in (car ts) r seen) (k-writes-list (cdr ts) r seen)))))
  (k-writes-parts (subr (maxeff kstate spin) (k-parts k-region int) bool)
    (lambda (ps r seen)
      (and (not (null? ps))
           (or (k-writes-in (extract (car ps) 2) r seen) (k-writes-parts (cdr ps) r seen))))))

(define k-any-frozen? (subr kreads (k-eff) bool)
  (lambda (e) (and (not (null? e)) (or (k-frozen-atom? (car e)) (k-any-frozen? (cdr e))))))
(define k-writes-frozen? (subr kreads (k-eff) bool)
  (lambda (e)
    (and (not (null? e))
         (or (and (k-frozen-atom? (car e)) (= (k-atom-rank (car e)) 1))
             (k-writes-frozen? (cdr e))))))
;; Whether an atom reads, allocates or awaits data frozen in the heap,
;; which never ends: that is pure.
(define k-pure-on-const? (subr (read @globals) (k-atom) bool)
  (lambda (a)
    (and (k-frozen-atom? a)
         (let ((k (k-atom-rank a))) (or (= k 0) (or (= k 2) (= k 5))))
         (tagcase (k-atom-region a) (r-frozen (p f) (< p 0)) (else y #f)))))
;; `e` without its reads, allocations and awaits on `const`, which are pure.
(define k-drop-frozen (subr kmakes (k-eff) k-eff)
  (lambda (e)
    (cond ((null? e) nil)
          ;; Only data frozen in the heap, which never ends; what is done to
          ;; data frozen into a place stays, until masking removes it.
          ((k-pure-on-const? (car e)) (k-drop-frozen (cdr e)))
          (else (cons (car e) (k-drop-frozen (cdr e)))))))
;; `x`'s effect `e`, noted.
(define k-note-effect (subr kstate (kx k-eff) unit)
  (lambda (x e)
    (let ((fact (product (1 (k-start x)) (2 (k-end x)) (3 (k-summary e)))))
      (set k-effect-notes (the k-facts (cons fact (get k-effect-notes)))))))
;; `e`, the effect of `x`, with what it does to frozen data taken out; or an
;; error, if it writes it.
(define k-frozen (subr checks (kx k-eff) k-eff)
  (lambda (x e)
    (cond ((not (k-any-frozen? e)) e)
          ((k-writes-frozen? e)
           (k-fail "this writes frozen data, whose region is `const`" (k-start x) (k-end x)))
          (else (k-drop-frozen e)))))

;; A `letfreeze r`'s value, of type `t`, as it leaves: `r` made `const`,
;; unless something in it could still write `r`.
(define k-frozen-result (subr (maxeff checks spin) (int k-region bool int int int) int)
  (lambda (r into written t a b)
    (if (begin (set k-wrote-param #f) (set k-given #f)
               (or (k-writes-in t (r-var r) (k-new-epoch)) (and (get k-wrote-param) (get k-given))))
        (k-fail (k-cat4 "the value of `letfreeze " (symbol->string (k-dvar-name r))
                        "` could still write its region's data: its type is " (k-show-ty t))
                a b)
        (let ((frozen (tagcase into (r-frozen (p f) (r-frozen p (not written))) (else y into))))
          (k-subst t (the k-map (cons (cons r (dr frozen)) nil))))))))))
