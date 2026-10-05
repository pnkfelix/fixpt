;;; The checker, in FX-26: what synthesis needs of regions that close, of
;;; writes, and of frozen data. Part of the checker, `check-types.fx` first
;;; (moved out of `check-infer.fx`, 2026-10-04).

;;; ------------------------------------------------------------ synthesis

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-close-module (module
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
              (ty-pair (a b x) (or (k-writes-in a r seen) (k-writes-in b r seen)))
              (ty-bloblet (fs z x) (k-writes-list fs r seen))
              (ty-product (ps) (k-writes-parts ps r seen))
              (ty-sum (ps) (k-writes-parts ps r seen))
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
          (k-subst t (the k-map (cons (cons r (dr frozen)) nil)))))))))

(define k-close-region (with check-close-module k-close-region))
(define k-note-effect (with check-close-module k-note-effect))
(define k-frozen (with check-close-module k-frozen))
(define k-frozen-result (with check-close-module k-frozen-result))
