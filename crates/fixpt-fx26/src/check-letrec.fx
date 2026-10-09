;;; A `letrec` group whose procedures read globals their types leave out:
;;; each one's type, with the globals it reads found, as `define*` finds them
;;; for a definition. The Rust checker's `letrec_with` and `letrec_found`,
;;; rule for rule.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-letrec-types (load-module "fx26:check-letrec-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-synth-types (load-module "fx26:check-synth-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-expect-types (load-module "fx26:check-expect-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-terminate-types (load-module "fx26:check-terminate-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-expect (select check-expect-types check-expect-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-print (select check-print-types check-print-sig))
           (check-env (select check-env-types check-env-sig))
           (check-terminate (select check-terminate-types check-terminate-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module
(define-type k-checker (select check-letrec-types k-checker))
(define-type k-group-checker (select check-letrec-types k-group-checker))
(define-type k-idss (select check-letrec-types k-idss))
;; The types it uses of the files before it.
(define a-read (with check-types-types a-read))
(define-effect checks (select check-types-types checks))
(define k-done (with check-types-types k-done))
(define-type k-eff (select check-types-types k-eff))
(define k-err (with check-types-types k-err))
(define-type k-ids (select check-types-types k-ids))
(define-type k-named (select check-types-types k-named))
(define-type k-te (select check-types-types k-te))
(define-effect kstate (select check-types-types kstate))
(define r-globals (with check-types-types r-globals))
(define ty-poly (with check-types-types ty-poly))
(define ty-subr (with check-types-types ty-subr))
(define-type k-done (select check-synth-types k-done))
(define-type k-letrec-bs (select check-resolve-types k-letrec-bs))
;; What it uses of the modules it is given.
(define k-fail (with check-types k-fail))
(define k-get (with check-types k-get))
(define k-recursive (with check-types k-recursive))
(define k-resolve (with check-types k-resolve))
(define k-tag (with check-types k-tag))
(define k-te (with check-types k-te))
(define k-ty-new (with check-types k-ty-new))
(define k-bind-letrec (with check-expect k-bind-letrec))
(define k-lambda? (with check-expect k-lambda?))
(define k-latent-of (with check-expect k-latent-of))
(define k-note-letrec (with check-expect k-note-letrec))
(define k-eff=? (with check-effects k-eff=?))
(define k-one (with check-effects k-one))
(define k-union (with check-effects k-union))
(define k-globals-atom? (with check-print-parts k-globals-atom?))
(define k-last-latent (with check-env k-last-latent))
(define k-mark (with check-env k-mark))
(define k-unbind-to (with check-env k-unbind-to))
(define k-letrec-lambdas (with check-terminate k-letrec-lambdas))
(define k-note-why (with check-terminate k-note-why))
(define k-termination (with check-terminate k-termination))

;; Note of the recursive group `bs` whether it needs `spin`, and why: `why`, "" if not.
(define k-note-ending (subr (maxeff kstate spin) (k-letrec-bs string) unit)
  (lambda (bs why)
    (let ((spins (not (string=? why ""))))
      (begin (k-note-letrec bs spins) (if spins (k-note-why bs why) #u)))))

;; `t`, a `subr` under any `poly`s, with `extra` in its latent effect; -1 if
;; `t` is not one.
(define k-with-latent (subr (maxeff kstate spin) (int k-eff) int)
  (lambda (t extra)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body)
        (let ((b (k-with-latent body extra))) (if (< b 0) -1 (k-ty-new (ty-poly bs b)))))
      (ty-subr (e ps r cv) (k-ty-new (ty-subr (k-union e extra) ps r cv)))
      (else y -1))))
;; The atoms of `e` on globals.
(define k-globals-of (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-eff) k-eff)
  (lambda (e)
    (cond ((null? e) nil)
          ((k-globals-atom? (car e)) (the k-eff (cons (car e) (k-globals-of (cdr e)))))
          (else (k-globals-of (cdr e))))))

;; Whether `ts` and `us` have the same latent effects, pairwise.
(define k-same-latents? (subr (maxeff kstate spin) (k-ids k-ids) bool)
  (lambda (ts us)
    (or (null? ts)
        (and (not (null? us))
             (let ((a (k-latent-of (car ts))) (b (k-latent-of (car us))))
               (if (null? a) (null? b) (and (not (null? b)) (k-eff=? (car a) (car b)))))
             (k-same-latents? (cdr ts) (cdr us))))))
;; `bs` at the types `ts`.
(define k-retyped (subr (read @globals) (k-letrec-bs k-ids) k-letrec-bs)
  (lambda (bs ts)
    (if (or (null? bs) (null? ts))
        nil
        (let ((b (car bs)))
          (the k-letrec-bs (cons (product (1 (extract b 1)) (2 (car ts)) (3 (extract b 3)))
                                 (k-retyped (cdr bs) (cdr ts))))))))
(define k-types-of (subr (read @globals) (k-letrec-bs) k-ids)
  (lambda (bs) (if (null? bs) nil (the k-ids (cons (extract (car bs) 2) (k-types-of (cdr bs)))))))
;; Group `bs` bound, known, and its termination noted.
(define* k-bind-group (subr (maxeff checks spin) (k-letrec-bs) unit)
  (lambda (bs)
    (begin (k-bind-letrec bs) (k-letrec-lambdas bs) (k-note-ending bs (k-termination bs)))))
;; Each of `bs` (bound at their types) checked as though its type said it
;; read any global; the declared types in `decl` with the globals each
;; body read. An error escapes.
(define* k-letrec-reads (subr (maxeff checks spin) (k-letrec-bs k-ids k-checker) k-ids)
  (lambda (bs decl check)
    (if (null? bs)
        nil
        (let* ((t (extract (car bs) 2))
               (w (k-with-latent t (k-one (a-read (r-globals)))))
               (e (check (extract (car bs) 3) (if (< w 0) t w)))
               (f (k-with-latent (car decl) (k-globals-of (get k-last-latent))))
               (found (if (< f 0) (car decl) f)))
          (the k-ids (cons found (k-letrec-reads (cdr bs) (cdr decl) check)))))))
;; What the last round found.
(define k-found-types (ref k-ids @t) (new nil))
(define* k-letrec-round (subr (maxeff checks spin) (k-letrec-bs k-ids k-checker) k-idss)
  (lambda (bs ts check)
    (let* ((saved (k-mark)) (rsaved (get k-recursive)) (group (k-retyped bs ts))
           (r (prompt k-tag
                (begin (k-bind-group group)
                       (set k-found-types (k-letrec-reads group (k-types-of bs) check))
                       (k-done (k-te 0 nil)))
                (lambda (r) r)))
           (ok (tagcase r (k-done (te) #t) (else y #f))))
      (begin (k-unbind-to saved) (set k-recursive rsaved)
             (if ok (the k-idss (cons (get k-found-types) nil)) nil)))))
;; Rounds from types `ts`, at most `n`, until the calls of each other add
;; no globals: the group at the types found; none if a round fails, or it
;; finds nothing new.
(define* k-letrec-found (subr (maxeff checks spin) (k-letrec-bs k-ids k-checker nat)
                              (listof k-letrec-bs acyclic))
  (lambda (bs ts check n)
    (if (= n 0)
        nil
        (let ((r (k-letrec-round bs ts check)))
          (cond ((null? r) nil)
                ((k-same-latents? (car r) ts)
                 (if (k-same-latents? (car r) (k-types-of bs))
                     nil
                     (the (listof k-letrec-bs acyclic) (cons (k-retyped bs (car r)) nil))))
                (else (k-letrec-found bs (car r) check (- n 1))))))))
(define k-all-lambdas? (subr (read @globals) (k-letrec-bs) bool)
  (lambda (bs) (or (null? bs) (and (k-lambda? (extract (car bs) 3)) (k-all-lambdas? (cdr bs))))))
(define k-group-size (subr (read @globals) (k-letrec-bs nat) nat)
  (lambda (bs n) (if (null? bs) n (k-group-size (cdr bs) (+ n 1)))))
;; Group `bs`, bound as `k-bind-group` binds it after `saved` and `rsaved`,
;; its procedures checked at their types; and if one does not check, the
;; group again at its types with the globals each reads found, bound so
;; for the body; the first error if that finds nothing new. The effect.
(define* k-letrec-checked
  (subr (maxeff checks spin) (k-letrec-bs int k-named k-checker k-group-checker) k-eff)
  (lambda (bs saved rsaved check check-group)
    (let ((r (prompt k-tag (k-done (k-te 0 (check-group bs))) (lambda (r) r))))
      (tagcase r
        (k-done (te) (extract te 2))
        (k-err (m a b)
          (if (not (k-all-lambdas? bs))
              (k-fail m a b)
              (begin
                (k-unbind-to saved)
                (set k-recursive rsaved)
                (let* ((size (k-group-size bs 0))
                       (found (k-letrec-found bs (k-types-of bs) check (+ size 2))))
                  (if (null? found)
                      (k-fail m a b)
                      (begin (k-bind-group (car found)) (check-group (car found))))))))
        (else y (k-fail "k-ok inside" 0 0)))))))))
