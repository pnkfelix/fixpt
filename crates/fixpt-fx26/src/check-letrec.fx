;;; A `letrec` group whose procedures read globals their types leave out:
;;; each one's type, with the globals it reads found, as `define*` finds them
;;; for a definition. The Rust checker's `letrec_with` and `letrec_found`,
;;; rule for rule.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-letrec-module (module
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

;; What checks one expression against a type, and a group's procedures at
;; their types: `k-check` and `k-check-letrec`, given by `check-synth.fx`.
(define-type k-checker (subr (maxeff checks spin) (kx int) k-eff))
(define-type k-group-checker (subr (maxeff checks spin) (k-letrec-bs) k-eff))

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
;; One round: the group at types `ts`, and what each was found to read; or
;; none, if a procedure does not check even so.
(define-type k-idss (listof k-ids acyclic))
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
        (else y (k-fail "k-ok inside" 0 0))))))))

(define k-note-ending (with check-letrec-module k-note-ending))
(define k-with-latent (with check-letrec-module k-with-latent))
(define k-globals-of (with check-letrec-module k-globals-of))
(define k-bind-group (with check-letrec-module k-bind-group))
(define k-letrec-checked (with check-letrec-module k-letrec-checked))
