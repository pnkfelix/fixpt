;;; A `letrec` group whose procedures read globals their types leave out:
;;; each one's type, with the globals it reads found, as `define*` finds them
;;; for a definition. The Rust checker's `letrec_with` and `letrec_found`,
;;; rule for rule. And a group with members typed `->*`, their effects
;;; found: `arrow_star_group`.

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
           (check-print-parts (select check-print-parts-types check-print-parts-sig))
           (check-resolve (select check-resolve-types check-resolve-sig)))
    (module
(hide (include check-letrec-types) (include check-types-types) (include check-synth-types)
      (include check-resolve-types))
;; The types it uses of the files before it.
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-expect) (include check-effects)
      (include check-print-parts) (include check-env) (include check-terminate))
(import check-resolve k-end k-free-into k-start)

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
;;; ------------------------------------------------------------ `->*`

;; The latent effect of `x`, a `lambda`, told by `synth` the parameters and
;; result of `t`, a `subr` under any `poly`s, whose binders are in scope.
(define* k-arrow-star-latent (subr (maxeff checks spin) (k-lambda-synth int kx) k-eff)
  (lambda (synth t x)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body) (k-arrow-star-latent synth body x))
      (ty-subr (e ps r cv) (begin (synth x ps r) (get k-last-latent)))
      (else y (k-fail "`->*` reads as a `subr`" (k-start x) (k-end x))))))
;; Whether effect `e` reads the global of one of `ns`.
(define k-reads-one-of? (subr (maxeff (read @globals) (read @t)) (k-names k-eff) bool)
  (lambda (ns e)
    (and (not (null? e))
         (or (tagcase (car e)
               (a-read (r) (tagcase r (r-global (g) (k-has-name? ns g)) (else y #f)))
               (else y #f))
             (k-reads-one-of? ns (cdr e))))))
;; Each of `bs`'s own effect: one typed `->*`, found from its `lambda` by
;; `synth`, the group's calls of each other standing for nothing more;
;; another's, its type's.
(define* k-arrow-star-owns (subr (maxeff checks spin) (k-lambda-synth k-letrec-bs) k-eff-list)
  (lambda (synth bs)
    (if (null? bs)
        nil
        (let* ((t (extract (car bs) 2))
               (x (extract (car bs) 3))
               (own (cond ((not (k-arrow-star-ty? t))
                           (let ((l (k-latent-of t))) (if (null? l) (the k-eff nil) (car l))))
                          ((tagcase x (x-lambda (ps body a b abk) #t) (else y #f))
                           (k-arrow-star-latent synth t x))
                          (else (k-fail (string-append "`->*` finds a procedure's effect from its "
                                                       "`lambda`: define it as one")
                                        (k-start x) (k-end x))))))
          (the k-eff-list (cons own (k-arrow-star-owns synth (cdr bs))))))))
(define k-bs-names (subr (read @globals) (k-letrec-bs) k-names)
  (lambda (bs) (if (null? bs) nil (the k-names (cons (extract (car bs) 1) (k-bs-names (cdr bs)))))))
;; Whether each of `bs` is polymorphic: its effect says its own binders.
(define k-bs-polys (subr (maxeff kstate spin) (k-letrec-bs) k-bools)
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((p (tagcase (k-get (k-resolve (extract (car bs) 2)))
                   (ty-poly (vs body) #t)
                   (else y #f))))
          (the k-bools (cons p (k-bs-polys (cdr bs))))))))
;; The indexes, from `i`, of those of `ns` in `free`.
(define k-indexes-in (subr (maxeff (read @globals) (read @t)) (k-names k-names int) k-ids)
  (lambda (ns free i)
    (cond ((null? ns) nil)
          ((k-has-name? free (car ns)) (the k-ids (cons i (k-indexes-in (cdr ns) free (+ i 1)))))
          (else (k-indexes-in (cdr ns) free (+ i 1))))))
;; For each of `bs`, the members of the group, `ns`, its `lambda` names.
(define* k-group-refs (subr (maxeff (read @t) (alloc @t)) (k-letrec-bs k-names) k-idss)
  (lambda (bs ns)
    (if (null? bs)
        nil
        (the k-idss (cons (k-indexes-in ns (k-free-into (extract (car bs) 3) nil nil) 0)
                          (k-group-refs (cdr bs) ns))))))
(define k-ids-onto (subr (read @globals) (k-ids k-ids) k-ids)
  (lambda (xs ys) (if (null? xs) ys (the k-ids (cons (car xs) (k-ids-onto (cdr xs) ys))))))
;; The members reached from `todo` through `refs`, onto `seen`.
(define* k-reach (subr (maxeff (read @t) spin) (k-idss k-ids k-ids) k-ids)
  (lambda (refs todo seen)
    (cond ((null? todo) seen)
          ((k-has-id? seen (car todo)) (k-reach refs (cdr todo) seen))
          (else (k-reach refs (k-ids-onto (k-nth refs (car todo)) (cdr todo))
                         (the k-ids (cons (car todo) seen)))))))
;; The effects of the members `js`, `i` itself and those not polymorphic.
(define* k-reached-effect (subr (maxeff kstate spin) (k-eff-list k-bools k-ids int) k-eff)
  (lambda (owns polys js i)
    (cond ((null? js) nil)
          ((or (= (car js) i) (not (k-nth polys (car js))))
           (k-union (k-nth owns (car js)) (k-reached-effect owns polys (cdr js) i)))
          (else (k-reached-effect owns polys (cdr js) i)))))
;; Each of `bs`, from the `i`th, at its type found: one typed `->*`, with
;; the effects of the members it reaches, and `spin` if that reads one's
;; global.
(define* k-arrow-star-each
  (subr (maxeff kstate spin) (k-letrec-bs k-eff-list k-idss k-bools k-names int) k-letrec-bs)
  (lambda (bs owns refs polys ns i)
    (if (null? bs)
        nil
        (let* ((b (car bs))
               (t (extract b 2))
               (found (if (k-arrow-star-ty? t)
                          (let* ((e (k-reached-effect owns polys (k-reach refs (cons i nil) nil) i))
                                 (e (if (k-reads-one-of? ns e) (k-insert (a-spin) e) e)))
                            (k-with-latent t e))
                          t))
               (rest (k-arrow-star-each (cdr bs) owns refs polys ns (+ i 1))))
          (the k-letrec-bs (cons (product (1 (extract b 1)) (2 found) (3 (extract b 3))) rest))))))
;; Group `bs`, with members typed `->*`, bound and its termination noted,
;; at the types found: each such member's own effect found from its
;; `lambda` in one pass (`synth`), the group's calls of each other standing
;; for nothing more; then each one's with the effects of every member it
;; reaches through the group's references (but a polymorphic one's, which
;; say its own binders), and `spin` if that reads a member's global, as
;; `k-no-reaching-itself` asks. The group is checked again at these types,
;; which refuses what they leave out.
(define* k-arrow-star-found (subr (maxeff checks spin) (k-lambda-synth k-letrec-bs) k-letrec-bs)
  (lambda (synth bs)
    (let* ((owns (k-arrow-star-owns synth bs)) (ns (k-bs-names bs)))
      (k-arrow-star-each bs owns (k-group-refs bs ns) (k-bs-polys bs) ns 0))))
(define k-any-arrow-star? (subr (maxeff (read @globals) (read @t)) (k-letrec-bs) bool)
  (lambda (bs)
    (and (not (null? bs))
         (or (k-arrow-star-ty? (extract (car bs) 2)) (k-any-arrow-star? (cdr bs))))))

;; Group `bs`, bound by `k-bind-group` after `saved` and `rsaved`, its
;; procedures checked at their types (with `->*`, at the types found,
;; `synth` telling each `lambda`); and if one does not check, the group
;; again at its types with the globals each reads found, bound so for the
;; body; the first error if that finds nothing new. The effect.
(define* k-letrec-checked
  (subr (maxeff checks spin) (k-letrec-bs int k-named k-checker k-group-checker k-lambda-synth)
        k-eff)
  (lambda (bs0 saved rsaved check check-group synth)
    (let* ((bound (k-bind-group bs0))
           (star (k-any-arrow-star? bs0))
           ;; With `->*`, the group bound again at the types found.
           (bs (if star
                   (let ((found (k-arrow-star-found synth bs0)))
                     (begin (k-unbind-to saved) (set k-recursive rsaved) (k-bind-group found)
                            found))
                   bs0))
           (r (prompt k-tag (k-done (k-te 0 (check-group bs))) (lambda (r) r))))
      (tagcase r
        (k-done (te) (extract te 2))
        (k-err (m a b)
          (if (or star (not (k-all-lambdas? bs)))
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
