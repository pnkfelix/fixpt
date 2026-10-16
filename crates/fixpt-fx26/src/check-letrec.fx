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
;; An error at the first of `bs` typed `->*` that is not a `lambda`.
(define k-arrow-star-lambdas (subr checks (k-letrec-bs) unit)
  (lambda (bs)
    (cond ((null? bs) #u)
          ((and (k-arrow-star-ty? (extract (car bs) 2))
                (not (tagcase (extract (car bs) 3) (x-lambda (ps body a b abk) #t) (else y #f))))
           (k-fail (string-append "`->*` finds a procedure's effect from its `lambda`: "
                                  "define it as one")
                   (k-start (extract (car bs) 3)) (k-end (extract (car bs) 3))))
          (else (k-arrow-star-lambdas (cdr bs))))))
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

;; The strongly connected components of the graph `refs` (each node's
;; successors), each sorted, callees first: Tarjan's, from each node in
;; order, its successors in order, as the Rust checker's `components`.
(define* k-components (subr k-walks (k-idss) k-idss)
  (lambda (refs)
    (let* ((n (k-length refs))
           (w (product (1 (the (arrayof int @t) (make-array n -1)))
                       (2 (the (arrayof int @t) (make-array n 0)))
                       (3 (the (arrayof bool @t) (make-array n #f)))
                       (4 (the (ref k-ids @t) (new nil)))
                       (5 (the (ref int @t) (new 0)))
                       (6 (the (ref k-idss @t) (new nil))))))
      (begin (k-components-from refs w 0 n) (k-idss-reversed (get (extract w 6)) nil)))))
(define* k-components-from (subr k-walks (k-idss k-walk int int) unit)
  (lambda (refs w v n)
    (if (>= v n)
        #u
        (begin (if (< (array-ref (extract w 1) v) 0) (k-tarjan refs w v) #u)
               (k-components-from refs w (+ v 1) n)))))
(define-rec
  (k-tarjan (subr k-walks (k-idss k-walk int) unit)
    (lambda (refs w v)
      (let ((next (extract w 5)) (stack (extract w 4)))
        (begin
          (array-set! (extract w 1) v (get next))
          (array-set! (extract w 2) v (get next))
          (set next (+ (get next) 1))
          (set stack (the k-ids (cons v (get stack))))
          (array-set! (extract w 3) v #t)
          (k-tarjan-next refs w v (k-nth refs v))
          (if (= (array-ref (extract w 1) v) (array-ref (extract w 2) v))
              (set (extract w 6)
                   (the k-idss (cons (k-ids-sorted (k-tarjan-pop w v nil) nil)
                                     (get (extract w 6)))))
              #u)))))
  (k-tarjan-next (subr k-walks (k-idss k-walk int k-ids) unit)
    (lambda (refs w v us)
      (if (null? us)
          #u
          (let ((u (car us)) (low (extract w 2)))
            (begin
              (cond ((< (array-ref (extract w 1) u) 0)
                     (begin (k-tarjan refs w u)
                            (array-set! low v (min (array-ref low v) (array-ref low u)))))
                    ((array-ref (extract w 3) u)
                     (array-set! low v (min (array-ref low v) (array-ref (extract w 1) u))))
                    (else #u))
              (k-tarjan-next refs w v (cdr us))))))))
;; The stack of `w` popped down to `v`, onto `acc`.
(define* k-tarjan-pop (subr k-walks (k-walk int k-ids) k-ids)
  (lambda (w v acc)
    (let* ((stack (extract w 4)) (u (car (get stack))))
      (begin (set stack (cdr (get stack)))
             (array-set! (extract w 3) u #f)
             (if (= u v) (the k-ids (cons u acc)) (k-tarjan-pop w v (the k-ids (cons u acc))))))))
;; `xs` sorted, onto `acc` (sorted).
(define k-ids-sorted (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-ids k-ids) k-ids)
  (lambda (xs acc) (if (null? xs) acc (k-ids-sorted (cdr xs) (k-id-inserted (car xs) acc)))))
(define k-id-inserted (subr (maxeff (read @globals) (read @t) (alloc @t)) (int k-ids) k-ids)
  (lambda (x xs)
    (if (or (null? xs) (<= x (car xs)))
        (the k-ids (cons x xs))
        (the k-ids (cons (car xs) (k-id-inserted x (cdr xs)))))))
(define k-idss-reversed (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-idss k-idss) k-idss)
  (lambda (xs acc) (if (null? xs) acc (k-idss-reversed (cdr xs) (the k-idss (cons (car xs) acc))))))

;; `ns` with each `(n . old)` `(n . new)`, reversed onto `acc`; a list as
;; long as the recursion noted, walked in a loop.
(define k-named-retyped (subr (maxeff kreads (alloc @t)) (k-named symbol int int k-named) k-named)
  (lambda (ns n old new acc)
    (cond ((null? ns) acc)
          ((and (symbol=? (car (car ns)) n) (= (cdr (car ns)) old))
           (k-named-retyped (cdr ns) n old new (the k-named (cons (cons n new) acc))))
          (else (k-named-retyped (cdr ns) n old new (the k-named (cons (car ns) acc)))))))
(define k-whys-retyped (subr (maxeff kreads (alloc @t)) (k-whys symbol int int k-whys) k-whys)
  (lambda (ws n old new acc)
    (cond ((null? ws) acc)
          ((and (symbol=? (extract (car ws) 1) n) (= (extract (car ws) 2) old))
           (let ((w (product (1 n) (2 new) (3 (extract (car ws) 3)))))
             (k-whys-retyped (cdr ws) n old new (the k-whys (cons w acc)))))
          (else (k-whys-retyped (cdr ws) n old new (the k-whys (cons (car ws) acc)))))))
(define k-named-reversed (subr (maxeff (read @globals) (alloc @t)) (k-named k-named) k-named)
  (lambda (ns acc)
    (if (null? ns) acc (k-named-reversed (cdr ns) (the k-named (cons (car ns) acc))))))
(define k-whys-reversed (subr (maxeff (read @globals) (alloc @t)) (k-whys k-whys) k-whys)
  (lambda (ws acc)
    (if (null? ws) acc (k-whys-reversed (cdr ws) (the k-whys (cons (car ws) acc))))))
;; Member `n`, of type `old`, given type `new`: bound so, and a call of it
;; still recursion where its group's is.
(define k-arrow-star-retyped (subr (maxeff kstate spin) (symbol int int) unit)
  (lambda (n old new)
    (begin (k-rebind n new)
           (set k-recursive
                (k-named-reversed (k-named-retyped (get k-recursive) n old new nil) nil))
           (set k-spin-why
                (k-whys-reversed (k-whys-retyped (get k-spin-why) n old new nil) nil)))))

;; Whether any of the members `comp` is typed `->*`, `ts` their types.
(define k-comp-starred? (subr (maxeff (read @globals) (read @t)) (k-ids (arrayof int @t)) bool)
  (lambda (comp ts)
    (and (not (null? comp))
         (or (k-arrow-star-ty? (array-ref ts (car comp))) (k-comp-starred? (cdr comp) ts)))))
;; Each of the members `comp`'s own effect: one typed `->*` (`marks`),
;; found from its `lambda` by `synth` at its type in `ts`; another's, its
;; type's.
(define* k-comp-owns
  (subr (maxeff checks spin) (k-lambda-synth k-letrec-bs k-bools (arrayof int @t) k-ids) k-eff-list)
  (lambda (synth bs marks ts comp)
    (if (null? comp)
        nil
        (let* ((i (car comp))
               (t (array-ref ts i))
               (own (if (k-nth marks i)
                        (k-arrow-star-latent synth t (extract (k-nth bs i) 3))
                        (let ((l (k-latent-of t))) (if (null? l) (the k-eff nil) (car l)))))
               (rest (k-comp-owns synth bs marks ts (cdr comp))))
          (the k-eff-list (cons own rest))))))
;; The effects `owns` of members `comp`: `i`'s and those of the others not
;; polymorphic (`polys`).
(define* k-comp-effect (subr (maxeff kstate spin) (k-ids k-eff-list k-bools int) k-eff)
  (lambda (comp owns polys i)
    (cond ((null? comp) nil)
          ((or (= (car comp) i) (not (k-nth polys (car comp))))
           (k-union (car owns) (k-comp-effect (cdr comp) (cdr owns) polys i)))
          (else (k-comp-effect (cdr comp) (cdr owns) polys i)))))
;; Each of the members `rest` of `comp` typed `->*` given its type found:
;; the effects of its component, and `spin` if that reads a member's
;; global (of `ns`).
(define* k-comp-found
  (subr (maxeff kstate spin) (k-ids k-ids k-eff-list k-bools k-bools k-names (arrayof int @t)) unit)
  (lambda (rest comp owns marks polys ns ts)
    (if (null? rest)
        #u
        (let ((i (car rest)))
          (begin
            (if (k-nth marks i)
                (let* ((e (k-comp-effect comp owns polys i))
                       (e (if (k-reads-one-of? ns e) (k-insert (a-spin) e) e))
                       (old (array-ref ts i))
                       (found (k-with-latent old e)))
                  (begin (k-arrow-star-retyped (k-nth ns i) old found) (array-set! ts i found)))
                #u)
            (k-comp-found (cdr rest) comp owns marks polys ns ts))))))
;; Each of components `comps` with a member typed `->*`, in order.
(define* k-comps-found
  (subr (maxeff checks spin)
        (k-lambda-synth k-letrec-bs k-bools k-bools k-names (arrayof int @t) k-idss)
        unit)
  (lambda (synth bs marks polys ns ts comps)
    (if (null? comps)
        #u
        (begin
          (if (k-comp-starred? (car comps) ts)
              (let ((owns (k-comp-owns synth bs marks ts (car comps))))
                (k-comp-found (car comps) (car comps) owns marks polys ns ts))
              #u)
          (k-comps-found synth bs marks polys ns ts (cdr comps))))))
(define k-bs-marks (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-letrec-bs) k-bools)
  (lambda (bs)
    (if (null? bs)
        nil
        (the k-bools (cons (k-arrow-star-ty? (extract (car bs) 2)) (k-bs-marks (cdr bs)))))))
;; The types of `bs` into `ts`, from `i`.
(define k-bs-types
  (subr (maxeff (read @globals) (read @t) (write @t)) (k-letrec-bs (arrayof int @t) int) unit)
  (lambda (bs ts i)
    (if (null? bs)
        #u
        (begin (array-set! ts i (extract (car bs) 2)) (k-bs-types (cdr bs) ts (+ i 1))))))
;; `bs`, from the `i`th, at the types `ts`.
(define k-bs-at
  (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-letrec-bs (arrayof int @t) int)
        k-letrec-bs)
  (lambda (bs ts i)
    (if (null? bs)
        nil
        (let ((b (car bs)))
          (the k-letrec-bs (cons (product (1 (extract b 1)) (2 (array-ref ts i)) (3 (extract b 3)))
                                 (k-bs-at (cdr bs) ts (+ i 1))))))))
;; Group `bs`, with members typed `->*`, bound and its termination noted,
;; at the types found, as the Rust checker's `arrow_star_group`: its
;; components taken callees first (`k-components`), each such member's
;; own effect found from its `lambda` in one pass (`synth`), told the types
;; found of the members it names outside its component, its component's
;; calls of each other standing for nothing more; then each one's with the
;; effects of the rest of its component (but a polymorphic one's), and
;; `spin` if that reads a member's global; its binding given the type
;; found, a call of it still recursion where the group's is. The group is
;; checked again at these types, which refuses what they leave out.
(define* k-arrow-star-found (subr (maxeff checks spin) (k-lambda-synth k-letrec-bs) k-letrec-bs)
  (lambda (synth bs)
    (begin
      (k-arrow-star-lambdas bs)
      (let* ((ns (k-bs-names bs))
             (ts (the (arrayof int @t) (make-array (k-length bs) -1)))
             (filled (k-bs-types bs ts 0)))
        (begin (k-comps-found synth bs (k-bs-marks bs) (k-bs-polys bs) ns ts
                              (k-components (k-group-refs bs ns)))
               (k-bs-at bs ts 0))))))
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
