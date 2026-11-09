;;; The checker, in FX-26: which recursive groups need not say `spin` (size-
;;; change termination).
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------- well-founded recursion
;;; Which recursive groups need not say `spin`: size-change termination
;;; (Lee, Jones and Ben-Amram, POPL 2001), as `terminate.rs` does it. Each
;;; call within the group is a graph of how the callee's arguments relate to
;;; the caller's parameters; closed under composition, every graph from a
;;; member to itself that is its own composition must have a parameter
;;; strictly smaller. The measures: parts (of sums, products, pairs at a
;;; `acyclic` region, datums), and integers counting down to a bound below or
;;; up to one above. A member named but not called escapes, and fails.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-terminate-types (load-module "fx26:check-terminate-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-synth-types (load-module "fx26:check-synth-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (table-types (load-module "fx26:table-types.fx"))
       (check-holds-types (load-module "fx26:check-holds-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-expect-types (load-module "fx26:check-expect-types.fx"))
       (check-sc-graphs-types (load-module "fx26:check-sc-graphs-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-subtype-types (load-module "fx26:check-subtype-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (check-holds (select check-holds-types check-holds-sig))
           (check-env (select check-env-types check-env-sig))
           (check-expect (select check-expect-types check-expect-sig))
           (check-sc-graphs (select check-sc-graphs-types check-sc-graphs-sig))
           (check-print (select check-print-types check-print-sig))
           (tables (select table-types tables-sig))
           (check-subtype (select check-subtype-types check-subtype-sig)))
    (module
(hide (include check-terminate-types) (include check-types-types) (include check-synth-types)
      (include check-resolve-types))
;; The types it uses of the files before it.
(define-type table (select table-types table))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-resolve) (include check-holds) (include check-env)
      (include check-expect) (include check-sc-graphs) (include check-print) (include tables)
      (include check-subtype))

(define k-sc-compose-one (->* (k-edge k-graph k-graph) k-graph)
  (lambda (e b out)
    (cond ((null? b) out)
          ((= (extract e 2) (extract (car b) 1))
           (let* ((d (car b)) (strict (or (extract e 3) (extract d 3))))
             (k-sc-compose-one e (cdr b) (k-sc-add out (extract e 1) (extract d 2) strict))))
          (else (k-sc-compose-one e (cdr b) out)))))
(define k-sc-compose (->* (k-graph k-graph k-graph) k-graph)
  (lambda (a b out) (if (null? a) out (k-sc-compose (cdr a) b (k-sc-compose-one (car a) b out)))))
(define k-sc-same? (->* (k-graph k-graph) bool)
  (lambda (a b)
    (if (null? a)
        (null? b)
        (and (not (null? b))
             (= (extract (car a) 1) (extract (car b) 1))
             (= (extract (car a) 2) (extract (car b) 2))
             (if (extract (car a) 3) (extract (car b) 3) (not (extract (car b) 3)))
             (k-sc-same? (cdr a) (cdr b))))))
;; Whether `c` and `d` are the same call: from and to the same members, of the same graph.
(define k-sc-call=? (->* (k-call k-call) bool)
  (lambda (c d)
    (and (= (extract c 1) (extract d 1))
         (= (extract c 2) (extract d 2))
         (k-sc-same? (extract c 3) (extract d 3)))))
(define k-sc-has? (->* (k-calls k-call) bool)
  (lambda (cs c) (and (not (null? cs)) (or (k-sc-call=? (car cs) c) (k-sc-has? (cdr cs) c)))))
;; A call's members, from and to, as one key.
(define k-sc-key (->* (k-call) int)
  (lambda (c) (+ (* (extract c 1) 65536) (extract c 2))))
;; Whether `c` is among the calls in `seen` (by `k-sc-key`); if not, it is now.
(define k-sc-seen? (->* ((table int k-calls @t) k-call) bool)
  (lambda (seen c)
    (let ((here (table-ref seen (k-sc-key c) nil)))
      (if (k-sc-has? here c) #t (begin (table-set! seen (k-sc-key c) (cons c here)) #f)))))
(define k-sc-seen-all (->* ((table int k-calls @t) k-calls) (table int k-calls @t))
  (lambda (seen cs)
    (if (null? cs) seen (begin (k-sc-seen? seen (car cs)) (k-sc-seen-all seen (cdr cs))))))
;; `cs` without repeats, onto `out` in reverse: each call compared only with
;; those of the same members (by `seen`, from and to), not every one kept.
(define k-sc-dedup-in (->* (k-calls k-calls (table int k-calls @t)) k-calls)
  (lambda (cs out seen)
    (if (null? cs)
        out
        (let* ((c (car cs)) (key (k-sc-key c)) (here (table-ref seen key nil)))
          (if (k-sc-has? here c)
              (k-sc-dedup-in (cdr cs) out seen)
              (begin (table-set! seen key (cons c here))
                     (k-sc-dedup-in (cdr cs) (cons c out) seen)))))))
(define k-sc-dedup (->* (k-calls k-calls) k-calls)
  (lambda (cs out) (k-sc-dedup-in cs out (make-table k-id-hash k-id=?))))
;; Whether `e` is a strict edge from a slot to itself.
(define k-sc-strict-self? (->* (k-edge) bool)
  (lambda (e) (and (= (extract e 1) (extract e 2)) (extract e 3))))
(define k-sc-strict-loop? (->* (k-graph) bool)
  (lambda (g) (and (not (null? g)) (or (k-sc-strict-self? (car g)) (k-sc-strict-loop? (cdr g))))))
;; Whether every graph from a member to itself that is its own composition
;; has a strict loop.
(define k-sc-ok? (->* (k-calls) bool)
  (lambda (cs)
    (or (null? cs)
        (let ((c (car cs)))
          (and (or (not (= (extract c 1) (extract c 2)))
                   (not (k-sc-same? (k-sc-compose (extract c 3) (extract c 3) nil) (extract c 3)))
                   (k-sc-strict-loop? (extract c 3)))
               (k-sc-ok? (cdr cs)))))))
;; A graph's closure may grow; beyond this many, the group does not pass.
(define k-sc-most int 4000)
(define-rec
  ;; `seen`: `all`, by `k-sc-key`, for whether a call is new.
  (k-sc-close (->* (k-calls k-calls int (table int k-calls @t)) bool)
    (lambda (todo all n seen)
      (if (null? todo)
          (k-sc-ok? all)
          (let ((c (car todo)) (calls (get k-sc-calls)))
            (k-sc-extend (extract c 1) (extract c 2) (extract c 3) calls (cdr todo) all n seen)))))
  (k-sc-extend
    (->* (int int k-graph k-calls k-calls k-calls int (table int k-calls @t)) bool)
    (lambda (f g a calls todo all n seen)
      (cond ((null? calls) (k-sc-close todo all n seen))
            ((not (= (extract (car calls) 1) g)) (k-sc-extend f g a (cdr calls) todo all n seen))
            (else
             (let* ((rest (cdr calls)) (cg (k-sc-compose a (extract (car calls) 3) nil))
                    (h (extract (car calls) 2)) (new (product (1 f) (2 h) (3 cg))))
               (cond ((k-sc-seen? seen new) (k-sc-extend f g a rest todo all n seen))
                     ((>= n k-sc-most) (begin (set k-sc-too-many #t) #f))
                     (else
                      (k-sc-extend f g a rest (cons new todo) (cons new all) (+ n 1) seen)))))))))

;; A binding's lambda, under `plambda`, `the` and `rlambda`.
(define k-sc-lambda-of (->* (kx) kx)
  (lambda (x)
    (tagcase x
      (x-plambda (bs body a b abk abkr) (k-sc-lambda-of body))
      (x-the (t body a b abk abkr) (k-sc-lambda-of body))
      (x-rlambda (r l a b abk abkr) (k-sc-lambda-of l))
      (else y y))))
;; The parameter types of a declared type, under its binders.
(define k-sc-param-types (->* (int) k-ids)
  (lambda (t)
    (tagcase (k-get t)
      (ty-poly (bs body) (k-sc-param-types body))
      (ty-subr (e ps r cv spc) ps)
      (else y nil))))
;; Whether `s` names the standard binding of that name.
(define k-std? (->* (symbol) bool)
  (lambda (s) (k-std-binding? s (k-lookup s))))
;; Whether `t` is a natural, of a size or not.
(define k-nat-ty? (->* (int) bool)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-nat (z) #t) (else y #f))))
;; What is known of parameter `j`, of type `t`, on entry: itself, and a count if an integer.
(define k-sc-param-knows (->* (int int bool) k-trs)
  (lambda (j t natural)
    (let ((count (or natural (= (k-resolve t) (k-resolve k-int)))))
      (the k-trs (cons (tr-part j #f t) (if count (the k-trs (cons (tr-int j 0) nil)) nil))))))
;; The parameters `ps`, the `j`th on, each known as itself.
(define k-sc-param-scope (->* (k-typed-params k-ids int k-tscope) k-tscope)
  (lambda (ps ts j sc)
    (if (null? ps)
        sc
        (let* ((t (car ts))
               (natural (k-nat-ty? t))
               (noted (if natural (set k-sc-naturals (cons j (get k-sc-naturals))) #u))
               (ks (k-sc-param-knows j t natural)))
          (k-sc-param-scope (cdr ps) (cdr ts) (+ j 1) (k-sc-bind (extract (car ps) 1) ks sc))))))
(define k-sc-walk-members (->* (k-letrec-bs int) bool)
  (lambda (bs i)
    (or (null? bs)
        (tagcase (k-sc-lambda-of (extract (car bs) 3))
          (x-lambda (ps body a b abk abkr)
            (let ((ts (k-sc-param-types (extract (car bs) 2))))
              (and (<= (k-length ps) (k-length ts))
                   (begin (set k-sc-current i)
                          (set k-sc-naturals nil)
                          (k-sc-walk body (k-sc-param-scope ps ts 0 nil) nil)
                          (and (null? (get k-sc-escapes)) (k-sc-walk-members (cdr bs) (+ i 1)))))))
          (else y #f)))))
(define k-sc-names (->* (k-letrec-bs) k-names)
  (lambda (bs) (if (null? bs) nil (the k-names (cons (extract (car bs) 1) (k-sc-names (cdr bs)))))))
(define k-sc-upto (->* (int int) k-ids)
  (lambda (j n)
    (letrec ((down (subr kstate (int k-ids) k-ids)
                   (lambda (i acc) (if (< i j) acc (down (- i 1) (the k-ids (cons i acc)))))))
      (down (- n 1) nil))))
;; Every (member . parameter) of the group, the `i`th member on.
(define k-sc-all-params (->* (k-letrec-bs int k-guards) k-guards)
  (lambda (bs i out)
    (if (null? bs)
        out
        (k-sc-all-params (cdr bs) (+ i 1)
          (tagcase (k-sc-lambda-of (extract (car bs) 3))
            (x-lambda (ps body a b abk abkr) (k-sc-with i (k-sc-upto 0 (k-length ps)) out))
            (else y out))))))
(define k-sc-drop (->* (k-guards int int) k-guards)
  (lambda (gs i j)
    (cond ((null? gs) gs)
          ((and (= (car (car gs)) i) (= (cdr (car gs)) j)) (k-sc-drop (cdr gs) i j))
          (else (the k-guards (cons (car gs) (k-sc-drop (cdr gs) i j)))))))
;; `inv` less parameter `j` of each node `ns` from `n` says is of binding `to`:
;; any may be called.
(define k-sc-drop-nodes (->* (k-guards int int k-ids int) k-guards)
  (lambda (inv to j ns n)
    (cond ((null? ns) inv)
          ((= (car ns) to) (k-sc-drop-nodes (k-sc-drop inv n j) to j (cdr ns) (+ n 1)))
          (else (k-sc-drop-nodes inv to j (cdr ns) (+ n 1))))))
;; `inv` less what the call from `from` to `to` passing `args` changes.
(define k-sc-keep-args (->* (k-guards int int k-ids int) k-guards)
  (lambda (inv from to args j)
    (if (null? args)
        inv
        (let* ((p (car args))
               (kept (if (and (>= p 0) (k-sc-guarded? inv from p))
                         inv
                         (k-sc-drop-nodes inv to j (get k-sc-node-binding) 0))))
          (k-sc-keep-args kept from to (cdr args) (+ j 1))))))
(define k-sc-keep-all (->* (k-guards k-passed) k-guards)
  (lambda (inv ps)
    (if (null? ps)
        inv
        (let* ((c (car ps)) (kept (k-sc-keep-args inv (extract c 1) (extract c 2) (extract c 3) 0)))
          (k-sc-keep-all kept (cdr ps))))))
;; The invariant parameters: the greatest set every call keeps.
(define k-sc-invariants (->* (k-guards) k-guards)
  (lambda (inv)
    (let ((next (k-sc-keep-all inv (get k-sc-passed))))
      (if (= (k-length next) (k-length inv)) inv (k-sc-invariants next)))))
(define k-sc-member-name (->* (int) string)
  (lambda (i) (symbol->string (k-nth (get k-sc-members) i))))
(define k-sc-node-name (->* (int) string)
  (lambda (i) (symbol->string (k-nth (get k-sc-node-names) i))))
(define k-sc-strict-any? (->* (k-graph) bool)
  (lambda (g) (and (not (null? g)) (or (extract (car g) 3) (k-sc-strict-any? (cdr g))))))
(define k-sc-has-string? (->* (k-texts string) bool)
  (lambda (xs s) (and (not (null? xs)) (or (string=? (car xs) s) (k-sc-has-string? (cdr xs) s)))))
;; The call `c`, in words.
(define k-sc-call-words (->* (k-call) string)
  (lambda (c)
    (let ((callee (k-sc-node-name (extract c 2))) (caller (k-sc-node-name (extract c 1))))
      (k-cat5 "the call of `" callee "` in `" caller "`"))))
;; The calls, in the order met, that pass nothing strictly smaller, and
;; either nothing related to the caller's parameters or with a hint why;
;; each once, in words (newest first). One passing its caller's parameters
;; on unchanged is harmless.
(define k-sc-flat (->* (k-calls k-texts k-texts) k-texts)
  (lambda (cs hs out)
    (if (null? cs)
        out
        (let* ((c (car cs))
               (s1 (k-sc-call-words c))
               (s (if (string=? (car hs) "") s1 (k-cat4 s1 " (" (car hs) ")"))))
          (k-sc-flat (cdr cs) (cdr hs)
                     (if (or (k-sc-strict-any? (extract c 3))
                             (and (not (null? (extract c 3))) (string=? (car hs) ""))
                             (k-sc-has-string? out s))
                         out
                         (the k-texts (cons s out))))))))
(define k-sc-escape-why (->* () string)
  (lambda ()
    (let* ((e (car (get k-sc-escapes))) (escapes (k-sc-member-name (cdr e)))
           (named (k-cat4 "`" escapes "` is named in `" (k-sc-node-name (car e)))))
      (k-cat3 named "` other than as a call's operator: "
              "whoever is given it may call it again, with anything"))))
;; Why the walked calls, not too many, may not end: those that pass nothing smaller, in words.
(define k-sc-shrinks-why (->* () string)
  (lambda ()
    (let* ((calls (the k-calls (reverse (get k-sc-calls))))
           (hints (the k-texts (reverse (get k-sc-hints))))
           (flat (the k-texts (reverse (k-sc-flat calls hints nil)))))
      (if (null? flat)
          "no argument keeps shrinking around every loop of calls"
          (string-append "nothing smaller, or related, is passed by " (k-join flat ", "))))))
;; Why the walked calls may not end.
(define k-sc-calls-why (->* () string)
  (lambda ()
    (let ((all (k-sc-dedup (get k-sc-calls) nil)))
      (cond ((k-sc-close all all (k-length all) (k-sc-seen-all (make-table k-id-hash k-id=?) all))
             "")
            ((get k-sc-too-many) "the calls combine in too many ways to follow")
            (else (k-sc-shrinks-why))))))
;; Whether every run of the group `bs` ends, so that calls within it need
;; not say `spin`: "" if so, and otherwise why not, in words for an error.
;; With an `allof`, at each member's types (`k-termination-by-member`), each
;; binding's kept for its calls (`k-member-spins`): the group ends if it does
;; from every member.
(define k-termination (->* (k-letrec-bs) string)
  (lambda (bs)
    (if (= (k-sc-most-members bs 0) 0)
        (k-termination-one bs)
        (let ((by (k-termination-by-member bs)))
          (begin (k-note-member-spins bs by) (k-first-why by))))))
(define k-sc-members-of (->* (int) k-ids)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-allof (ms) ms) (else y nil))))
(define k-sc-most-members (->* (k-letrec-bs int) int)
  (lambda (bs most)
    (if (null? bs)
        most
        (k-sc-most-members (cdr bs) (max most (k-length (k-sc-members-of (extract (car bs) 2))))))))
;; The group walked, its nodes `nodes`: "" if every node is a lambda and no
;; member escapes; else why not. Walked twice: first to learn which
;; parameters every call passes on unchanged, then with them as bounds.
(define k-sc-walked (->* (k-letrec-bs k-letrec-bs k-ids bool) string)
  (lambda (bs nodes binding skip)
    (begin
      (set k-sc-members (k-sc-names bs))
      (set k-sc-node-names (k-sc-names nodes))
      (set k-sc-node-binding binding)
      (set k-sc-skip-dead skip)
      (set k-sc-calls nil)
      (set k-sc-hints nil)
      (set k-sc-passed nil)
      (set k-sc-arg-tys nil)
      (set k-sc-invariant nil)
      (set k-sc-escapes nil)
      (set k-sc-too-many #f)
      (let ((walked (k-sc-walk-members nodes 0)))
        (cond ((not (null? (get k-sc-escapes))) (k-sc-escape-why))
              ((not walked) "it is not a lambda")
              (else
               (let ((inv (k-sc-invariants (k-sc-all-params nodes 0 nil))))
                 (if (null? inv)
                     ""
                     (begin
                       (set k-sc-invariant inv)
                       (set k-sc-calls nil)
                       (set k-sc-hints nil)
                       (set k-sc-passed nil)
                       (set k-sc-arg-tys nil)
                       (let ((again (k-sc-walk-members nodes 0)))
                         (cond ((not (null? (get k-sc-escapes))) (k-sc-escape-why))
                               ((not again) "it is not a lambda")
                               (else ""))))))))))))
(define k-termination-one (->* (k-letrec-bs) string)
  (lambda (bs)
    (let ((why (k-sc-walked bs bs (k-sc-upto 0 (k-length bs)) #f)))
      (if (string=? why "") (k-sc-calls-why) why))))

;;; ------------------------------------------------------------ by member

;; Each binding of `bs` at each member of its `allof` (at its type, for one of
;; no `allof`): the nodes walked, and of each, its binding, from `i`.
(define k-sc-nodes (->* (k-letrec-bs) k-letrec-bs)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((b (car bs)) (ms (k-sc-members-of (extract b 2)))
               (ts (if (null? ms) (the k-ids (cons (extract b 2) nil)) ms)))
          (k-sc-nodes-at b ts (k-sc-nodes (cdr bs)))))))
(define k-sc-nodes-at (->* ((productof (1 symbol) (2 int) (3 kx)) k-ids k-letrec-bs) k-letrec-bs)
  (lambda (b ts rest)
    (if (null? ts)
        rest
        (cons (product (1 (extract b 1)) (2 (car ts)) (3 (extract b 3)))
              (k-sc-nodes-at b (cdr ts) rest)))))
(define k-sc-node-bindings (->* (k-letrec-bs int) k-ids)
  (lambda (bs i)
    (if (null? bs)
        nil
        (let ((ms (k-sc-members-of (extract (car bs) 2))))
          (k-ids-repeat i (if (null? ms) 1 (k-length ms)) (k-sc-node-bindings (cdr bs) (+ i 1)))))))
(define k-ids-repeat (->* (int int k-ids) k-ids)
  (lambda (x n rest) (if (= n 0) rest (k-ids-repeat x (- n 1) (the k-ids (cons x rest))))))
;; Whether arguments of types `ts` (-1 not known) fit parameters `ps`.
(define k-sc-fit? (->* (k-ids k-ids) bool)
  (lambda (ts ps)
    (if (null? ts)
        (null? ps)
        (and (not (null? ps))
             (or (< (car ts) 0) (k-subtype (car ts) (car ps)))
             (k-sc-fit? (cdr ts) (cdr ps))))))
;; The calls, oldest first, each to every node of its binding whose member
;; its arguments fit: as edges from node to node, oldest first, with their
;; hints (`hs`) alongside.
(define k-sc-expand (->* (k-calls k-texts (listof k-ids acyclic) k-letrec-bs k-ids) k-edges-hints)
  (lambda (cs hs tys nodes binding)
    (if (null? cs)
        (product (1 nil) (2 nil))
        (let ((rest (k-sc-expand (cdr cs) (cdr hs) (cdr tys) nodes binding))
              (out (k-sc-expand-one (car cs) (car hs) (car tys) nodes binding 0)))
          (product (1 (k-calls-append (extract out 1) (extract rest 1)))
                   (2 (k-texts-append (extract out 2) (extract rest 2))))))))
(define k-sc-expand-one (->* (k-call string k-ids k-letrec-bs k-ids int) k-edges-hints)
  (lambda (c h ts nodes binding n)
    (if (null? nodes)
        (product (1 nil) (2 nil))
        (let ((rest (k-sc-expand-one c h ts (cdr nodes) (cdr binding) (+ n 1))))
          (if (and (= (car binding) (extract c 2))
                   (k-sc-fit? ts (k-sc-param-types (extract (car nodes) 2))))
              (let ((edge (product (1 (extract c 1)) (2 n) (3 (extract c 3)))))
                (product (1 (cons edge (extract rest 1))) (2 (cons h (extract rest 2)))))
              rest)))))
(define k-calls-append (->* (k-calls k-calls) k-calls)
  (lambda (a b) (if (null? a) b (cons (car a) (k-calls-append (cdr a) b)))))
(define k-texts-append (->* (k-texts k-texts) k-texts)
  (lambda (a b) (if (null? a) b (the k-texts (cons (car a) (k-texts-append (cdr a) b))))))
;; The nodes reachable from those of `todo`, by `edges`, onto `seen`.
(define k-sc-reach (->* (k-ids k-ids k-calls) k-ids)
  (lambda (todo seen edges)
    (cond ((null? todo) seen)
          ((k-has-id? seen (car todo)) (k-sc-reach (cdr todo) seen edges))
          (else (k-sc-reach (k-sc-callees edges (car todo) (cdr todo))
                            (the k-ids (cons (car todo) seen)) edges)))))
(define k-sc-callees (->* (k-calls int k-ids) k-ids)
  (lambda (edges n out)
    (cond ((null? edges) out)
          ((= (extract (car edges) 1) n)
           (k-sc-callees (cdr edges) n (the k-ids (cons (extract (car edges) 2) out))))
          (else (k-sc-callees (cdr edges) n out)))))
;; Of `edges` and their hints `hs`, those from a node of `reach`.
(define k-sc-from (->* (k-calls k-texts k-ids) k-edges-hints)
  (lambda (edges hs reach)
    (if (null? edges)
        (product (1 nil) (2 nil))
        (let ((rest (k-sc-from (cdr edges) (cdr hs) reach)))
          (if (k-has-id? reach (extract (car edges) 1))
              (product (1 (cons (car edges) (extract rest 1))) (2 (cons (car hs) (extract rest 2))))
              rest)))))
;; Why node `n` may not end, or "": the calls reachable from it, each loop.
(define k-sc-node-why (->* (int k-calls k-texts) string)
  (lambda (n edges hs)
    (let ((from (k-sc-from edges hs (k-sc-reach (the k-ids (cons n nil)) nil edges))))
      (begin (set k-sc-calls (the k-calls (reverse (extract from 1))))
             (set k-sc-hints (the k-texts (reverse (extract from 2))))
             (set k-sc-too-many #f)
             (k-sc-calls-why)))))
;; For each node from `n`, why it may not end, or "", after those of `done`
;; (newest first).
(define k-sc-node-whys (->* (int int k-calls k-texts k-texts) k-texts)
  (lambda (n count edges hs done)
    (if (= n count)
        (the k-texts (reverse done))
        (let ((why (k-sc-node-why n edges hs)))
          (k-sc-node-whys (+ n 1) count edges hs (the k-texts (cons why done)))))))
;; For each binding of the group `bs`, for each member of its `allof` (one,
;; its type, for a binding of no `allof`): why a run from a call of it at
;; that member may not end, or "". An `allof`'s body is walked once at each
;; member's types, passing over what they rule out; each call goes to every
;; member its arguments' types fit, where they are known (to each where they
;; are not). As Rust's `termination_by_member`.
(define k-termination-by-member (->* (k-letrec-bs) (listof k-texts acyclic))
  (lambda (bs)
    (let* ((nodes (k-sc-nodes bs))
           (binding (k-sc-node-bindings bs 0))
           (why (k-sc-walked bs nodes binding #t)))
      (if (not (string=? why ""))
          (k-sc-by-binding binding (k-sc-same-texts (k-length nodes) why nil) 0)
          (let ((ex (k-sc-expand (reverse (get k-sc-calls)) (reverse (get k-sc-hints))
                                 (reverse (get k-sc-arg-tys)) nodes binding)))
            (k-sc-by-binding
             binding (k-sc-node-whys 0 (k-length nodes) (extract ex 1) (extract ex 2) nil) 0))))))
(define k-sc-same-texts (->* (int string k-texts) k-texts)
  (lambda (n s out) (if (= n 0) out (k-sc-same-texts (- n 1) s (the k-texts (cons s out))))))
;; The nodes' whys grouped by binding, from binding `i`.
(define k-sc-by-binding (->* (k-ids k-texts int) (listof k-texts acyclic))
  (lambda (binding whys i)
    (if (null? binding)
        nil
        (let ((mine (k-sc-whys-of binding whys i)) (rest (k-sc-whys-past binding whys i)))
          (cons mine (k-sc-by-binding (extract rest 1) (extract rest 2) (+ i 1)))))))
(define k-sc-whys-of (->* (k-ids k-texts int) k-texts)
  (lambda (binding whys i)
    (if (or (null? binding) (not (= (car binding) i)))
        nil
        (the k-texts (cons (car whys) (k-sc-whys-of (cdr binding) (cdr whys) i))))))
(define k-sc-whys-past (->* (k-ids k-texts int) (productof (1 k-ids) (2 k-texts)))
  (lambda (binding whys i)
    (if (or (null? binding) (not (= (car binding) i)))
        (product (1 binding) (2 whys))
        (k-sc-whys-past (cdr binding) (cdr whys) i))))
;; Each binding's members' whys kept, as whether each may not end.
(define k-note-member-spins (->* (k-letrec-bs (listof k-texts acyclic)) unit)
  (lambda (bs by)
    (if (null? bs)
        #u
        (let ((m (product (1 (extract (car bs) 1)) (2 (extract (car bs) 2))
                          (3 (k-texts-nonempty (car by))))))
          (begin (set k-member-spins (cons m (get k-member-spins)))
                 (k-note-member-spins (cdr bs) (cdr by)))))))
(define k-texts-nonempty (->* (k-texts) (listof bool acyclic))
  (lambda (ws)
    (if (null? ws) nil (cons (not (string=? (car ws) "")) (k-texts-nonempty (cdr ws))))))
;; The first why of all, or "".
(define k-first-why (->* ((listof k-texts acyclic)) string)
  (lambda (by)
    (cond ((null? by) "")
          ((null? (car by)) (k-first-why (cdr by)))
          ((string=? (car (car by)) "")
           (k-first-why (the (listof k-texts acyclic) (cons (cdr (car by)) (cdr by)))))
          (else (car (car by))))))
;; Note why each of `g` may not end.
(define k-note-why (->* (k-letrec-bs string) unit)
  (lambda (g why)
    (if (null? g)
        #u
        (let ((w (product (1 (extract (car g) 1)) (2 (extract (car g) 2)) (3 why))))
          (begin (set k-spin-why (cons w (get k-spin-why)))
                 (k-note-why (cdr g) why))))))
(define k-why-of (->* (k-whys symbol int) string)
  (lambda (ws n t)
    (cond ((null? ws) "")
          ((and (symbol=? (extract (car ws) 1) n) (= (extract (car ws) 2) t)) (extract (car ws) 3))
          (else (k-why-of (cdr ws) n t)))))
;; Whether `needle` is in `hay` at `i`.
(define k-text-at? (->* (string string int) bool)
  (lambda (hay needle i) (string=? (substring hay i (+ i (string-length needle))) needle)))
(define k-text-has? (->* (string string int) bool)
  (lambda (hay needle i)
    (and (<= (+ i (string-length needle)) (string-length hay))
         (or (k-text-at? hay needle i) (k-text-has? hay needle (+ i 1))))))
;; Where `needle` is in `hay`, from `i`, or -1.
(define k-text-find (->* (string string int) int)
  (lambda (hay needle i)
    (cond ((> (+ i (string-length needle)) (string-length hay)) -1)
          ((k-text-at? hay needle i) i)
          (else (k-text-find hay needle (+ i 1))))))
;; Where line `i` of `m` ends: its newline, or the end.
(define k-line-end (->* (string int) int)
  (lambda (m i)
    (cond ((>= i (string-length m)) i)
          ((char=? (string-ref m i) #\newline) i)
          (else (k-line-end m (+ i 1))))))
;; Whether error `m` is about `spin`: its effect beyond what is expected, if
;; it says one, names it; else the message does (`check.rs`'s `about_spin`).
(define k-about-spin? (->* (string) bool)
  (lambda (m)
    (let ((i (k-text-find m "beyond what is expected, it has " 0)))
      (if (< i 0)
          (k-text-has? m "spin" 0)
          (k-text-has? (substring m i (k-line-end m i)) "spin" 0)))))
;; Why a wait inside `a`..`b` may not end: the first's, by where it starts
;; and ends, of `ws`, else "" (`k-waits-spun`; `check.rs`'s `declared_error`).
(define k-waits-why (->* ((listof (productof (1 int) (2 int) (3 string)) acyclic) int int) string)
  (lambda (ws a b) (k-waits-best ws a b -1 -1 "")))
;; The loop of `k-waits-why`: `s`..`e` where the best so far starts and
;; ends, `why` its, or `s` -1.
(define k-waits-best
  (->* ((listof (productof (1 int) (2 int) (3 string)) acyclic) int int int int string) string)
  (lambda (ws a b s e why)
    (if (null? ws)
        why
        (let* ((w (car ws)) (ws1 (extract w 1)) (we (extract w 2)))
          (if (and (<= a ws1) (<= we b)
                   (or (< s 0) (< ws1 s) (and (= ws1 s) (< we e))))
              (k-waits-best (cdr ws) a b ws1 we (extract w 3))
              (k-waits-best (cdr ws) a b s e why))))))
;; Error `m` where `n`, declared `t`, is defined at `a`..`b`: saying so, and,
;; if about `spin`, why, on the line it is about, before why control was not
;; masked: its group's, else a wait's inside it.
(define k-declared-error (->* (string symbol int int int) string)
  (lambda (m n t a b)
    (let* ((group (k-why-of (get k-spin-why) n t))
           (why (if (string=? group "") (k-waits-why (get k-waits-spun) a b) group))
           (spins (and (not (string=? why "")) (k-about-spin? m)))
           (tail (if spins (string-append "; it may not end: " why) ""))
           (at (k-text-find m (string-append k-newline "  " k-undelimited) 0))
           (declared (k-cat4 (k-quote (symbol->string n)) " is declared a " (k-show-ty t) ": ")))
      (if (< at 0)
          (k-cat4 declared m tail "")
          (k-cat4 declared (substring m 0 at) tail (substring m at (string-length m)))))))
;; `f`, checking what `n` is declared `t`; an error at `a`..`b` itself says
;; so, and, if it is about `spin` and `n`'s group may not end, why not.
(define k-declaring (->* (k-thunk int int symbol int) k-te)
  (lambda (f a b n t)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb)
          (if (and (= ea a) (= eb b))
              (k-fail (k-declared-error m n t a b) ea eb)
              (k-fail m ea eb)))
        (k-ok (xs) (k-fail "k-ok inside" a b))))))

;; The error for `n`, bound in a recursive group to `x`, which is not a lambda.
(define k-fail-not-lambda (->* (symbol kx) void)
  (lambda (n x) (k-fail (k-letrec-not-lambda n) (k-start x) (k-end x))))
;; Every binding of a `letrec` a lambda, or an error at the first that is not.
(define k-letrec-lambdas (->* (k-letrec-bs) unit)
  (lambda (bs)
    (cond ((null? bs) #u)
          ((k-lambda? (extract (car bs) 3)) (k-letrec-lambdas (cdr bs)))
          (else (k-fail-not-lambda (extract (car bs) 1) (extract (car bs) 3)))))))))
