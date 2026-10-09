;;; The signature of `check-sc-graphs.fx`, its `check-sc-graphs-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-proofs.fx`, `check-rules.fx`,
;; `check-test-facts.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type kxs (select check-types-types kxs))
;; The types it names, from the files that define them.
(define check-terminate-types (load-module "fx26:check-terminate-types.fx"))
(define-type k-calls (select check-terminate-types k-calls))
(define-type k-graph (select check-terminate-types k-graph))
(define-type k-guards (select check-terminate-types k-guards))
(define-type k-ids (select check-types-types k-ids))
(define-type k-names (select check-types-types k-names))
(define-type k-passed (select check-terminate-types k-passed))
(define-type k-trs (select check-terminate-types k-trs))
(define-type k-tscope (select check-terminate-types k-tscope))
(define-type kx (select check-types-types kx))
(define-type check-sc-graphs-sig
  (moduleof (val k-op-either? (subr pure (string string string) bool))
            (val k-sc-one? (subr (read @t) (kxs) bool))
            (val k-sc-two? (subr (maxeff (read @globals) (read @t)) (kxs) bool))
            (val k-sc-members (ref k-names @t))
            (val k-sc-current (ref int @t))
            (val k-sc-calls (ref k-calls @t))
            (val k-sc-escapes (ref (listof (pairof int int @t) acyclic) @t))
            (val k-sc-hints (ref (listof string acyclic) @t))
            (val k-sc-too-many (ref bool @t))
            (val k-sc-passed (ref k-passed @t))
            (val k-sc-invariant (ref k-guards @t))
            (val k-sc-guarded?
                 (subr (maxeff (read @globals) (read @t)) (k-guards int int) bool))
            (val k-sc-naturals (ref k-ids @t))
            (val k-sc-with
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (int k-ids k-guards)
                       k-guards))
            (val k-sc-add
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (k-graph int int bool)
                       k-graph))
            (val k-sc-bind
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (symbol k-trs k-tscope)
                       k-tscope))
            (val k-sc-walk
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (kx k-tscope k-guards)
                       unit))))
