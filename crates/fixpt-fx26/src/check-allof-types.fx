;;; The signature of `check-allof.fx`, its `check-allof-module`, as its
;;; clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; The types it names, from the files that define them.
(hide (define check-types-types (load-module "fx26:check-types-types.fx"))
      (define check-synth-types (load-module "fx26:check-synth-types.fx"))
      (define check-subtype-types (load-module "fx26:check-subtype-types.fx")))
(import check-types-types (type kx kxs k-te k-eff k-regions) (effect checks))
(import check-synth-types (type k-done k-nars))
(import check-subtype-types (type k-checking))
;; What the rules give it of their recursive group: `k-check`, `k-synth`,
;; and what a call's type and effect are once its arguments' are known
;; (`k-app-result`).
(define-type k-check-fn (subr (maxeff checks spin) (kx int) k-eff))
(define-type k-synth-fn (subr (maxeff checks spin) (kx) k-te))
(define-type k-result-fn (subr (maxeff checks spin) (kx kx int kxs k-eff k-eff int) k-te))
(define-type k-app-fn (subr (maxeff checks spin) (kx kx kxs int) k-te))
;; What its clients use of it (`check-rules.fx`).
(define-type check-allof-sig
  (moduleof (val k-allof-type? (subr (maxeff checks spin) (int) bool))
            (val k-allof-lambda (subr (maxeff checks spin) (kx int k-check-fn) k-eff))
            (val k-allof-call
                 (subr (maxeff checks spin)
                       (kx kx int kxs k-done k-te k-synth-fn k-result-fn k-check-fn) k-te))
            (val k-arm-dead? (subr (maxeff checks spin) (int symbol kx) bool))
            (val k-branch-synth (subr (maxeff checks spin) (kx k-nars k-synth-fn) k-te))
            (val k-branch-check (subr (maxeff checks spin) (kx int k-nars k-check-fn) k-eff))
            (val k-split-app (subr (maxeff checks spin) (kx kx kxs int k-app-fn k-synth-fn) k-te))
            (val k-as-argument (subr (maxeff checks spin) (k-checking kx int) k-te))
            (val k-meet (subr (maxeff checks spin) (int int k-regions) int))))
