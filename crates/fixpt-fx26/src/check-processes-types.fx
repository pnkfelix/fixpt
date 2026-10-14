;;; The signature of `check-processes.fx`, its `check-processes-module`, as
;;; its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-rules.fx`).
;; The types it names, from the files that define them.
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(define-type kx (select check-types-types kx))
(define-type kxs (select check-types-types kxs))
(define-type k-te (select check-types-types k-te))
(define-effect checks (select check-types-types checks))
(define-effect kreads (select check-types-types kreads))
;; What synthesizes an expression's type and effect: the rules' `k-synth`.
(define-type k-synth-fn (subr (maxeff checks spin) (kx) k-te))
(define-type check-processes-sig
  (moduleof (val k-library-type (subr (maxeff kreads spin) (symbol kx) int))
            (val k-library-op (subr (maxeff kreads spin) (kx kxs) string))
            (val k-library-with (subr (maxeff checks spin) (int kx int int int) k-te))
            (val k-spawn-te (subr (maxeff checks spin) (kx kx kxs int k-synth-fn) k-te))
            (val k-par-te (subr (maxeff checks spin) (kx kx kxs k-synth-fn) k-te))
            (val k-synth-fx (subr (maxeff checks spin) (kx int kx int int) k-te))
            (val k-note-fx-plain-op (subr (maxeff checks spin) (kx) unit))
            (val k-note-fx-plain (subr (maxeff checks spin) (kx int int) unit))))
