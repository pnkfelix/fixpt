;;; The eager reader's states, in FX-26: what a feed returns, which holds
;;; the reader's continuation while it waits for a character. A module file
;;; of the reader's regions, which only `eager-reader.fx` loads; the types
;;; its clients use are in `eager-reader-types.fx`, which mentions no
;;; continuation (kayak's request, 2026-10-15).

(module-parameters ((rs region) (re region) (rm region) (rc region)))
(hide (define reader-types ((proj (load-module "fx26:eager-reader-types.fx") rs re rm rc))))
(import reader-types (type syns) (effect parsing))

;; What a feed returns: waiting for a character, or stopped at an error.
;; Fields: need?, the continuation (one, when waiting), and then, as a
;; `state-rest`, the position, the complete top-level data (newest first),
;; and the message.
(define-type state-rest (pairof int (pairof syns string rs) rs))
(define-type state
  (dletrec ((st (pairof bool (pairof (listof k acyclic) state-rest rs) rs))
            (k (composable char st (maxeff parsing spin) re)))
    st))
(define-type cont (composable char state (maxeff parsing spin) re))
