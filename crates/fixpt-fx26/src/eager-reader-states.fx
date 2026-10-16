;;; The eager reader's working state, in FX-26: its cursors, and what a feed
;;; returns, which holds the reader's continuation while it waits for a
;;; character. A module file of the reader's regions, which only
;;; `eager-reader.fx` loads; the types its clients use are in
;;; `eager-reader-types.fx`, which mentions no continuation and no type
;;; abbreviation that mentions itself (kayak's requests, 2026-10-15 and
;;; 2026-10-16).

(module-parameters ((rs region) (re region) (rm region) (rc region)))
(hide (define reader-types ((proj (load-module "fx26:eager-reader-types.fx") rs re rm rc))))
(import reader-types (type chars syns syn) (effect parsing))

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

;; The lookahead character (none once a closing character is consumed), how
;; many characters have been consumed, the top-level data, and — after `#`
;; followed by something that is not a comment — the cursor after that
;; something, which the datum reader takes up.
(define-type cursor (pairof chars (pairof int (pairof syns (listof cursor acyclic) rs) rs) rs))
(define-type cursors (listof cursor acyclic))

;; What was read, and the cursor after it.
(define-type result (pairof syn cursor rs))
;; Some characters, and the cursor after them.
(define-type word (pairof string cursor rs))

;; Where an atom is being read: where it starts, the data read before it,
;; and the text given ahead when it started, with where that starts. While
;; the atom is all in that text (the origin unchanged, as any feed changes
;; it), its text is taken from there at the end, with no list of its
;; characters.
(define-type atom-in (productof (start int) (data syns) (text string) (origin int)))
