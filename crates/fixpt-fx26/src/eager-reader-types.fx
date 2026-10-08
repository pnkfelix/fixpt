;;; The eager reader's types, in FX-26: what it reads, its states and
;;; cursors, and what its procedures may do. A module file of the reader's
;;; regions, as `eager-reader.fx` is, which loads it at its own: it holds no
;;; state, so any file may load it, and two loads are the same types, since
;;; FX-26's types are structural (the front end's modules, `TODO.md` §68).

;; The reader's regions: its data, its prompt tag, its mark key, and the
;; lists it hands back (`eager-reader.fx`).
(module-parameters ((rs region) (re region) (rm region) (rc region)))
;; What a reading procedure may do: allocate, read and write its own data,
;; mark, and suspend or fail through its prompt. A delimited parse does the
;; same, less the control on `re` (`parsing`); looking at the data only reads
;; it (`inspects`).
(define-effect own-data (maxeff (alloc rs) (read rs) (write rs)))
(define-effect marks (maxeff (write rm) (read rm)))
(define-effect parsing (maxeff (read @globals) own-data marks))
(define-effect reads (maxeff parsing (goto re) (comefrom re)))
(define-effect inspects (maxeff (read @globals) (read rs)))
;; What most of its procedures do: that, perhaps without end.
(define-effect reading (maxeff reads spin))

(define-type chars (listof char acyclic))
(define-type data (listof datum acyclic))

;; What is read, with where each piece starts and ends. A vector's elements
;; keep theirs; any other datum that is not a list is an `atom`. Each piece
;; also carries the plain datum it reads as, made once, when it was read,
;; from the datums the marks already hold.
(define-datatype syn
  (atom datum int int)
  (lst (listof syn acyclic) datum int int)
  (dotted (listof syn acyclic) syn datum int int)
  (vec (listof syn acyclic) datum int int))
(define-type syns (listof syn acyclic))

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

;; What a suspended parse is in the middle of, as its marks say, in the
;; caller's region `rc`; what is asked of it.
(define-type context (listof datum rc))
(define-type closers (listof char rc))
(define-effect in-context (maxeff (read @globals) (read rc) (alloc rc) spin))
(define-effect asks (maxeff in-context (read rs) (read rm)))

;; Where an atom is being read: where it starts, the data read before it,
;; and the text given ahead when it started, with where that starts. While
;; the atom is all in that text (the origin unchanged, as any feed changes
;; it), its text is taken from there at the end, with no list of its
;; characters.
(define-type atom-in (productof (start int) (data syns) (text string) (origin int)))
