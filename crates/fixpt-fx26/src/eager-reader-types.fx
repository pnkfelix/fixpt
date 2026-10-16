;;; The eager reader's types, in FX-26: what it reads, and what its
;;; procedures may do. A module file of the reader's regions, as
;;; `eager-reader.fx` is, which loads it at its own: it holds no state, so
;;; any file may load it, and two loads are the same types, since FX-26's
;;; types are structural (the front end's modules, `TODO.md` §68). The
;;; reader's own working state, its cursors and the states that hold its
;;; continuations, is in `eager-reader-states.fx`, which only the reader
;;; loads, so that a client that wants `syn` meets no continuation and no
;;; recursive abbreviation (kayak's requests, 2026-10-15 and 2026-10-16).

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

;; What a suspended parse is in the middle of, as its marks say, in the
;; caller's region `rc`; what is asked of it.
(define-type context (listof datum rc))
(define-type closers (listof char rc))
(define-effect in-context (maxeff (read @globals) (read rc) (alloc rc) spin))
(define-effect asks (maxeff in-context (read rs) (read rm)))
