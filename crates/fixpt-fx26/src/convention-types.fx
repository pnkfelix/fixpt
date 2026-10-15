;;; The types of `convention.fx`: a native convention as data a generator
;;; reads (`TODO.md` §97, `docs/research/declared-conventions.md`, step 6).
;;; A register is its number, `x0` 0 to `x30` 30, `sp` 31; an offset in the
;;; state is in bytes from the state's register; a frame's are from the
;;; frame's register. A module file of no state, which `convention.fx`
;;; loads, and so may its clients, to name the types.

;; A text read: a name, an integer, or a list of them.
(define-datatype cv-sx (cx-name string) (cx-int int) (cx-list (listof cv-sx acyclic)))
(define-type cv-sxs (listof cv-sx acyclic))
;; What reading does: read the module's procedures, and count down.
(define-effect cvr (maxeff (read @globals) spin))
;; A text read from a place in a string, and the place after it.
(define-type cv-at (productof (x cv-sx) (at int)))
(define-type cv-sxs-at (productof (xs cv-sxs) (at int)))

;; Names and their numbers, in the declaration's order: tags, immediates,
;; kinds, a trap's kinds.
(define-type cv-names (listof (productof (name string) (number int)) acyclic))
(define-type cv-ints (listof int acyclic))
(define-type cv-strs (listof string acyclic))
;; Roles and their registers: a routine's inputs.
(define-type cv-regs (listof (productof (name string) (registers cv-ints)) acyclic))

(define-type cv-registers
  (productof (arguments cv-ints) (rest-in int) (count int) (result int) (closure int)
             (link int) (frame int)
             ;; Pinned: never changed by code, but fuel as `cv-fuel` says.
             (state int) (fuel int) (stack-limit int) (code-distance int)))

;; A header's field: its first bit and its width.
(define-type cv-bits (listof (productof (name string) (at int) (width int)) acyclic))
(define-type cv-values
  (productof (tags cv-names) (fixnum-shift int) (fixnum-bits int) (immediates cv-names)
             (char-subtag int) (char-payload-shift int)
             ;; A pair's fields, from its reference.
             (car int) (cdr int)
             ;; A bloblet's reference: its suffix plus this, the tag; field
             ;; `k` is `8k` + this before the suffix.
             (bloblet-past-suffix int) (field-k-before-suffix int)
             (header cv-bits) (kinds cv-names)))

;; `code-field` is the code bloblet's; its code is native code when at or
;; past the state's field at `native-when-code-at-least`.
(define-type cv-closures
  (productof (kind int) (code-field int) (first-free-field int) (native-when-code-at-least int)))

;; A code bloblet's code runs at its reference plus the code distance's
;; register; field `k` is `8k` + this before its first instruction.
(define-type cv-code (productof (field-k-before-code int)))

;; A frame, from its register: its header, link, return, stack map and
;; first value slot. A map's bit `k` below `live-below` is value slot `k`
;; live; above `fields-above`, the count of the frame's fields; negative,
;; every value live. `stub` is a stub's frame's size.
(define-type cv-frames
  (productof (align int) (header int) (link int) (return int) (map int) (values-from int)
             (live-below int) (fields-above int) (stub int)))

;; The state's fields that code reads or writes, by offset.
(define-type cv-state
  (productof (fuel int) (reserve int) (trap int) (pc int) (args int) (nargs int) (aux int)
             (callout int) (rust-sp int) (native-sp int) (fp int) (top int) (words int)
             (alloc-limit int) (code int) (clo int) (delta int) (code-lo int) (trap-stub int)
             (foreign int) (closure int) (cards int) (stack-limit int) (overflow int) (poll int)
             (cons int)))

;; A routine: its entry's offset in the state, called by `blr`; its inputs,
;; each a role and its registers; its output's register, -1 for none; whether
;; it may collect.
(define-type cv-routine
  (productof (entry int) (in cv-regs) (out int) (may-collect bool)))
;; `overflow`, when `sp` is below the stack limit's register once a frame is
;; made: its entry called with the return in `x30`, the code bloblet in
;; `code`, in `info` the arguments held (`held-width` bits from `held-at`),
;; whether the closure was read and whether the procedure is variadic (bits
;; `closure-read`, `variadic`). It keeps the registers in `keeps`.
(define-type cv-overflow
  (productof (entry int) (code int) (info int) (held-at int) (held-width int)
             (closure-read int) (variadic int) (keeps cv-ints)))
;; `trap`: its kind in `kind`, each kind's number and name.
(define-type cv-trap (productof (entry int) (kind int) (kinds cv-names)))
(define-type cv-routines
  (productof (foreign cv-routine) (overflow cv-overflow) (poll cv-routine) (cons cv-routine)
             (trap cv-trap)))

;; Fuel: in `register`, less `subtract` on entry and on a back edge; at
;; zero, a call of `poll`.
(define-type cv-fuel (productof (register int) (subtract int)))
;; A store of a value marks `mark` at the card table (at `cards` in the
;; state) plus the address shifted right by `card-shift`.
(define-type cv-barrier (productof (cards int) (card-shift int) (mark int)))

(define-type convention
  (productof (target string) (registers cv-registers) (values cv-values)
             (closures cv-closures) (code cv-code) (frames cv-frames) (state cv-state)
             (routines cv-routines) (fuel cv-fuel) (barrier cv-barrier)))

;; A declaration read: the convention, or why not.
(define-type cv-read (sumof (ok convention) (refused string)))
