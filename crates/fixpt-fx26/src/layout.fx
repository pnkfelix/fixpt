;;; The object layout, generated from `crates/fixpt-heap/src/layout.rs`.
;;; Do not edit: change the table there and regenerate, with
;;;   FIXPT_BLESS=1 cargo test -p fixpt-fx26 --test layout
;;; See `docs/object-model.md`.

;;; Tags: the low three bits of every word.
(define tag-fixnum int 0)  ; 61-bit signed integer; also what a zeroed word is
(define tag-pair int 1)  ; index of a two-word car/cdr cell, which has no header
(define tag-unused int 2)  ; retired: pointed at an object's header, before every object was a bloblet
(define tag-immediate int 3)  ; #f, #t, (), unit, eof, characters, …
(define tag-bloblet int 4)  ; index of the start of a bloblet's suffix
(define tag-trailer int 5)  ; the last field of a bloblet that has one; runtime-reserved payload
(define tag-header int 6)  ; never a value: starts an object
(define tag-forward int 7)  ; a forwarding pointer, only during a collection
(define tag-bits int 3)

;;; The header word's bit fields: lowest bit, and width.
(define header-tag-lo int 0)
(define header-tag-width int 3)  ; 110, the header tag
(define header-kind-lo int 3)
(define header-kind-width int 8)  ; what the object is to the language
(define header-large-lo int 11)
(define header-large-width int 1)  ; F is too big for this word: it is in the next one
(define header-fields-frozen-lo int 12)
(define header-fields-frozen-width int 1)  ; the fields are immutable
(define header-suffix-frozen-lo int 13)
(define header-suffix-frozen-width int 1)  ; the suffix is immutable
(define header-fields-lo int 14)
(define header-fields-width int 18)  ; F, the number of tagged fields
(define header-bytes-lo int 32)
(define header-bytes-width int 32)  ; B, the suffix length in bytes
(define extension-fields-lo int 11)
(define extension-fields-width int 53)  ; F, for an object whose F does not fit the main header

;;; Kinds.
(define kind-string int 1)
(define kind-symbol int 2)
(define kind-vector int 3)
(define kind-bytevector int 4)
(define kind-flonum int 5)
(define kind-bignum int 6)
(define kind-ratnum int 7)
(define kind-closure int 8)
(define kind-code int 9)
(define kind-box int 10)
(define kind-record int 11)
(define kind-record-type int 12)
(define kind-port int 13)
(define kind-continuation int 14)
(define kind-values int 15)
(define kind-promise int 16)
(define kind-hash-table int 17)
(define kind-environment int 18)
(define kind-primitive int 19)
(define kind-bloblet int 32)
(define kind-threaded-code int 33)
(define kind-compiled-code int 34)
(define kind-env-frame int 35)
(define kind-extension int 255)

;;; A closure's fields, and an environment frame's, by negative offset.
(define closure-code int 2)
(define closure-extra0 int 3)
(define frame-parent int 2)
(define frame-slot0 int 3)

;;; A code bloblet's fields, by negative offset from its code. 1 is the trailer.
(define code-entry int 2)
(define code-frame int 3)
(define code-free int 4)
(define code-has-rest int 5)
(define code-arity int 6)
(define code-name int 7)
(define code-items int 8)
(define code-item0 int 9)

;;; A threaded word's fields, by negative offset, and its routines by number.
(define word-entry int 2)
(define word-name int 3)
(define word-cell0 int 4)
(define routine-docol int 0)  ; run a word's cells
(define routine-exit int 1)  ; return to the calling word
(define routine-halt int 2)  ; stop, leaving the data stack as the result
(define routine-lit int 3)  ; ( -- x ), x the next cell
(define routine-branch int 4)  ; skip the next cell's fixnum of cells, counted after it
(define routine-zbranch int 5)  ; ( flag -- ), branch if flag is #f
(define routine-execute int 6)  ; ( w -- ), run a word, or a primitive given as its fixnum
(define routine-dup int 7)  ; ( a -- a a )
(define routine-drop int 8)  ; ( a -- )
(define routine-swap int 9)  ; ( a b -- b a )
(define routine-over int 10)  ; ( a b -- a b a )
(define routine-add int 11)  ; ( a b -- a+b ), fixnums
(define routine-sub int 12)  ; ( a b -- a-b ), fixnums
(define routine-less int 13)  ; ( a b -- a<b ), fixnums
(define routine-eq int 14)  ; ( a b -- flag ), the same Value
(define routine-field-ref int 15)  ; ( obj k -- x ), field k of a bloblet
(define routine-field-set int 16)  ; ( x obj k -- ), field k of a bloblet
(define routine-cons int 17)  ; ( a b -- pair )
(define routine-car int 18)  ; ( pair -- a )
(define routine-cdr int 19)  ; ( pair -- b )
