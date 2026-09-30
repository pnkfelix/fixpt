;;; The object layout, generated from `crates/fixpt-heap/src/layout.rs`.
;;; Do not edit: change the table there and regenerate, with
;;;   FIXPT_BLESS=1 cargo test -p fixpt-fx26 --test layout
;;; See `docs/object-model.md`.

;;; Tags: the low three bits of every word.
(define tag-fixnum int 0)  ; 61-bit signed integer; also what a zeroed word is
(define tag-pair int 1)  ; index of a two-word car/cdr cell, which has no header
;; retired: pointed at an object's header, before every object was a bloblet
(define tag-unused int 2)
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
(define kind-cellular-code int 33)
(define kind-compiled-code int 34)
(define kind-env-frame int 35)
(define kind-sum int 36)
(define kind-product int 37)
(define kind-cellular-closure int 38)
(define kind-cellular-continuation int 39)
(define kind-register-code int 40)
(define kind-native-closure int 41)
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

;;; A cellular word's fields, by negative offset, and its routines by number.
(define word-entry int 2)
(define word-name int 3)
(define word-twin int 4)
(define word-cell0 int 5)
(define cellular-closure-word int 2)
(define cellular-closure-free0 int 3)
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
(define routine-slot int 20)  ; ( -- x ), slot i of this frame; i the next cell
(define routine-slot! int 21)  ; ( x -- ), into slot i of this frame
(define routine-free int 22)  ; ( -- x ), free value i of the closure running
(define routine-global int 23)  ; ( -- x ), what the cell that is the next cell holds
(define routine-global! int 24)  ; ( x -- ), into the cell that is the next cell
;; ( v1 … vn -- c ), word w closed over the v's; w and n the next cells
(define routine-closure int 25)
;; ( x1 … xn c -- r ), n the next cell: the x's become the callee's frame
(define routine-call int 26)
(define routine-tailcall int 27)  ; ( x1 … xn c -- r ), the same, the x's replacing this frame
(define routine-return int 28)  ; ( … r -- r ), leave this frame, keeping r, and return
(define routine-prim int 29)  ; ( x1 … xn -- r ), the runtime's primitive p; p and n the next cells
(define routine-prompt int 30)  ; ( tag handler thunk -- r ), run the thunk under a prompt for tag
(define routine-abort int 31)  ; ( tag v -- ), to the nearest prompt for tag, whose handler gets v
;; ( proc tag -- r ), call proc with the continuation up to tag's prompt
(define routine-callcomp int 32)
(define routine-callcc int 33)  ; ( proc -- r ), call proc with the whole continuation
(define routine-withmark int 34)  ; ( key v thunk -- r ), run the thunk with key marked v
(define routine-firstmark int 35)  ; ( key default -- v ), the innermost mark for key
(define routine-currentmarks int 36)  ; ( key -- list ), every mark for key, innermost first
(define routine-marksof int 37)  ; ( k key -- list ), the marks for key in continuation k
;; ( key v thunk -- r ), withmark in tail position: the frame is left, and a mark for key on top
;; replaced
(define routine-withmark-tail int 38)
(define routine-tcall int 39)  ; ( x1 … xn c -- r ), call closure c; n the next cell
(define routine-ttailcall int 40)  ; ( x1 … xn c -- ), tail-call closure c; n the next cell
(define routine-resume int 41)  ; ( v k -- ), give continuation k the value v, in this frame's place
(define routine-undefined int 42)  ; ( -- ), trap: called before it was defined
(define routine-int-add int 43)  ; ( a b -- a+b ), ints: overflow checked
(define routine-int-sub int 44)  ; ( a b -- a-b ), ints: overflow checked
(define routine-int-less int 45)  ; ( a b -- a<b ), ints
(define routine-pair-car int 46)  ; ( pair -- a ), a pair
(define routine-pair-cdr int 47)  ; ( pair -- b ), a pair
(define routine-field int 48)  ; ( obj -- x ), field k of a bloblet that has it; k the next cell
(define routine-rest int 49)  ; ( -- list ), this frame's values, from slot 0, as a list

;;; Register code's instructions by number, and how many registers it has.
;; 1: entered with n arguments in REG1…REGn; first, and only first (arities are static: nothing is
;; checked)
(define rop-args int 0)
(define rop-const int 1)  ; 1: RESULT := x, the operand
(define rop-global int 2)  ; 1: RESULT := the value in global cell g
(define rop-setglbl int 3)  ; 1: global cell g := RESULT
(define rop-reg int 4)  ; 1: RESULT := REGk
(define rop-setreg int 5)  ; 1: REGk := RESULT
(define rop-movereg int 6)  ; 2: REGk2 := REGk1
(define rop-lexical int 7)  ; 1: RESULT := free value i of the closure running (REG0)
(define rop-save int 8)  ; 1: push a frame of n slots, each #f
(define rop-pop int 9)  ; 1: pop the frame of n slots
(define rop-stack int 10)  ; 1: RESULT := frame slot n
(define rop-setstk int 11)  ; 1: frame slot n := RESULT
(define rop-load int 12)  ; 2: REGk := frame slot n
(define rop-store int 13)  ; 2: frame slot n := REGk
(define rop-op1 int 14)  ; 1: RESULT := cellular routine r applied to RESULT
(define rop-op2 int 15)  ; 2: RESULT := cellular routine r applied to RESULT and REGk
(define rop-op2imm int 16)  ; 2: RESULT := cellular routine r applied to RESULT and x
(define rop-field int 17)  ; 1: RESULT := field k of the bloblet in RESULT
(define rop-setfield int 18)  ; 2: field k of the bloblet in RESULT := REGj
(define rop-prim int 19)  ; 2: RESULT := runtime primitive p applied to REG1…REGn; may collect
(define rop-lambda int 20)  ; 2: RESULT := a closure of cellular word w over REG1…REGn; may collect
;; 1: call the procedure in RESULT with REG1…REGn; RESULT := its value; may collect
(define rop-invoke int 21)
;; 1: the same in tail position, the frame popped: its value is this one's
(define rop-tailinvoke int 22)
(define rop-return int 23)  ; 0: return RESULT, the frame popped
(define rop-branch int 24)  ; 1: skip the operand's count of cells, counted after it
(define rop-branchf int 25)  ; 1: the same if RESULT is #f
;; 2: cellular routine r with REG1…REGn as its data stack operands; RESULT := what it leaves; may
;; collect
(define rop-cellular int 26)
;; 1: call the procedure running (REG0) with REG1…REGn, by its own entry; RESULT := its value; may
;; collect
(define rop-invokeself int 27)
;; 3: unless global cell g holds a closure made from cellular word w (a cellular closure of w, or a
;; native one whose code was compiled from w), skip the third operand's count of cells, counted
;; after it; RESULT kept
(define rop-global-guard int 28)
(define rop-brancht int 29)  ; 1: the same as branch if RESULT is not #f
;; 0: entered with any number of arguments, their count in a register (x9, natively), in REG1…REGn
;; (past REGS, a list of the rest in the last); first, instead of args, and only first
(define rop-vargs int 30)
;; 1: RESULT := runtime primitive p applied to RESULT: one that never collects
;; (`fixpt_runtime::never_collects`), so that no register need be in the frame
(define rop-prim1 int 31)
(define rop-prim2 int 32)  ; 2: RESULT := such a primitive p applied to RESULT and REGk
(define rop-prim2imm int 33)  ; 2: RESULT := such a primitive p applied to RESULT and x
(define register-regs int 8)
