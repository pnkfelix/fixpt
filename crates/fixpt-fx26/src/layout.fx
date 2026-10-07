;;; The object layout, generated from `crates/fixpt-heap/src/layout.rs`.
;;; Do not edit: change the table there and regenerate, with
;;;   FIXPT_BLESS=1 cargo test -p fixpt-fx26 --test layout
;;; See `docs/object-model.md`.

;;; Tags: the low three bits of every word.
;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define layout-module (module
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
(define kind-flat-array int 42)
(define kind-eqtable int 43)
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
(define routine-int-add int 43)  ; ( a b -- a+b ), ints: a bignum past a fixnum
(define routine-int-sub int 44)  ; ( a b -- a-b ), ints: a bignum past a fixnum
(define routine-int-less int 45)  ; ( a b -- a<b ), ints
(define routine-pair-car int 46)  ; ( pair -- a ), a pair
(define routine-pair-cdr int 47)  ; ( pair -- b ), a pair
(define routine-field int 48)  ; ( obj -- x ), field k of a bloblet that has it; k the next cell
(define routine-rest int 49)  ; ( -- list ), this frame's values, from slot 0, as a list
(define routine-int-eq int 50)  ; ( a b -- a=b ), ints, fixnums or bignums

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
(define register-regs int 8)))

(define tag-fixnum (with layout-module tag-fixnum))
(define tag-pair (with layout-module tag-pair))
(define tag-unused (with layout-module tag-unused))
(define tag-immediate (with layout-module tag-immediate))
(define tag-bloblet (with layout-module tag-bloblet))
(define tag-trailer (with layout-module tag-trailer))
(define tag-header (with layout-module tag-header))
(define tag-forward (with layout-module tag-forward))
(define tag-bits (with layout-module tag-bits))
(define header-tag-lo (with layout-module header-tag-lo))
(define header-tag-width (with layout-module header-tag-width))
(define header-kind-lo (with layout-module header-kind-lo))
(define header-kind-width (with layout-module header-kind-width))
(define header-large-lo (with layout-module header-large-lo))
(define header-large-width (with layout-module header-large-width))
(define header-fields-frozen-lo (with layout-module header-fields-frozen-lo))
(define header-fields-frozen-width (with layout-module header-fields-frozen-width))
(define header-suffix-frozen-lo (with layout-module header-suffix-frozen-lo))
(define header-suffix-frozen-width (with layout-module header-suffix-frozen-width))
(define header-fields-lo (with layout-module header-fields-lo))
(define header-fields-width (with layout-module header-fields-width))
(define header-bytes-lo (with layout-module header-bytes-lo))
(define header-bytes-width (with layout-module header-bytes-width))
(define extension-fields-lo (with layout-module extension-fields-lo))
(define extension-fields-width (with layout-module extension-fields-width))
(define kind-string (with layout-module kind-string))
(define kind-symbol (with layout-module kind-symbol))
(define kind-vector (with layout-module kind-vector))
(define kind-bytevector (with layout-module kind-bytevector))
(define kind-flonum (with layout-module kind-flonum))
(define kind-bignum (with layout-module kind-bignum))
(define kind-ratnum (with layout-module kind-ratnum))
(define kind-closure (with layout-module kind-closure))
(define kind-code (with layout-module kind-code))
(define kind-box (with layout-module kind-box))
(define kind-record (with layout-module kind-record))
(define kind-record-type (with layout-module kind-record-type))
(define kind-port (with layout-module kind-port))
(define kind-continuation (with layout-module kind-continuation))
(define kind-values (with layout-module kind-values))
(define kind-promise (with layout-module kind-promise))
(define kind-hash-table (with layout-module kind-hash-table))
(define kind-environment (with layout-module kind-environment))
(define kind-primitive (with layout-module kind-primitive))
(define kind-bloblet (with layout-module kind-bloblet))
(define kind-cellular-code (with layout-module kind-cellular-code))
(define kind-compiled-code (with layout-module kind-compiled-code))
(define kind-env-frame (with layout-module kind-env-frame))
(define kind-sum (with layout-module kind-sum))
(define kind-product (with layout-module kind-product))
(define kind-cellular-closure (with layout-module kind-cellular-closure))
(define kind-cellular-continuation (with layout-module kind-cellular-continuation))
(define kind-register-code (with layout-module kind-register-code))
(define kind-native-closure (with layout-module kind-native-closure))
(define kind-flat-array (with layout-module kind-flat-array))
(define kind-eqtable (with layout-module kind-eqtable))
(define kind-extension (with layout-module kind-extension))
(define closure-code (with layout-module closure-code))
(define closure-extra0 (with layout-module closure-extra0))
(define frame-parent (with layout-module frame-parent))
(define frame-slot0 (with layout-module frame-slot0))
(define code-entry (with layout-module code-entry))
(define code-frame (with layout-module code-frame))
(define code-free (with layout-module code-free))
(define code-has-rest (with layout-module code-has-rest))
(define code-arity (with layout-module code-arity))
(define code-name (with layout-module code-name))
(define code-items (with layout-module code-items))
(define code-item0 (with layout-module code-item0))
(define word-entry (with layout-module word-entry))
(define word-name (with layout-module word-name))
(define word-twin (with layout-module word-twin))
(define word-cell0 (with layout-module word-cell0))
(define cellular-closure-word (with layout-module cellular-closure-word))
(define cellular-closure-free0 (with layout-module cellular-closure-free0))
(define routine-docol (with layout-module routine-docol))
(define routine-exit (with layout-module routine-exit))
(define routine-halt (with layout-module routine-halt))
(define routine-lit (with layout-module routine-lit))
(define routine-branch (with layout-module routine-branch))
(define routine-zbranch (with layout-module routine-zbranch))
(define routine-execute (with layout-module routine-execute))
(define routine-dup (with layout-module routine-dup))
(define routine-drop (with layout-module routine-drop))
(define routine-swap (with layout-module routine-swap))
(define routine-over (with layout-module routine-over))
(define routine-add (with layout-module routine-add))
(define routine-sub (with layout-module routine-sub))
(define routine-less (with layout-module routine-less))
(define routine-eq (with layout-module routine-eq))
(define routine-field-ref (with layout-module routine-field-ref))
(define routine-field-set (with layout-module routine-field-set))
(define routine-cons (with layout-module routine-cons))
(define routine-car (with layout-module routine-car))
(define routine-cdr (with layout-module routine-cdr))
(define routine-slot (with layout-module routine-slot))
(define routine-slot! (with layout-module routine-slot!))
(define routine-free (with layout-module routine-free))
(define routine-global (with layout-module routine-global))
(define routine-global! (with layout-module routine-global!))
(define routine-closure (with layout-module routine-closure))
(define routine-call (with layout-module routine-call))
(define routine-tailcall (with layout-module routine-tailcall))
(define routine-return (with layout-module routine-return))
(define routine-prim (with layout-module routine-prim))
(define routine-prompt (with layout-module routine-prompt))
(define routine-abort (with layout-module routine-abort))
(define routine-callcomp (with layout-module routine-callcomp))
(define routine-callcc (with layout-module routine-callcc))
(define routine-withmark (with layout-module routine-withmark))
(define routine-firstmark (with layout-module routine-firstmark))
(define routine-currentmarks (with layout-module routine-currentmarks))
(define routine-marksof (with layout-module routine-marksof))
(define routine-withmark-tail (with layout-module routine-withmark-tail))
(define routine-tcall (with layout-module routine-tcall))
(define routine-ttailcall (with layout-module routine-ttailcall))
(define routine-resume (with layout-module routine-resume))
(define routine-undefined (with layout-module routine-undefined))
(define routine-int-add (with layout-module routine-int-add))
(define routine-int-sub (with layout-module routine-int-sub))
(define routine-int-less (with layout-module routine-int-less))
(define routine-pair-car (with layout-module routine-pair-car))
(define routine-pair-cdr (with layout-module routine-pair-cdr))
(define routine-field (with layout-module routine-field))
(define routine-rest (with layout-module routine-rest))
(define routine-int-eq (with layout-module routine-int-eq))
(define rop-args (with layout-module rop-args))
(define rop-const (with layout-module rop-const))
(define rop-global (with layout-module rop-global))
(define rop-setglbl (with layout-module rop-setglbl))
(define rop-reg (with layout-module rop-reg))
(define rop-setreg (with layout-module rop-setreg))
(define rop-movereg (with layout-module rop-movereg))
(define rop-lexical (with layout-module rop-lexical))
(define rop-save (with layout-module rop-save))
(define rop-pop (with layout-module rop-pop))
(define rop-stack (with layout-module rop-stack))
(define rop-setstk (with layout-module rop-setstk))
(define rop-load (with layout-module rop-load))
(define rop-store (with layout-module rop-store))
(define rop-op1 (with layout-module rop-op1))
(define rop-op2 (with layout-module rop-op2))
(define rop-op2imm (with layout-module rop-op2imm))
(define rop-field (with layout-module rop-field))
(define rop-setfield (with layout-module rop-setfield))
(define rop-prim (with layout-module rop-prim))
(define rop-lambda (with layout-module rop-lambda))
(define rop-invoke (with layout-module rop-invoke))
(define rop-tailinvoke (with layout-module rop-tailinvoke))
(define rop-return (with layout-module rop-return))
(define rop-branch (with layout-module rop-branch))
(define rop-branchf (with layout-module rop-branchf))
(define rop-cellular (with layout-module rop-cellular))
(define rop-invokeself (with layout-module rop-invokeself))
(define rop-global-guard (with layout-module rop-global-guard))
(define rop-brancht (with layout-module rop-brancht))
(define rop-vargs (with layout-module rop-vargs))
(define rop-prim1 (with layout-module rop-prim1))
(define rop-prim2 (with layout-module rop-prim2))
(define rop-prim2imm (with layout-module rop-prim2imm))
(define register-regs (with layout-module register-regs))
