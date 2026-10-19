;;; The native convention's compiler to x86_64 written in FX-26, its
;;; modules applied as the conductor applies them (`tests/native_direct_x64.rs`).
(define x86-64 (load-input "fx26:x86_64.fx"))
(define dl (load-module "fx26:native-direct-x64-layout.fx"))
(define layout (load-module "fx26:layout.fx"))
(define asm ((load-input "fx26:native-direct-x64-asm.fx") x86-64 dl))
(define reps ((load-input "fx26:native-reps.fx") dl layout))
(define raw ((load-input "fx26:native-direct-x64-raw.fx") x86-64 dl asm))
(define flat ((load-input "fx26:native-direct-x64-flat.fx") x86-64 dl asm raw))
(define proc ((load-input "fx26:native-direct-x64-proc.fx") dl layout asm reps))
(define ops
  ((load-input "fx26:native-direct-x64-ops.fx") x86-64 dl layout asm reps raw proc))
(define prims
  ((load-input "fx26:native-direct-x64-prims.fx") x86-64 dl layout asm reps raw flat proc))
(define direct
  ((load-input "fx26:native-direct-x64.fx") x86-64 dl layout asm reps raw proc ops prims))
(define native-compile-x64-proc (with direct native-compile-x64-proc))
