;;; The native convention's compiler to arm64 written in FX-26, its modules
;;; applied as the conductor applies them (`tests/native_direct_arm64.rs`,
;;; and `tests/native_x64.rs`'s `compare_direct` with
;;; `FIXPT_FX_DIRECT_ALONE`). Where raw values are kept is of no machine
;;; (`native-reps.fx`): it is given x86_64's layout, as in the conductor.
(define arm64 (load-input "fx26:arm64.fx"))
(define dl (load-module "fx26:native-direct-arm64-layout.fx"))
(define xl (load-module "fx26:native-direct-x64-layout.fx"))
(define layout (load-module "fx26:layout.fx"))
(define asm ((load-input "fx26:native-direct-arm64-asm.fx") arm64 dl))
(define reps ((load-input "fx26:native-reps.fx") xl layout))
(define raw ((load-input "fx26:native-direct-arm64-raw.fx") arm64 dl asm))
(define flat ((load-input "fx26:native-direct-arm64-flat.fx") arm64 dl asm))
(define proc ((load-input "fx26:native-direct-arm64-proc.fx") dl layout asm reps))
(define ops
  ((load-input "fx26:native-direct-arm64-ops.fx") arm64 dl layout asm reps raw proc))
(define prims
  ((load-input "fx26:native-direct-arm64-prims.fx") arm64 dl layout asm reps raw flat proc))
(define direct
  ((load-input "fx26:native-direct-arm64.fx") arm64 dl layout asm reps raw proc ops prims))
(define native-compile-arm64-proc (with direct native-compile-arm64-proc))
