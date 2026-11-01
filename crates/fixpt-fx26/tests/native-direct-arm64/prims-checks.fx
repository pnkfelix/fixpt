;;; The primitives' module (`native-direct-arm64-prims.fx`) applied as the
;;; conductor applies it (`compiler.fx`), to be checked
;;; (`native_direct_arm64_prims.rs`).
(define arm64 (load-input "fx26:arm64.fx"))
(define dl (load-module "fx26:native-direct-arm64-layout.fx"))
(define xl (load-module "fx26:native-direct-x64-layout.fx"))
(define layout (load-module "fx26:layout.fx"))
(define asm ((load-input "fx26:native-direct-arm64-asm.fx") arm64 dl))
(define reps ((load-input "fx26:native-reps.fx") xl layout))
(define raw ((load-input "fx26:native-direct-arm64-raw.fx") arm64 dl asm))
(define flat ((load-input "fx26:native-direct-arm64-flat.fx") arm64 dl asm))
(define proc ((load-input "fx26:native-direct-arm64-proc.fx") dl layout asm reps))
(define prims
  ((load-input "fx26:native-direct-arm64-prims.fx") arm64 dl layout asm reps raw flat proc))
