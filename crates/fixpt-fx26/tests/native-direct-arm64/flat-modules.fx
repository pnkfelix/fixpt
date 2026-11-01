;;; The modules the flat pieces are tested over (`native_direct_arm64_flat.rs`).
(define arm64 (load-input "fx26:arm64.fx"))
(define dl (load-module "fx26:native-direct-arm64-layout.fx"))
(define asm ((load-input "fx26:native-direct-arm64-asm.fx") arm64 dl))
(define flat ((load-input "fx26:native-direct-arm64-flat.fx") arm64 dl asm))
