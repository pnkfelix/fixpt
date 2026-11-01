;;; The modules the raw pieces are tested over (`native_direct_arm64_raw.rs`).
(define arm64 (load-input "fx26:arm64.fx"))
(define dl (load-module "fx26:native-direct-arm64-layout.fx"))
(define asm ((load-input "fx26:native-direct-arm64-asm.fx") arm64 dl))
(define raw ((load-input "fx26:native-direct-arm64-raw.fx") arm64 dl asm))
