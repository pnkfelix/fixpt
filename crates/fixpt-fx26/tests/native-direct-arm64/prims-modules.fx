;;; The modules the fast paths' pieces run in (`native_direct_arm64_prims.rs`):
;;; `pure_fast`'s and `string_eq`'s file, made of the raw values' and the heap's.
(define arm64 (load-input "fx26:arm64.fx"))
(define dl (load-module "fx26:native-direct-arm64-layout.fx"))
(define asm ((load-input "fx26:native-direct-arm64-asm.fx") arm64 dl))
(define raw ((load-input "fx26:native-direct-arm64-raw.fx") arm64 dl asm))
(define flat ((load-input "fx26:native-direct-arm64-flat.fx") arm64 dl asm))
(define strings ((load-input "fx26:native-direct-arm64-strings.fx") arm64 dl asm raw flat))
