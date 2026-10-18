;;; The modules the raw values' pieces are tested over (`tests/native_direct_x64_raw.rs`).
(define x86-64 (load-input "fx26:x86_64.fx"))
(define dl (load-module "fx26:native-direct-x64-layout.fx"))
(define asm ((load-input "fx26:native-direct-x64-asm.fx") x86-64 dl))
(define raw ((load-input "fx26:native-direct-x64-raw.fx") x86-64 dl asm))
