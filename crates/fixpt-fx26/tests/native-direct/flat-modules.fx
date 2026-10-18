;;; The modules the heap's pieces are tested over (`tests/native_direct_x64_flat.rs`).
(define direct-types (load-module "fx26:native-direct-x64-types.fx"))
(define x86-64 (load-input "fx26:x86_64.fx"))
(define dl (load-module "fx26:native-direct-x64-layout.fx"))
(define asm ((load-input "fx26:native-direct-x64-asm.fx") x86-64 dl))
