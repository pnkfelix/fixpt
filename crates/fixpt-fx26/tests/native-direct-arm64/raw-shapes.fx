;;; The raw values' pieces' wrappers of their own shapes
;;; (`tests/native_direct_arm64_raw.rs`), `{EFF}` their effect: what a piece
;;; answers goes first (`pre`).
(define t-raw-entry-skip (subr {EFF} (int) (listof int @k))
  (lambda (n) (begin (ada-reset 10)
    (let ((k (adr-raw-entry-skip n)))
      (t-out (cons (modulo k 256) (cons (quotient k 256) nil)) nil)))))
(define t-f32-fast (subr {EFF} (int string) (listof int @k))
  (lambda (y w)
    (begin (ada-reset 10) (let ((b (adr-f32-fast w y))) (t-out (cons (t-bit b) nil) nil)))))
(define t-compare (subr {EFF} (bool string) (listof int @k))
  (lambda (s w)
    (begin (ada-reset 10) (t-out (cons (modulo (adr-compare s w) 256) nil) nil))))
(define t-int-slow (subr {EFF} (bool int int int int int bool bool bool) (listof int @k))
  (lambda (ov x y imm into prim sub br when)
    (begin (ada-reset 10)
      (let* ((entry (ada-label)) (o (if ov (ada-label) -1)) (back (ada-label))
             (b (if br (ada-label) -1)))
        (begin
          (adr-int-slow (product (1 entry) (2 o) (3 back) (4 x) (5 y) (6 imm) (7 into) (8 prim)
                                 (9 sub) (10 b) (11 when)))
          (t-out nil (if br (cons back (cons b nil)) (cons back nil))))))))
