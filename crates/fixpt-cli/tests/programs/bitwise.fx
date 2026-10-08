;;; Bits of `int`s (SRFI 151's names, `TODO.md` §55) on every machine,
;;; fixnums and bignums, a negative shift rounding down.
(list (bitwise-and 12 10) (bitwise-ior 12 10) (bitwise-xor 12 10) (bitwise-not 5)
      (arithmetic-shift 3 4) (arithmetic-shift -17 -2) (arithmetic-shift 1 70)
      (bitwise-and (arithmetic-shift 1 70) (- (arithmetic-shift 1 71) 1))
      (bitwise-and -1 255) (bitwise-xor (arithmetic-shift 1 64) -1))
