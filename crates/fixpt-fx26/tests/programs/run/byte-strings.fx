; A bytevector written as text, `#u8"…"` (SRFI 207's spelling), beside
; `#u8(…)`: each character ASCII, its one byte, a string's escapes, and
; `\xHH;` any byte. Either is a constant of type `bytevector`, made once
; and interned by its bytes, as a quote's constant is; quoted, itself; in
; quoted data, a datum, told apart by `bytevector?` and by `typecase`. It
; is written back as `#u8(…)`, whichever way it was written.
(define t #u8"ab\x80;\xff;\n\\z")
t
(bytevector-length t)
(bytevector=? t #u8(97 98 128 255 10 92 122))
(bytevector-u8-ref #u8"A" 0)
'#u8"quoted"
(define d '(a #u8"in a list" #u8(1 2) 3))
(typecase (car (cdr d)) (bytevector b (bytevector-length b)) (else y -1))
(list (bytevector? (car (cdr (cdr d)))) (bytevector? (car d)))
(define* once (subr pure () bytevector) (lambda () #u8"once"))
(eq? (once) (once))
#u8""
(bytevector=? #u8"" #u8())
(tagcase (bytes->utf8 #u8"h\xc3;\xa9;") (text u (utf8-length u)) (bad n (- 0 n)))
(tagcase (bytes->utf8 #u8"h\xc3;") (text u (utf8-length u)) (bad n (- 0 n)))
