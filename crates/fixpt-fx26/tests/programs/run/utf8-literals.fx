; `#utf8"…"`, UTF-8 text written in a program (TODO.md §306): a constant
; of type `utf8`, made once and interned, as a quote's constant is; a
; string's escapes; quoted, itself; in quoted data, a datum, told apart by
; `utf8?` and by `typecase`. Text all ASCII is marked so as it is read, so
; its count of characters is its length in bytes.
(define t #utf8"aé\x1F600;z")
t
(list (utf8-length t) (utf8-byte-length t))
(utf8=? t (string->utf8 "aé\x1F600;z"))
(utf8-ref #utf8"hello" 1)
'#utf8"quoted"
(define d '(a #utf8"in a list" 3))
(typecase (car (cdr d)) (utf8 u (utf8-length u)) (else y -1))
(list (utf8? (car (cdr d))) (utf8? (car d)))
(define* once (subr pure () utf8) (lambda () #utf8"once"))
(eq? (once) (once))
#utf8""
(utf8-ref #utf8"\x3BB;q\t" 0)
(utf8-length #utf8"\x3BB;q\t")
