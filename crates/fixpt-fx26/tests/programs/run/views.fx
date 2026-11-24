; Views into bytes and into a string (TODO.md §310): `str` and `bytes`,
; `(strof r)` and `(bytesof r)`, read only; a whole buffer is one, so a
; `string` or a `(stringof r)` goes wherever a `str` is wanted, nothing
; converted; a slice is a view of a piece, nothing copied, a slice of a
; slice one of the first's owner; a slice of a buffer still written sees
; its writes; the copies (`substring`, `str->string`, `bytevector-copy`,
; `bytes->bytevector`) are whole buffers, and read views. Frozen bytes
; read as UTF-8 text in place (`bytes-as-utf8`), validated, a slice of
; them too, and a slice of that text.
(define s "hello, world")
(define* len (poly ((r region)) (subr pure ((strof r)) nat)) (lambda (v) (str-length v)))
(len s)
(define w (str-slice s 7 12))
w
(len w)
(str-ref w 0)
(str-slice w 1 3)
(list (str=? w "world") (str<? w "x") (str<? w w))
(str->string w)
(substring w 1 4)
(string->utf8 w)
(define* seen (subr (maxeff (alloc @heap) (read @heap) (write @heap)) () char)
  (lambda ()
    (let* ((m (the (stringof @heap) (make-string 3 #\a))) (v (str-slice m 1 3)))
      (begin (string-set! m 1 #\z) (str-ref v 0)))))
(seen)
(define bv (letfreeze r (the (bytevectorof r) (make-bytevector 4 (int->u8 7)))))
(define bs (bytes-slice bv 1 3))
bs
(bytes-length bs)
(bytes-u8-ref bs 0)
(bytes=? bs (bytes-slice bv 2 4))
(bytes->bytevector bs)
(bytevector-copy bs 0 1)
(tagcase (bytes->utf8 (bytes-slice (utf8->bytes (string->utf8 "abc")) 1 3))
  (text u u)
  (bad k (string->utf8 "")))
(define fb (letfreeze r (the (bytevectorof r) (utf8->bytes (string->utf8 "h\xe9;llo")))))
(define u (tagcase (bytes-as-utf8 fb) (text u u) (bad k (string->utf8 ""))))
u
(list (utf8-length u) (utf8-byte-length u))
(utf8-slice u 1 3)
(tagcase (bytes-as-utf8 (bytes-slice fb 0 2)) (text v -1) (bad k k))
(tagcase (bytes-as-utf8 (bytes-slice fb 3 6)) (text v v) (bad k (string->utf8 "")))
