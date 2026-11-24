; UTF-8 text, `utf8` (TODO.md §306): frozen, indexed by byte offset, a
; character read where one starts and the offset after it the next, so a
; walk over it is O(n); lengths in characters and in bytes; a piece
; between two offsets; compared; a `string`'s text and back; bytes
; validated, and the offset bytes not UTF-8 are valid up to; told apart by
; `utf8?` and by `typecase`.
(define t (string->utf8 "aé\x1F600;z"))
(define* walk (subr (maxeff (alloc @heap) spin) (utf8 int) (listof char @heap))
  (lambda (u k)
    (if (>= k (utf8-byte-length u)) nil (cons (utf8-ref u k) (walk u (utf8-next u k))))))
(utf8-length t)
(utf8-byte-length t)
(walk t 0)
(utf8-substring t 1 7)
(utf8->string (utf8-substring t 3 8))
(list (utf8=? t (string->utf8 "aé\x1F600;z")) (utf8=? t (utf8-substring t 0 7)) (utf8? t)
      (utf8? "aé"))
(tagcase (bytes->utf8 (utf8->bytes t)) (text u (utf8=? u t)) (bad k #f))
(tagcase (bytes->utf8 (bytevector-copy (utf8->bytes t) 0 2)) (text u -1) (bad k k))
(typecase t (utf8 u (utf8-length u)) (else y 0))
