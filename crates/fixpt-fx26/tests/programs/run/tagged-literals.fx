; A tagged literal, `#Ltag"text"` (Heist's `fixpt-tagged-literals.md`):
; read as `(literal:tag #utf8"text")`, a use of the name `literal:tag`,
; found as any name is, so a `let` may bind one. A procedure bound to it
; runs where the literal is evaluated; a macro, at expansion, so its text
; is looked at once. Quoted, it is that list, written back as it was read,
; `#L` and its tag; `#l` reads as `#L` does.
(define literal:twice (subr pure (utf8) int) (lambda (u) (* 2 (utf8-length u))))
#Ltwice"abc"
(let ((literal:twice (lambda ((u utf8)) 0))) #Ltwice"abc")
(define-syntax literal:len
  (er-macro-transformer
   (lambda (form rename compare) (let ((t (car (cdr form)))) (if (utf8? t) (utf8-length t) 0)))))
#Llen"héllo"
'#Limg"iVBORw0KGgo="
(car '#Limg"x")
(utf8? (car (cdr '#Limg"x")))
'(a #l-A1"y" (literal:x "plain") (literal:x #utf8"z" 1))
