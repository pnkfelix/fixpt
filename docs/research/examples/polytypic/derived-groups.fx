;;; §4's shape of derived code: one local letrec group per derived
;;; definition, a member per type node. Over a rose tree at `acyclic`
;;; the group descends, so the equality is pure; over the same shape at
;;; a writable region it must say spin (the list may be cyclic).
(define-datatype rose (rleaf int) (rnode (listof rose acyclic)))
(define rose=? (subr pure (rose rose) bool)
  (letrec ((t=? (subr pure (rose rose) bool)
             (lambda (x y)
               (tagcase x
                 (rleaf (n) (tagcase y (rleaf (m) (= n m)) (else _ #f)))
                 (rnode (xs) (tagcase y (rnode (ys) (ts=? xs ys)) (else _ #f))))))
           (ts=? (subr pure ((listof rose acyclic) (listof rose acyclic)) bool)
             (lambda (xs ys)
               (cond ((null? xs) (null? ys))
                     ((null? ys) #f)
                     (else (and (t=? (car xs) (car ys)) (ts=? (cdr xs) (cdr ys))))))))
    t=?))
;; Without spin in the three signatures: refused, "a part of a list that may be written is no smaller".
(define-datatype hrose (hleaf int) (hnode (listof hrose @heap)))
(define hrose=? (subr (maxeff (read @heap) spin) (hrose hrose) bool)
  (letrec ((t=? (subr (maxeff (read @heap) spin) (hrose hrose) bool)
             (lambda (x y)
               (tagcase x
                 (hleaf (n) (tagcase y (hleaf (m) (= n m)) (else _ #f)))
                 (hnode (xs) (tagcase y (hnode (ys) (ts=? xs ys)) (else _ #f))))))
           (ts=? (subr (maxeff (read @heap) spin) ((listof hrose @heap) (listof hrose @heap)) bool)
             (lambda (xs ys)
               (cond ((null? xs) (null? ys))
                     ((null? ys) #f)
                     (else (and (t=? (car xs) (car ys)) (ts=? (cdr xs) (cdr ys))))))))
    t=?))
(rose=? (rnode (cons (rleaf 1) nil)) (rnode (cons (rleaf 1) nil)))
