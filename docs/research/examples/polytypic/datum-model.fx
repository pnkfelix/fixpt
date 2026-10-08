;;; serde's split, with datum as the data model: each type writes only its
;;; way into datum (derived-copy.fx's tree->datum); consumers are written
;;; once, over datum. Here a generic equality (missing today, P0) and a
;;; count of leaves; walks of datum are pure, since datums never change.
(define datum=? (subr pure (datum datum) bool)
  (letrec ((eq (subr pure (datum datum) bool)
             (lambda (x y)
               (cond ((pair? x)
                      (and (pair? y)
                           (eq (car x) (car y))
                           (eq (cdr x) (cdr y))))
                     ((datum-int? x)
                      (and (datum-int? y) (= x y)))
                     ((symbol? x)
                      (and (symbol? y)
                           (string=? (symbol->string x) (symbol->string y))))
                     ((null? x) (null? y))
                     (else #f)))))                   ; strings, chars, … left out
    eq))
(define datum-ints (subr pure (datum) int)
  (letrec ((n (subr pure (datum) int)
             (lambda (d) (cond ((pair? d) (+ (n (car d)) (n (cdr d))))
                               ((datum-int? d) 1)
                               (else 0)))))
    n))
(define-datatype tree (leaf int) (node tree tree))
(define tree->datum (subr pure (tree) datum)       ; the one per-type part
  (letrec ((show (subr pure (tree) datum)
             (lambda (x)
               (tagcase x
                 (leaf (n) (cons 'leaf n))
                 (node (l r) (cons 'node (cons (show l) (show r))))))))
    show))
(define t1 tree (node (leaf 1) (node (leaf 2) (leaf 3))))
(datum=? (tree->datum t1) (tree->datum (node (leaf 1) (node (leaf 2) (leaf 4)))))
(datum-ints (tree->datum t1))
