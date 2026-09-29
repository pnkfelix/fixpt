;;; serde's split, with datum as the data model: each type writes only its
;;; way into datum (derived-copy.fx's tree->datum); consumers are written
;;; once, over datum. Here a generic equality (missing today, P0) and a
;;; count of leaves; walks of datum are pure, since datums never change.
(define datum=? (subr pure (datum datum) bool)
  (letrec ((eq (subr pure (datum datum) bool)
             (lambda (x y)
               (cond ((datum-pair? x)
                      (and (datum-pair? y)
                           (eq (datum-car x) (datum-car y))
                           (eq (datum-cdr x) (datum-cdr y))))
                     ((datum-int? x)
                      (and (datum-int? y) (= (datum-int-value x) (datum-int-value y))))
                     ((datum-symbol? x)
                      (and (datum-symbol? y)
                           (string=? (datum-symbol-name x) (datum-symbol-name y))))
                     ((datum-null? x) (datum-null? y))
                     (else #f)))))                   ; strings, chars, … left out
    eq))
(define datum-ints (subr pure (datum) int)
  (letrec ((n (subr pure (datum) int)
             (lambda (d) (cond ((datum-pair? d) (+ (n (datum-car d)) (n (datum-cdr d))))
                               ((datum-int? d) 1)
                               (else 0)))))
    n))
(define-datatype tree (leaf int) (node tree tree))
(define tree->datum (subr pure (tree) datum)       ; the one per-type part
  (letrec ((show (subr pure (tree) datum)
             (lambda (x)
               (tagcase x
                 (leaf (n) (datum-cons (datum-symbol "leaf") (datum-int n)))
                 (node (l r) (datum-cons (datum-symbol "node") (datum-cons (show l) (show r))))))))
    show))
(define t1 tree (node (leaf 1) (node (leaf 2) (leaf 3))))
(datum=? (tree->datum t1) (tree->datum (node (leaf 1) (node (leaf 2) (leaf 4)))))
(datum-ints (tree->datum t1))
