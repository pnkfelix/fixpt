;;; The FX-26 parser, in FX-26: top-level forms, and a program of them.
;;; Part of the parser, `parser.fx` first (PLAN.md §11, step 9a).

;;; ------------------------------------------------------------- top level

(define parse-top (subr (maxeff parses spin) (syn) top)
  (lambda (s)
    (let ((head (form-head s)))
      (cond ((symbol=? head 'define) (parse-define s #f))
            ;; `(define* name type lambda)`: its type is a list of it and the
            ;; head, which says the checker finds what the lambda reads.
            ((symbol=? head 'define*) (parse-define s #t))
            ((symbol=? head 'define-rec)
             (let ((items (syn-items s "a group of definitions")))
               (if (null? (cdr items))
                   (pfail "`(define-rec (name type lambda) …)`" s)
                   (t-define-rec (parse-rec-bindings (cdr items)) (syn-start s) (syn-end s)))))
            ((symbol=? head 'define-type)
             (let ((items (syn-items s "a type definition")))
               (if (= (len items) 3)
                   (t-define-type (nth items 1) (nth items 2) (syn-start s) (syn-end s))
                   (pfail "`(define-type name type)`" s))))
            ((symbol=? head 'define-effect)
             (let ((items (syn-items s "an effect definition")))
               (if (= (len items) 3)
                   (t-define-effect (nth items 1) (nth items 2) (syn-start s) (syn-end s))
                   (pfail "`(define-effect name effect)`" s))))
            ((symbol=? head 'private-regions)
             (let ((regions (keep (cdr (syn-items s "private-regions")))))
               (t-private-regions regions (syn-start s) (syn-end s))))
            (else (t-exp (parse-exp s)))))))

(define append-tops (subr (read @globals) (top-list top-list) top-list)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (append-tops (cdr xs) ys)))))

;; `(define-generative head rep)`: the form, and its two conversions, each
;; the identity: `(define up-name (poly (param …) (subr pure (rep) (name p
;; …))) (lambda (x) x))`, and `down-name` the other way.
(define generative? (subr (maxeff (read @globals) (read @s)) (syn) bool)
  (lambda (s) (form-of? s 'define-generative)))
;; A parameter as a binder, its variance left out.
(define gen-binder (subr parses (syn int int) syn)
  (lambda (param a b)
    (let ((p (syn-items param "a parameter")))
      (if (>= (len p) 2)
          (mk-list (list (car p) (nth p 1)) a b)
          (pfail "a parameter is `(name kind)`, `(name kind +)` or `(name kind -)`" param)))))
;; The parameters as binders, and their names.
(define gen-binders (subr parses (syns-a int int) syns-a)
  (lambda (ps a b)
    (if (null? ps)
        nil
        (let ((binder (gen-binder (car ps) a b)))
          (cons binder (gen-binders (cdr ps) a b))))))
(define gen-names (subr parses (syns-a) syns-a)
  (lambda (bs)
    (if (null? bs)
        nil
        (cons (car (syn-items (car bs) "a parameter")) (gen-names (cdr bs))))))
;; A conversion, `prefix` and the name `n`, of type `ty`: the identity.
(define gen-conversion (subr (read @globals) (string string syn exp int int) top)
  (lambda (prefix n ty identity a b)
    (t-define (string->symbol (string-append prefix n)) (the syns-a (cons ty nil)) identity a b)))
(define parse-generative (subr parses (syn) top-list)
  (lambda (s)
    (let* ((items (syn-items s "a generative type")) (a (syn-start s)) (b (syn-end s))
           (usage (string-append "`(define-generative name type)` or "
                                 "`(define-generative (name (param kind) …) type)`")))
      (if (not (= (len items) 3))
          (pfail usage s)
          (let* ((head (nth items 1))
                 (rep (nth items 2))
                 (family? (tagcase head (lst (hs d ha hb) (not (null? hs))) (else x #f)))
                 (hs (if family? (syn-items head "a generative type's name") (the syns-a nil)))
                 (name (if family? (car hs) head))
                 (n (if (syn-symbol? name) (symbol->string (syn-symbol name)) (pfail usage s)))
                 (binders (if family? (gen-binders (cdr hs) a b) (the syns-a nil)))
                 (used (if family? (mk-list (cons name (gen-names binders)) a b) name))
                 (conv (lambda ((from syn) (to syn))
                         (let ((t (mk-pure-subr (the syns-a (cons from nil)) to a b)))
                           (if family? (mk-poly binders t a b) t))))
                 (x (product (1 'x) (2 (the syns-a nil))))
                 (identity (e-lambda (the param-list (cons x nil)) (e-var 'x a b) a b))
                 (up (gen-conversion "up-" n (conv rep used) identity a b))
                 (down (gen-conversion "down-" n (conv used rep) identity a b)))
            (list (t-define-generative head rep a b) up down))))))

;; Each of `xs`, parsed as a top-level form.
(define parse-each-top (subr (maxeff parses spin) (syns-a) top-list)
  (lambda (xs) (if (null? xs) nil (cons (parse-top (car xs)) (parse-each-top (cdr xs))))))
;; What top-level form `x` makes: a generative type's or a datatype's
;; several forms, or one.
(define parse-made (subr (maxeff parses spin) (syn) top-list)
  (lambda (x)
    (cond ((generative? x) (parse-generative x))
          ((datatype? x) (parse-each-top (expand-datatype x)))
          (else (the top-list (cons (parse-top x) nil))))))

(define parse-tops (subr (maxeff parses spin) (syns-a) top-list)
  (lambda (xs)
    (if (null? xs)
        nil
        (let* ((made (parse-made (car xs))) (rest (parse-tops (cdr xs))))
          (append-tops made rest)))))

;; The entry point: a program's forms, as read, to trees or an error. The
;; prompt catches every failure, but its tag is a global whose type names
;; @p, so the control effect stays in the type, as the reader's on @e do;
;; @p is this program's own, so that is still licensed.
(define parse-program (subr (maxeff (read @globals) parses spin) (syns-a) presult)
  (lambda (forms) (prompt parse-tag (p-ok (parse-tops forms)) (lambda (r) r))))
