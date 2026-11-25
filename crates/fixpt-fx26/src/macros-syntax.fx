;;; Typed hygienic macros, in FX-26: what the expander asks of syntax,
;;; which no syntax type is of (`macros-types.fx`, which loads it and gives
;;; what its parts ask for).

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define parser-module ((proj (load-module "fx26:parser.fx") rs re rm rc rp)))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted vec (type syn))
(import parser-module syn-symbol? syn-symbol (type syns-a names))
(define kernel (load-module "fx26:macros-kernel.fx"))
(define tables (load-module "fx26:table.fx"))
(import tables make-table table-ref table-set! symbol-hash (type table))

;; Whether `s` is `()`.
(define syn-nil? (->* (syn) bool)
  (lambda (s)
    (tagcase s
      (atom (d a b x) (null? d))
      (lst (items d a b x) (null? items))
      (else y #f))))
;; Whether `s` is a keyword, `#:name`.
(define syn-keyword? (->* (syn) bool)
  (lambda (s) (tagcase s (atom (d a b x) (keyword? d)) (else y #f))))
;; Whether `s` is an integer, as a program's label by position may be.
(define syn-number? (->* (syn) bool)
  (lambda (s) (tagcase s (atom (d a b x) (datum-int? d)) (else y #f))))
;; A list's car and cdr, the cdr a list of the rest (or the tail), in a list
;; of two; none if `s` is no pair.
(define split (->* (syn) syns-a)
  (lambda (s)
    (tagcase s
      (lst (items d a b x)
        (if (null? items)
            nil
            (list (car items)
                  (if (null? (cdr items))
                      (atom '() a b x)
                      (lst (cdr items) (if (pair? d) (cdr d) d) a b x)))))
      (dotted (items tail d a b x)
        (list (car items)
              (if (null? (cdr items))
                  tail
                  (dotted (cdr items) tail (if (pair? d) (cdr d) d) a b x))))
      (else y nil))))
;; `d`, a datum, as syntax at no place.
(define datum->syn (->* (datum) syn)
  (lambda (d)
    (if (pair? d)
        (let ((parts (datum-parts d)))
          (if (null? (cdr parts))
              (lst (car parts) d 0 0 0)
              (dotted (car parts) (car (car (cdr parts))) d 0 0 0)))
        (atom d 0 0 0))))
;; A pair's elements as syntax, and its tail if it is not `()`, in a list.
(define datum-parts (->* (datum) (listof syns-a acyclic))
  (lambda (d)
    (letrec ((go (subr (maxeff (read @globals) spin) (datum) syns-a)
               (lambda (x) (if (pair? x) (cons (datum->syn (car x)) (go (cdr x))) nil)))
             (end (subr (maxeff (read @globals) spin) (datum) datum)
               (lambda (x) (if (pair? x) (end (cdr x)) x))))
      (let ((e (end d)))
        (if (null? e)
            (list (go d))
            (list (go d) (the syns-a (list (atom e 0 0 0)))))))))

;; `s` written as the Rust front end's `write_syntax` writes it, for what
;; is said of it.
(define show-syn (->* (syn) string)
  (lambda (s)
    (tagcase s
      (lst (items d a b x) (if (null? items) "()" (string-append "(" (show-each items) ")")))
      (dotted (items tail d a b x)
        (string-append "(" (show-each items) " . " (show-syn tail) ")"))
      (vec (items d a b x) (string-append "#(" (show-each items) ")"))
      (atom (d a b x) (show-datum d)))))
(define show-each (->* (syns-a) string)
  (lambda (xs)
    (cond ((null? xs) "")
          ((null? (cdr xs)) (show-syn (car xs)))
          (else (string-append (show-syn (car xs)) " " (show-each (cdr xs)))))))
(define show-datum (->* (datum) string)
  (lambda (d)
    (cond ((null? d) "()")
          ((symbol? d) (symbol->string d))
          ((keyword? d) (string-append "#:" (symbol->string (keyword->symbol d))))
          ((string? d) (string-append "\"" d "\""))
          ((utf8? d) (string-append "#utf8\"" (string-append (utf8->string d) "\"")))
          ((char? d) (string-append "#\\" (char->string d)))
          ((int? d) (int->string d))
          ((f64? d) (f64->string d))
          ((bool? d) (if d "#t" "#f"))
          (else "…"))))

;;; ------------------------------------------------------------ names

;; The kernel's words, each a table of its words made once: a name found
;; by its symbol's hash, made when it was interned (as Larceny's `case` on
;; symbols finds one, Clinger, "Rapid Case Dispatch in Scheme", 2006), not
;; by a walk of the list (140 symbols, most names none of them).
(define words-into (subr (maxeff (read @globals) spin (read rs) (write rs) (alloc rs))
                          ((table symbol bool rs) datum) (table symbol bool rs))
  (lambda (t ws)
    (if (pair? ws)
        (begin (if (symbol? (car ws)) (table-set! t (car ws) #t) #u) (words-into t (cdr ws)))
        t)))
(define words-table (subr (maxeff (read @globals) spin (read rs) (write rs) (alloc rs))
                          (datum) (table symbol bool rs))
  (lambda (ws) (words-into (the (table symbol bool rs) (make-table symbol-hash symbol=?)) ws)))
(define reserved-table (table symbol bool rs)
  (words-into (words-table (with kernel reserved-words))
              '(|#%fx| |#%toplevel| define-syntax define-syntax-rec)))
(define description-words (table symbol bool rs) (words-table (with kernel description-words)))
(define description-heads (table symbol bool rs) (words-table (with kernel description-heads)))
(define type-forms (table symbol bool rs) (words-table (with kernel type-forms)))
;; Whether `name` is a form's, `#%fx`, `#%toplevel` or `define-syntax`: never
;; bound, so never a binder or a variable.
(define reserved? (->* (string) bool)
  (lambda (name) (reserved-sym? (string->symbol name))))
(define reserved-sym? (->* (symbol) bool) (lambda (n) (table-ref reserved-table n #f)))
;; Whether `name` is a word of descriptions (the kernel's): one read
;; anywhere (`pure`, `heap`, a region constant `@r`, or a name already
;; `#%`'s), or, `head`, one a list's head may be (`subr`, `listof`).
(define desc-word? (->* (string bool) bool)
  (lambda (name head)
    (or (and (> (string-length name) 0) (char=? (string-ref name 0) #\@))
        (and (> (string-length name) 1) (string=? (substring name 0 2) "#%"))
        (let ((n (string->symbol name)))
          (or (table-ref description-words n #f) (and head (table-ref description-heads n #f)))))))
;; Whether `name` is a type form's head (the kernel's `type-forms`), whose
;; template makes a description.
(define type-form? (->* (string) bool)
  (lambda (name) (table-ref type-forms (string->symbol name) #f)))
;; Whether `s` is a name, and a reserved one.
(define reserved-syn? (->* (syn) bool)
  (lambda (s) (and (syn-symbol? s) (reserved-sym? (syn-symbol s)))))
(define name-in? (->* (symbol names) bool)
  (lambda (n ns) (and (not (null? ns)) (or (symbol=? n (car ns)) (name-in? n (cdr ns))))))

;; Whether `i` is one of `is`.
(define int-in? (->* (int (listof int acyclic)) bool)
  (lambda (i is) (and (not (null? is)) (or (= i (car is)) (int-in? i (cdr is))))))
