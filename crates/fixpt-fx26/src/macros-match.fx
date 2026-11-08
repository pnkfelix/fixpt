;;; Typed hygienic macros, in FX-26: a use matched against a clause's
;;; pattern, its pattern variables bound to what the use gave (by ellipsis,
;;; a list of them), and the small list helpers transcription counts with
;;; (`macros.rs`'s `matches`, `pattern_names`). Part of the expander: loaded
;;; by `macros-exports.fx`, and loading `macros-scopes.fx` (and through it
;;; the rest), so that `macros.fx` takes one instance of each through it.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define scopes-module ((proj (load-module "fx26:macros-scopes.fx") rs re rm rc rp)))
(define align-module (with scopes-module align-module))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol len nth mk-list
        (type syns-a names))
(import types-module split syn-nil? reserved-syn? name-in? proper-items ellipsis? ellipsis-of
        (type addr))

;;; ------------------------------------------------------------ matching

;; Pattern variables' syntax, by name.
(define-type binds (listof (tupleof symbol syn) acyclic))
(define bound-of (->* (symbol binds) (listof syn acyclic))
  (lambda (n bs)
    (cond ((null? bs) nil)
          ((symbol=? n (extract (car bs) 1)) (list (extract (car bs) 2)))
          (else (bound-of n (cdr bs))))))
;; Whether `s` matches pattern `p`, onto `bs`: its bindings, in a list of
;; one; none if not. A name is a pattern variable (`_` anything; one of
;; `ns`, the names', a name alone), a form's name or a keyword itself.
(define matched (->* (syn syn names binds) (listof binds acyclic))
  (lambda (p s ns bs)
    (cond
      ;; `(x ...)`: each element of a list by `x`, each of its pattern
      ;; variables then the list of what it matched.
      ((not (null? (ellipsis-of p)))
       (if (or (syn-nil? s) (not (null? (proper-items s))))
           (let ((each (matched-each (car (ellipsis-of p)) (proper-items s) ns nil)))
             (if (null? each)
                 nil
                 (list (seq-binds (pattern-names (car (ellipsis-of p))) (car each) s bs))))
           nil))
      ((syn-symbol? p)
       (cond ((string=? (syn-name p) "_") (list bs))
             ((reserved-syn? p)
              (if (and (syn-symbol? s) (symbol=? (syn-symbol s) (syn-symbol p))) (list bs) nil))
             ((and (name-in? (syn-symbol p) ns) (not (syn-symbol? s))) nil)
             (else (list (cons (tuple (syn-symbol p) s) bs)))))
      ((syn-nil? p) (if (syn-nil? s) (list bs) nil))
      ((not (null? (split p)))
       (let ((ps (split p)) (ss (split s)))
         (if (null? ss)
             nil
             (let ((first (matched (car ps) (car ss) ns bs)))
               (if (null? first) nil (matched (nth ps 1) (nth ss 1) ns (car first)))))))
      ((same-atom? p s) (list bs))
      (else nil))))
;; What each of `xs` matched by `x`, in order, onto `out` (reversed), in a
;; list of one; none if one does not match.
(define matched-each
  (->* (syn syns-a names (listof binds acyclic)) (listof (listof binds acyclic) acyclic))
  (lambda (x xs ns out)
    (if (null? xs)
        (list (the (listof binds acyclic) (reverse out)))
        (let ((one (matched x (car xs) ns nil)))
          (if (null? one) nil (matched-each x (cdr xs) ns (cons (car one) out)))))))
;; `bs`, each of `ns` bound to the list of what each of `each` bound it to,
;; at `s`'s place.
(define seq-binds (->* (names (listof binds acyclic) syn binds) binds)
  (lambda (ns each s bs)
    (if (null? ns)
        bs
        (let ((items (bound-in-each (car ns) each)))
          (seq-binds (cdr ns) each s
                     (cons (tuple (car ns) (mk-list items (syn-start s) (syn-end s))) bs))))))
(define bound-in-each (->* (symbol (listof binds acyclic)) syns-a)
  (lambda (n each)
    (if (null? each) nil (cons (car (bound-of n (car each))) (bound-in-each n (cdr each))))))
;; The pattern variables in pattern `p`: its names but `_`, `...` and the
;; forms' (which match themselves).
(define pattern-names (->* (syn) names)
  (lambda (p)
    (cond ((syn-symbol? p)
           (if (or (string=? (syn-name p) "_") (ellipsis? p) (reserved-syn? p))
               nil
               (list (syn-symbol p))))
          (else (pattern-names-each (list-items p))))))
(define pattern-names-each (->* (syns-a) names)
  (lambda (xs) (if (null? xs) nil (append (pattern-names (car xs)) (pattern-names-each (cdr xs))))))
;; Whether two atoms are the same datum.
(define same-atom? (->* (syn syn) bool)
  (lambda (p s)
    (tagcase p
      (atom (d a b x)
        (tagcase s
          (atom (e c f y)
            (cond ((keyword? d)
                   (and (keyword? e) (symbol=? (keyword->symbol d) (keyword->symbol e))))
                  ((string? d) (and (string? e) (string=? d e)))
                  ((int? d) (and (int? e) (= d e)))
                  ((char? d) (and (char? e) (char=? d e)))
                  ((bool? d) (and (bool? e) (eq? d e)))
                  (else #f)))
          (else z #f)))
      (else y #f))))
;; A list's items (a dotted list's before its tail); none if `s` is no list.
(define list-items (->* (syn) syns-a)
  (lambda (s)
    (tagcase s (lst (items d a b x) items) (dotted (items t d a b x) items) (else y nil))))
;; The first of `ls` from the `i`th whose length is not the first's; -1.
(define odd-length (->* ((listof syns-a acyclic) int) int)
  (lambda (ls i)
    (cond ((or (null? ls) (null? (cdr ls))) -1)
          ((= (len (car (cdr ls))) (len (car ls)))
           (odd-length (cons (car ls) (cdr (cdr ls))) (+ i 1)))
          (else (+ i 1)))))
(define nth-name (->* (names int) symbol)
  (lambda (ns i) (if (= i 0) (car ns) (nth-name (cdr ns) (- i 1)))))
(define nth-list (->* ((listof syns-a acyclic) int) syns-a)
  (lambda (ls i) (if (= i 0) (car ls) (nth-list (cdr ls) (- i 1)))))
(define len-ints (->* ((listof int acyclic)) int)
  (lambda (is) (if (null? is) 0 (+ 1 (len-ints (cdr is))))))
(define addr-under? (->* (addr addr) bool)
  (lambda (a p)
    (or (null? p) (and (not (null? a)) (eq? (car a) (car p)) (addr-under? (cdr a) (cdr p))))))
(define ints=? (->* ((listof int acyclic) (listof int acyclic)) bool)
  (lambda (a b)
    (if (null? a) (null? b) (and (not (null? b)) (= (car a) (car b)) (ints=? (cdr a) (cdr b))))))
(define all-ints? (->* ((listof int acyclic) int) bool)
  (lambda (is k) (or (null? is) (and (= (car is) k) (all-ints? (cdr is) k)))))
;; The first `d` of `is`.
(define ints-prefix (->* ((listof int acyclic) int) (listof int acyclic))
  (lambda (is d) (if (or (= d 0) (null? is)) nil (cons (car is) (ints-prefix (cdr is) (- d 1))))))
