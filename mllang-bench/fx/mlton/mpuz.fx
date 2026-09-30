;;; MPUZ -- solving Emacs's multiplication puzzle (M-x mpuz) by trying every
;;; assignment of digits to letters.
;;;
;;; Written by sweeks@sweeks.com on 1999-08-31; very loosely based on an
;;; OCaml solution posted to comp.lang.ml by Laurent Vaucher.
;;; From MLton's benchmark suite (benchmark/tests/mpuz.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): (doit 1), solving AGH * FB = FGIJE 1 times.
;;; Answer: "J = 0 I = 1 D = 8 E = 2 C = 5 B = 6 F = 4 H = 7 G = 3 A = 9 \n",
;;; what printResult prints (the solution the original's comment gives).
;;; The original overrides `print` to do nothing, "so the benchmark is
;;; silent"; here `print` appends what it is given to a string in a ref,
;;; which is the answer (it is called only for the one solution).
;;;
;;; Changed, as FX-26 needs: List.fold and String.fold, used at several
;;; types, are `poly`s; SML's tuples are products; `concat` is written
;;; here. Procedures passed as arguments read globals at large,
;;; `(read @globals)`.

(define-type chars (listof char @h))
(define-type strings (listof string @h))

;; What `print` has printed.
(define printed (ref string @h) (new ""))
(define* print (subr (maxeff (read @h) (write @h)) (string) unit)
  (lambda (s) (set printed (string-append (get printed) s))))

(define* concat (subr (maxeff (read @h) spin) (strings) string)
  (lambda (ss) (if (null? ss) "" (string-append (car ss) (concat (cdr ss))))))

;; structure List
(define list-exists (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (chars (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (char) bool)) bool)
  (lambda (l p)
    (letrec ((loop (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (chars) bool)
               (lambda (l) (if (null? l) #f (if (p (car l)) #t (loop (cdr l)))))))
      (loop l))))

(define list-map (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) ((listof int @h) (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (int) (productof (v int) (r (ref bool @h)))))
                       (listof (productof (v int) (r (ref bool @h))) @h))
  (lambda (l f)
    (letrec ((loop (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) ((listof int @h)) (listof (productof (v int) (r (ref bool @h))) @h))
               (lambda (l) (if (null? l) nil (cons (f (car l)) (loop (cdr l)))))))
      (loop l))))

(define list-fold (poly ((a type) (b type)) (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) ((listof a @h) b (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (a b) b)) b))
  (plambda ((a type) (b type))
    (lambda (l b f)
      (letrec ((loop (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) ((listof a @h) b) b)
                 (lambda (l b) (if (null? l) b (loop (cdr l) (f (car l) b))))))
        (loop l b)))))

(define list-foreach (poly ((a type)) (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) ((listof a @h) (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (a) unit)) unit))
  (plambda ((a type))
    (lambda (l f) ((proj list-fold a unit) l #u (lambda (x u) (f x))))))

;; structure String
(define string-fold (poly ((b type)) (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (string b (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (char b) b)) b))
  (plambda ((b type))
    (lambda (s b f)
      (let ((n (string-length s)))
        (letrec ((loop (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (int b) b)
                   (lambda (i b) (if (= i n) b (loop (+ i 1) (f (string-ref s i) b))))))
          (loop 0 b))))))

;; structure Mpuz
(define solve (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (string string string string string) unit)
  (lambda (a b c d e)
    (let* ((letters
            ((proj list-fold string chars)
             (list a b c d e) nil
             (lambda (s letters)
               ((proj string-fold chars)
                s letters
                (lambda (c letters)
                  (if (list-exists letters (lambda (c2) (char=? c c2)))
                      letters
                      (cons c letters)))))))
           (letter-values (the (arrayof int @h) (make-array (+ 255 1) 0)))
           (letter-value (lambda ((c char)) (array-ref letter-values (char->integer c))))
           (set-letter-value (lambda ((c char) (v int)) (array-set! letter-values (char->integer c) v)))
           (string-value (lambda ((s string))
                           ((proj string-fold int) s 0 (lambda (c v) (+ (* v 10) (letter-value c))))))
           (print-result (lambda ()
                           (begin
                             ((proj list-foreach char)
                              letters
                              (lambda (c)
                                (print (concat (list (char->string c) " = " (int->string (letter-value c)) " ")))))
                             (print "\n"))))
           (test-ok (lambda ()
                      (let* ((b0 (letter-value (string-ref b 1)))
                             (b1 (letter-value (string-ref b 0)))
                             (a (string-value a))
                             (b (string-value b))
                             (c (string-value c))
                             (d (string-value d))
                             (e (string-value e)))
                        (if (and (= (* a b0) c)
                                 (= (* a b1) d)
                                 (= (* a b) e)
                                 (= (+ c (* d 10)) e))
                            (print-result)
                            #u))))
           (values (list-map (list 0 1 2 3 4 5 6 7 8 9)
                             (lambda (v) (product (v v) (r (the (ref bool @h) (new #f))))))))
      ;; Try all assignments of values to letters.
      (letrec ((loop (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (chars) unit)
                 (lambda (letters)
                   (if (null? letters)
                       (test-ok)
                       (let ((c (car letters)) (letters (cdr letters)))
                         ((proj list-foreach (productof (v int) (r (ref bool @h))))
                          values
                          (lambda (p)
                            (let ((v (extract p v)) (r (extract p r)))
                              (if (get r)
                                  #u
                                  (begin (set r #t)
                                         (set-letter-value c v)
                                         (loop letters)
                                         (set r #f)))))))))))
        (loop letters)))))

;; The input, where no compiler can fold it: a global, which a later
;; definition may replace.
(define iterations int 1)

(define* doit (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (int) string)
  (lambda (size)
    (letrec ((loop (subr (maxeff (read @h) (write @h) (alloc @h) spin (read @globals)) (int) unit)
               (lambda (n)
                 (if (= n 0)
                     #u
                     (begin (set printed "")
                            (solve "AGH" "FB" "CBEE" "GHFD" "FGIJE")
                            (loop (- n 1)))))))
      (begin (loop size) (get printed)))))
(doit iterations)
