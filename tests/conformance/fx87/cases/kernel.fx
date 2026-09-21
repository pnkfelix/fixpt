;;; fixpt FX-87 conformance corpus -- kernel and standard types.
;;; Authored for this project; every expected answer is produced by the
;;; reference implementation (GiffordHistory fx-lang/fx87), never by hand.
;;; Ill-typed cases are deliberate and marked by comment.

;;; ---- literals ----
3
-17
3.5
#\a
"hello"
#t
#f
#u
'()

;;; ---- kernel: the ----
(the pure int 3)
(the int 3)
(the pure bool #t)
(the pure unit #u)
(the pure bool 3)                       ; ill-typed: int </= bool

;;; ---- kernel: if ----
(if #t 1 2)
(if #t 1 #\a)                           ; ill-typed: no common supertype
(if 1 2 3)                              ; ill-typed: test not bool

;;; ---- kernel: begin ----
(begin 1 2 3)
(begin #t)

;;; ---- kernel: lambda / application ----
(lambda ((x int)) x)
(lambda ((x int) (y int)) (+ x y))
((lambda ((x int)) x) 3)
((lambda ((x int)) x) #t)               ; ill-typed
(lambda ((f (subr pure (int) int)) (x int)) (f x))
(lambda ((x int)) (lambda ((y int)) x))
((lambda () 3))

;;; ---- kernel: let / let* (sugar) ----
(let ((x 3)) x)
(let ((x 3) (y 4)) (+ x y))
(let* ((x 3) (y x)) (+ x y))
(let ((x 3)) (let ((x #t)) x))

;;; ---- kernel: letrec ----
(letrec ((f (lambda ((n int)) (the pure int (if (= n 0) 1 (f (- n 1))))))) (f 5))

;;; ---- kernel: set! on a mutable variable ----
(let ((x 3 @!)) (set! x 4))
(lambda ((x int @!)) (begin (set! x 4) x))

;;; ---- kernel: and / or / cond / do sugar ----
(and #t #f)
(or #f #t)
(and)
(or)
(cond (#t 1) (else 2))
(cond ((= 1 2) 1) (else 2))
(do ((i 0 (+ i 1))) ((>= i 10) i))
(do ((i 0 (+ i 1)) (h 0 h @acc)) ((>= i 10) h) (set! h (+ h i)))

;;; ---- kernel: regions, ref, new/get/set ----
(new 3)
(get (new 3))
(set ((proj (proj new @!) int) 3) 4)
(lambda ((r (ref int @=))) (get r))
(lambda ((r (ref int @!))) (get r))
(lambda ((r (ref int @!))) (set r 1))
((proj (proj new @!) int) 3)
((proj (proj get @!) int) ((proj (proj new @!) int) 3))
(lambda ((x int)) (new x))

;;; ---- effect masking: an allocation in a private region is masked ----
(let ((r ((proj (proj new @private) int) 3))) 3)
(lambda ((x int)) (let ((r ((proj (proj new @private) int) x))) (get r)))

;;; ---- kernel: plambda / proj ----
(plambda ((t type)) (lambda ((x t)) x))
(proj (plambda ((t type)) (lambda ((x t)) x)) int)
((proj (plambda ((t type)) (lambda ((x t)) x)) int) 3)
((proj (plambda ((t type)) (lambda ((x t)) x)) bool) 3)   ; ill-typed
(plambda ((r region)) (lambda ((x (ref int r))) (get x)))
(plambda ((e effect) (t type)) (lambda ((f (subr e () t))) (f)))

;;; ---- kernel: plet ----
(plet ((s int)) (lambda ((x s)) x))

;;; ---- kernel: dlet / dlambda at the description level ----
(lambda ((x (dlet ((t int)) t))) x)
(lambda ((x ((dlambda ((t type)) t) int))) x)

;;; ---- poly types written out ----
(the pure (poly ((t type)) (subr pure (t) t))
     (plambda ((t type)) (lambda ((x t)) x)))

;;; ---- standard: int ----
(+ 1 2)
(- 1 2)
(* 3 4)
(/ 7 2)
(modulo 7 2)
(remainder 7 2)
(abs -3)
(expt 2 10)
(= 1 2)
(< 1 2)
(<= 1 2)
(> 1 2)
(>= 1 2)
(+ 1 #t)                                ; ill-typed

;;; ---- standard: float ----
(fl+ 1.5 2.5)
(fl* 1.5 2.5)
(fl< 1.5 2.5)
(sqrt 2.5)
(floor 3.7)
(int->float 3)
(fl+ 1 2.5)                             ; ill-typed
1.0                                     ; QUIRK: integer? is true of 1.0, so this is int
(fl+ 1.0 2.5)                           ; QUIRK: same, so ill-typed

;;; ---- standard: char ----
(char=? #\a #\b)
(char-upcase #\a)
(char->int #\a)
(int->char 97)
(char-alphabetic? #\a)

;;; ---- standard: bool ----
(not? #t)
(and? #t #f)
(or? #t #f)
(equiv? #t #f)

;;; ---- standard: uniqueof ----
(unique 3)
(value (unique 3))
(eq? (unique 3) (unique 4))

;;; ---- standard: pairof ----
(cons 1 2)
(car (cons 1 2))
(cdr (cons 1 2))
(null? (cons 1 2))
(cons 1 (cons 2 '()))
(lambda ((p (pairof int bool @=))) (car p))
(lambda ((p (pairof int bool @!))) (cdr p))

;;; ---- standard: listof ----
(list 1 2 3)
(length (list 1 2 3))
(append (list 1) (list 2))
(reverse (list 1 2 3))
(list-ref (list 1 2 3) 0)
(map (lambda ((x int)) (+ x 1)) (list 1 2 3))
(reduce (lambda ((x int) (y int)) (+ x y)) (list 1 2 3) 0)
(for-each (lambda ((x int)) x) (list 1 2 3))
(lambda ((l (listof int @=))) (length l))

;;; ---- standard: string ----
(string-length "abc")
(string-ref "abc" 0)
(string=? "a" "b")
(string->list "abc")
(list->string (string->list "abc"))

;;; ---- standard: vectorof ----
(make-vector 3 0)
(vector-length (make-vector 3 0))
(vector-ref (make-vector 3 0) 0)
(vector-set! ((proj (proj make-vector @!) int) 3 0) 0 1)
(lambda ((v (vectorof int @!))) (vector-set! v 0 1))
(lambda ((v (vectorof int @!))) (vector-ref v 0))

;;; ---- standard: recordof / record / select ----
(record ((a 1) (b #t)))
(select (record ((a 1) (b #t))) a)
(select (record ((a 1) (b #t))) c)      ; ill-typed: no such field
(lambda ((r (recordof ((a int) (b bool)) @=))) (select r a))
(record-set! (record ((a 1)) @!) a 2)
(lambda ((r (recordof ((a int)) @!))) (record-set! r a 2))

;;; ---- standard: oneof / one / tagcase ----
(one (oneof ((a int) (b bool)) @=) a 1)
(the pure (oneof ((a int) (b bool)) @=) (one (oneof ((a int) (b bool)) @=) a 1))
(tagcase (v (one (oneof ((a int) (b bool)) @=) a 1)) (a 1) (b 2))
(tagcase (v (one (oneof ((a int) (b bool)) @=) a 1)) (a v) (b 0))
(one-set! (one (oneof ((a int) (b bool)) @!) a 1) b #t)

;;; ---- standard: promise / delay ----
(delay 3)

;;; ---- standard: vsubr / vlambda ----
(vlambda (xs int) 3)

;;; ---- standard: symbol / sexp ----
(quote a)
'(1 2 3)                                ; QUIRK: no sexp literal syntax in the reference

;;; ---- subtyping and subeffecting ----
(the (maxeff (read @!) (write @!)) int (the (read @!) int 3))
(the (maxeff (read @=)) int (the pure int 3))
(lambda ((f (subr (maxeff) (int) int))) (the (subr (read @=) (int) int) f))
(lambda ((f (subr (read @=) (int) int))) (the (subr (maxeff) (int) int) f)) ; ill-typed

;;; ---- more regions: named regions, runion, effect-masking boundaries ----
(lambda ((r (ref int @red))) (get r))
(lambda ((r (ref int @red)) (s (ref int @blue))) (+ (get r) (get s)))
(the (read (runion @red @blue)) int
     ((lambda ((r (ref int @red)) (s (ref int @blue))) (+ (get r) (get s)))
      ((proj (proj new @red) int) 1)
      ((proj (proj new @blue) int) 2)))
(plambda ((r region)) (lambda ((x (ref int r))) (set x 1)))
(lambda ((x int)) ((proj (proj new @red) int) x))
(let ((v ((proj (proj make-vector @scratch) int) 3 0)))
  (begin (vector-set! v 0 1) (vector-ref v 0)))

;;; ---- dfunc kinds ----
(lambda ((x ((dlambda ((r region)) (ref int r)) @!))) (get x))
(plambda ((f (dfunc (type) type))) (lambda ((x (f int))) x))

;;; ---- higher-order effect polymorphism ----
(plambda ((e effect) (t type) (u type))
  (lambda ((f (subr e (t) u)) (x t)) (f x)))
(lambda ((f (subr (read @red) (int) int))) (f 1))
(lambda ((f (subr (maxeff (read @red) (write @blue)) (int) int))) (f 1))

;;; ---- recursive types via dletrec ----
(lambda ((l (dletrec ((il (oneof ((nil unit) (cons (pairof int il @=))) @=))) il))) l)

;;; ---- mutability of a binding is a static property ----
;;; Appended after the original 155 so earlier case numbers do not move.
;;; These pin the rule that makes FX-87 safe to compile more aggressively than
;;; Scheme: a binding with no explicit region lives in the immutable region and
;;; cannot be assigned at all, so a standard binding's meaning is fixed for
;;; every call site.
(let ((x 1)) (set! x 2))                ; ill-typed: @= is not writable
(set! + -)                              ; ill-typed: a standard binding is immutable
(lambda ((x int)) (set! x 4))           ; ill-typed: parameter has no mutable region
(lambda ((x int @!)) (set! x 4))        ; well-typed, and the write is masked
(let ((f +)) (f 1 2))                   ; a standard binding can still be aliased
(let ((+ 3)) +)                         ; ...and shadowed, which the checker sees
