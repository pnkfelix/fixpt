;;;; -*- Mode:SCHEME; Syntax:SCHEME; Package:SCHEME -*-
;;;;
;;;; This is a test file of working FX-91 programs. 
;;;;
;;;; Feel free to augment it as you wish (with expressions that
;;;; typecheck please since this file is used to test the correctness of
;;;; the FX-91 interpreter).
;;;;
;;;; jouvelot@brokaw.lcs.mit.edu (PSRG)

;;; Do not delete or change this first module expression. It is used
;;; later with a LOAD expression.

(module (define-abstraction t type int)
	(define x (up-t 3)))

(with (module (define f 3))
      f)

(with (module (define f (lambda () (f))))
      f)

(with (module (define f (lambda () 3))
	      (define g (lambda () (f))))
      f)

(with (module (define f (lambda () 3))
	      (define g (lambda () (f))))
      (begin f))

(let ((m (module (define f (lambda () 3))
		 (define g (lambda () (f))))))
  (let ((f (with m f))
	(g (with m g)))
    (begin f)))

(with (module (define-abstraction t type bool)
	      (define f (lambda (x) (up-t x))))
      (f #t))

(with (module (define-abstraction t type bool)
	      (define x (up-t #t))
	      (define f (lambda (x) (up-t x))))
      (if #t x (f #t)))

(lambda ((w bool))
  (with (module (define-abstraction t type bool)
		(define g (lambda (x) (down-t x))))
	(if w g (lambda ((x t)) w))))

(with (module (define-abstraction t type bool)
	      (define f (lambda (x) (up-t x)))
	      (define g (lambda (x) 
			  (if #t 
			      (down-t x)
			      (down-t (f #f))))))
      (f #t))

(with (module (define-abstraction pairof (dfunc type)
		(dlambda ((t type))
			 (subr (maxeff)
			       ((pair (subr (maxeff) 
					    ((car t) (cdr t))
					    t)))
			       t)))
	      (define-description impl
		       (poly ((t type))
			     (subr (maxeff)
				   ((pair (subr (maxeff) 
						((car t) (cdr t))
						t)))
				   t)))
	      (define ([ cons (t type) ] (x t) (y t))
		(up-pairof (lambda (f) (f x y))))
	      (define ([ car (t type) ] p)
		(((proj down-pairof t) p) (lambda ((x t) (y t)) x)))
	      (define ([ cdr (t type) ] p)
		((down-pairof p) (lambda ((x t) (y t)) y))))
      (cdr (cons #t #f)))

(with (module (define m (module (define-abstraction t type bool)
				(define f (lambda (x) (up-t x))))))
      (with m
	    (if #t
		(with m f)
		(with m f))))

(with (module (define-abstraction t type bool)
	      (define-description u (subr (maxeff) ((x t)) t))
	      (define f (lambda ((x u)
				 (z bool))
			  (x (up-t z)))))
      f)

(with (module (define-description u bool))
      (lambda ((x u)) x))

(with (module (define m (module (define-description u bool))))
      (with m
	    (lambda ((x u)) (if x #t #t))))

(lambda ((m (moduleof (val x bool)))) (with m x))

((lambda ((m (moduleof (abs (t u) type) (val x t))))
   (with m x)) 
 (module (define-abstraction t type bool) 
	 (define-abstraction u type unit)
	 (define x (up-t #t))))

(with (module (define not (lambda (x) (if x #t #f)))
	      (define flip (lambda (x) (not x))))
      flip)

(lambda ((m (moduleof (abs t type))) (x (select m t))) x)

(let ((m (load "tests.fx")))
  (with m x))

(lambda ((m (moduleof (desc t bool)))) 
  (lambda ((x (select m t))) 
    (if x m m)))

(let ((m (close (letrec ((f (lambda (x) x))) f)))) (m #t))

(let ((x (new #t))) (begin (get x) (set! x #f)))

(lambda ((ints (moduleof (abs int type)
			 (val zero int)
			 (val one int)
			 (val = (subr pure ((x int) (y int)) bool))
			 (val + (subr pure ((x int) (y int)) int))
			 (val * (subr pure ((x int) (y int)) int))
			 (val - (subr pure ((x int) (y int)) int)))))
  (with ints 
	(let ((dec (lambda (n)
			 (do (i n (- n one))
			     ((= i one) n)
			   #u))))

	  (dec one))))

((lambda ((ints (moduleof (abs newint type)
			  (val == (subr pure ((x newint)) bool)))))
   2)
 (module (define-abstraction newint type int)
	 (define (== (x newint)) #t)))

((lambda ((ints (moduleof 
		 (abs newint type)
		 (val zero newint)
		 (val one newint)
		 (val == (subr pure ((x newint) (y newint)) bool))
		 (val ** (subr pure ((x newint) (y newint)) newint))
		 (val -- (subr pure ((x newint) (y newint)) newint)))))
   (with ints 
	 (letrec ((fact (lambda (n)
			  (if (== n zero)
			      one
			      (** n (fact (-- n one))))))
		  (id (close (lambda (x) x)))
		  (even? (lambda (n)
			   (or (== n zero)
			       (odd? (-- n one)))))
		  (odd? (lambda (n)
			  (or (== n one)
			      (even? (-- n one))))))
	   (if (odd? one) 
	       (fact one)
	       one))))
 (module 
  (define-abstraction newint type int)
  (define zero (up-newint 0))
  (define one (up-newint 1))
  (define (== x y) (= (down-newint x) (down-newint y)))
  (define (** x y) (up-newint (* (down-newint x) (down-newint y))))
  (define (-- x y) (up-newint (- (down-newint x) (down-newint y))))))

(if #t 
    (set! ((let ((x (lambda () (new #t))))
	     (begin (get (x)) x))) 
	  #t)
    #u)

(close (lambda ((ints (moduleof (abs int type)
				(val one int)
				(val = (subr pure ((x int) (y int)) bool)))))
	 (with ints 
	       (letrec ((fact (lambda (n)
				(if (= n one) one (fact n)))))
		 fact))))

(plambda ((t type))
	 (with (module (define x (lambda ((x t)) x)) 
		       (define h (lambda ((y t)) y))) 
	       (if #t x h)))

(with (module (define-typed f
		(subr init ((x bool)) int)
		(lambda (x) (begin (new #t) (f #t)))))
      f)

(with (module (define f
		(lambda (x) (begin (f #t)))))
      f)

(let ((y (new 3)))
  (with (module (define-typed f
		  (subr init () (refof (refof int)))
		  (lambda () (new y))))
	f))

(plambda ((t type))
	 (lambda (x (u t))
	   (let ((y (lambda ((z t)) (begin x z)))) 
	     (begin (if #t u x) 
		    (y x)))))

(with (module (define-description t ((dlambda ((t type)) bool) bool)))
      (lambda ((x t)) (if x #t #f)))

(module (define-description f (sumof (a bool))) 
	(define g (lambda ((x f)) x)))

(with (module 
       (define-abstraction t type (sumof (a bool) (b t)))
       (define-description o 
	 (sumof (a ((dlambda ((t type)) bool) t)) (b t)))
       (define x (up-t (sum o a #t))))
      (lambda ((x o)) x))

(with (module 
       (define-abstraction t type (sumof (a bool) (b t)))
       (define-description o 
	 (sumof (a ((dlambda ((t type)) bool) t)) (b t)))
       (define x (up-t (sum o a #t))))
      (sum o b x))

(with (module 
       (define-abstraction t type (sumof (a bool) (b t)))
       (define-description o 
	 (sumof (a ((dlambda ((t type)) bool) t)) (b t)))
       (define f (lambda ((x t))
		   (let ((y (down-t x)))
		     (if #t #f (g y)))))
       (define x (up-t (sum o a #t)))
       (define-typed g
	 (subr write ((z o)) bool)
	 (lambda ((z o)) 
	   (tagcase o
		    z
		    a
		    (lambda (z1) z1)
		    (lambda (z)
		      (tagcase o
			       z
			       b
			       (lambda (z1) (f (up-t z)))
			       (lambda (x)
				 (error "Unknown tag"))))))))
      (if #t (f x) (g (sum o b x))))

(with (module (define-abstraction int type (sumof (zero unit) (succ int)))
	      (define-description rep (sumof (zero unit) (succ int)))
	      (define zero (up-int (sum rep zero #u)))
	      (define one (up-int (sum rep succ zero)))
	      (define (minus x)
		(tagcase rep
			 (down-int x)
			 zero
			 (lambda (x) zero)
			 (lambda (x) 
			   (tagcase rep
				    x
				    succ
				    (lambda (x) x)
				    (lambda (x) zero)))))
	      (define (add x y)
		(tagcase rep
			 (down-int x)
			 zero
			 (lambda (x) (minus y))
			 (lambda (x)
			   (tagcase rep
				    x
				    succ
				    (lambda (x)
				      (add (add x y) one))
				    (lambda (x) zero))))))
      ((if #t add (lambda (x y) (minus x))) one one))

(let ((m (module (define-abstraction u type bool)
		 (define-abstraction v type bool)
		 (define x (up-u #t))
		 (define y (up-v #f)))))
  ((lambda ((m (moduleof (abs (u v) type) (val x u) (val y v)))
	    (x m..u)
	    (y m..v))
     (if #t x x))
   m m.x m.y))

(lambda ((m (moduleof (abs u type) (val x u))) (x m..u))
     (if #t x x))

(let ((m (module (define-abstraction u type bool)
		 (define x (up-u #t)))))
  ((lambda ((m (moduleof (abs u type) (val x u))) (x m..u))
     (begin (if #t x x) 3))
   m m.x))

(let ((m1 (module (define-abstraction u type bool)
		 (define x (up-u #t)))))
  ((lambda ((m (moduleof (abs u type) (val x u))) (x m..u))
     (if #t x x))
   m1 m1.x))

(lambda ((m (moduleof (abs t (dfunc type)) (val x (t bool))))
	 (y (m..t bool)))
  (if #t m.x y))

(let ((x (module (define-abstraction t type bool) (define z (up-t #t))))
      (y (module (define-abstraction t type bool) (define z (up-t #t)))))
  (if #t x.z x.z))

(with (module (define id
		(with (module (define (f x) x)) (f f))))
      (id 3))

(let ((f (lambda () (module (define-abstraction t type bool) 
			    (define x (up-t #t))))))
  ((lambda ((m (subr pure () (moduleof (abs t type) (val x t))))
	    (x (select (m) t)))
     x)
   f
   (with (f) x)))

(let ((m (module (define-abstraction u type bool)
		 (define x (up-u #t)))))
  ((lambda ((mm (moduleof (abs u type) (val x u))) (x mm..u))
     (if #t x x))
   m m.x))

(lambda ((f (poly ((t type))
		  (poly ((u type)) 
			u)))
	 (g (poly ((u type))
		  (poly ((t type))
			t))))
  (if #t f g))

(let ((f (lambda () 
	   (lambda () 
	     (module (define-abstraction t type bool)
		     (define x (up-t #t)))))))
  ((lambda ((m (subr pure () (moduleof (abs t type) (val x t))))
	    (x (select (m) t)))
     x)
   (f)
   (with ((f)) x)))

(with (module) 
      (with (module (define f (lambda () 
				(lambda () 
				  (module (define-abstraction t type bool)
					  (define x (up-t #t)))))))
	    ((lambda ((m (subr pure () (moduleof (abs t type) (val x t))))
		      (x (select (m) t)))
	       x)
	     (f)
	     (with ((f)) x))))

(with (module) 
      (with (module (define (f)
		      (lambda () 
			(module (define-abstraction t type bool)
				(define x (up-t #t))))))
	    ((lambda ((m (moduleof (abs t type) (val x t)))
		      (x (select m t)))
	       x)
	     ((f))
	     (with ((f)) x))))

(lambda ((m (moduleof (val f (subr pure ((t int)) int)))))
  (let ((m1 (module (define (f x) x))))
    (begin
      (if #t m m1)
      (if #t (module (define (f (c char)) c)) m1)
      (if #t (module (define (f y) y)) m1)
      )))

(let ((+ fl+)) (+ 1.2 1.3))      

(lambda ((m (moduleof (abs listof (dfunc type)) 
		      (val nill (poly ((t type)) (listof t)))
		      (val last (poly ((t type)) 
				      (subr pure ((l (listof t))) t))))))
  (with m 
	(last [ nill bool ])))

(let* ((pairs (module 
	       (define-abstraction pairof (dfunc type type) 
		 (dlambda ((t1 type) (t2 type))
			  (moduleof (val car t1) (val cdr t2))))
	       (define-description rep
		 (dlambda ((t1 type) (t2 type))
			  (moduleof (val car t1) (val cdr t2))))
	       (define cons
		 (close
		  (lambda (x y)
		    (up-pairof
		     (module (define car x) (define cdr y))))))
	       (define car
		 (plambda ((t1 type) (t2 type))
			  (lambda ((p (pairof t1 t2)))
			    (with (down-pairof p) car))))
	       (define cdr
		 (plambda ((t1 type) (t2 type))
			  (lambda (p)
			    (with ([ down-pairof t1 t2 ] p) cdr)))))))
  (with pairs
	(lambda ((l (rep int int)))
	  l.cdr)))

(lambda ((u unit))
  (let* ((pairs (module
		 (define-abstraction pairof (dfunc type type) 
		   (dlambda ((t1 type) (t2 type))
			    (moduleof (val car t1) (val cdr t2))))
		 (define cons
		   (close
		    (lambda (x y)
		      (up-pairof
		       (module (define car x) (define cdr y))))))
		 (define car
		   (plambda ((t1 type) (t2 type))
			    (lambda ((p (pairof t1 t2)))
			      (with (down-pairof p) car))))
		 (define cdr
		   (plambda ((t1 type) (t2 type))
			    (lambda (p)
			      (with ([ down-pairof t1 t2 ] p) cdr)))))))
    (let ((lists
	   (with pairs
		 (module 
		  (define-abstraction listof (dfunc type)
		    (dlambda ((t type))
			     (sumof (nil unit) 
				    (cons (pairof t (listof t))))))
		  (define-description rep
		    (dlambda ((t type))
			     (sumof (nil unit) 
				    (cons (pairof t (listof t))))))
		  (define nill
		    (plambda ((t type))
			     (up-listof (sum (rep t) nil u))))
		  (define one-two (cons 1 (cons 2 (null))))
		  (define last
		    (close
		     (lambda (x default)
		       (letrec ((last 
				 (lambda ((l (rep bool)) pred)
				   (tagcase 
				    (rep bool)
				    l
				    nil 
				    (lambda (x) pred)
				    (lambda (l)
				      (tagcase
				       (rep bool)
				       l
				       cons
				       (lambda (l)
					 (last (down-listof (cdr l)) 
					       (car l)))
				       (lambda (l) pred)))))))
			 (last (down-listof x) default)))))))))
      (with lists
	    (if #t 
		(lambda () (last [ nill bool ] #f))
		(lambda () #t))))))

(lambda ((u unit))
  (let* ((pairs (module
		 (define-abstraction pairof (dfunc type type) 
		   (dlambda ((t1 type) (t2 type))
			    (moduleof (val car t1) (val cdr t2))))
		 (define car
		   (plambda ((t1 type) (t2 type))
			    (lambda ((p (pairof t1 t2)))
			      (with (down-pairof p) car))))
		 (define cdr
		   (plambda ((t1 type) (t2 type))
			    (lambda (p)
			      (with ([ down-pairof t1 t2 ] p) cdr)))))))
    (with pairs
	  (module (define-abstraction listof (dfunc type)
		    (dlambda ((t type))
			     (sumof (nil unit) 
				    (cons (pairof t (listof t))))))
		  (define-description rep
		    (dlambda ((t type))
			     (sumof (nil unit) 
				    (cons (pairof t (listof t))))))
		  (define last
		    (close
		     (lambda (x default)
		       (letrec ((last 
				 (lambda ((l (rep int)) pred)
				   (tagcase
				    (rep int)
				    l
				    cons
				    (lambda (l)
				      (last (down-listof (cdr l)) 
					    (car l)))
				    (lambda (l) pred)))))
			 (last (down-listof x) default)))))))))

(let* ((pairs (module 
	       (define-abstraction pairof (dfunc type type)
		 (dlambda ((t1 type) (t2 type))
			  (moduleof (val car t1) (val cdr t2))))
	       (define cons
		 (close
		  (lambda (x y)
		    (up-pairof
		     (module (define car x) (define cdr y)))))))))
  (let ((lists
	 (with pairs
	       (module (define-abstraction listof (dfunc type)
			 (dlambda ((t type))
				  (sumof (nil unit) 
					 (cons (pairof t (listof t))))))
		       (define-description rep
			 (dlambda ((t type))
				  (sumof (nil unit) 
					 (cons (pairof t (listof t))))))
		       (define nil
			 (plambda ((t type))
				  (up-listof (sum (rep t) nil #u))))
		       (define end [ nil int ])
		       (define one-two 
			 (cons 1 (cons 2 [ nil int ])))))))
    lists))

(let* ((f (open-input-stream "tests.fx"))
       (expr (stream-read-sexp f)))
  (if (sexp=? expr '(module (define-abstraction t type int)
			    (define x (up-t 3))))
      (begin
	(stream-write-sexp standard-output expr)
	(close-stream f))
      (error "Incorrect read operation")))

(let* ((v (scan + (make-vector 10 1)))
       (u (list->vector
	    (cons #f 
		  (cons #f 
			(cons #f
			      (cons #t 
				    (cons #t 
					  (cons #f
						(cons #t
						      (cons 
						       #f 
						       (cons #f 
							     (cons 
							      #t 
							      (null))
							     )))
						)))
			      ))))))
  (begin
    (permute (cshift 3 1) (segmented-scan + u v))
    (compress u v)))

(module (define-abstraction pair (dfunc type type)
	  (dlambda ((x type) (y type))
		   (poly ((z type))
			 (subr pure
			       ((p (subr pure ((car x) (cdr y)) z)))
			       z))))
	(define ([mk-pair (x type) (y type)] (a x) (b y))
	  (up-pair (plambda ((z type))
			    (lambda ((p (subr pure ((car x) (cdr y)) z)))
			      (p a b)))))
	(define ([car (x type) (y type)] (p (pair x y)))
	  ((down-pair p) (lambda (x y) x))))


(close (with (if #t
		 (module (define (f x) x)) 
		 (module (define (f x) x)))
	     (begin (f #t) (f 3))))

(the (moduleof (val f (subr pure ((x int)) int)))
     (module (define (f x) x)))

(with (if #f
	  (module (define (f x) x))
	  (module (define (f (x int)) (+ x 1))))
      (f 2))

(if #f
    (module (define (f x y) (+ (y x) 1)))
    (module (define (f x y) (begin (not? x) 1))))

(let ((m (module (define (f x) x))))
  (begin
    (with m (f #t))
    (if #t 
	m
	(module (define (f (x int)) 2)))
    (with m (f #t))))

(if #t
    (module (define (f x) x)
	    (define y (module (define (g x) x))))
    (module (define (f x) x)
	    (define y (module (define (g x) (if #t (f x) x))))))

(if #t
    (module (define (y x) (module (define (g y) y))))
    (module (define (y x) (module (define (g y) (if #t (x y) y))))))

(the (moduleof (abs t type) (val x (subr (maxeff init read) () t)))
     (module (define-abstraction t type bool)
	     (define x (lambda () (let ((u (new 3))) 
				    (begin (get u) (up-t #t)))))))

(plambda
  ((channelof (dfunc type)) (pairof (dfunc type type)))
  (lambda 
    ((cobegin (poly ((t1 type) (t2 type))
		    (subr pure ((x t1) (x t2)) (pairof t1 t2))))
     (channel (poly ((t type))
		    (subr pure () (channelof t))))
     (from (poly ((t type))
		 (subr pure ((c (channelof t))) t)))
     (to (poly ((t type))
	       (subr pure
		     ((c (channelof t)))
		     (subr pure ((x t)) unit)))))
    (module (define (f cont n)		
	      (if (<= n 1)
		  (cont n)
		  (let ((local (channel)))
		    (begin
		      (cobegin (cont (+ (from local) (from local)))
			       (cobegin (f (to local) (- n 1))
					(f (to local) (- n 2))))
		      #u)))))))

(if #f
    (if #t
	(module (define (f x) x)
		(define y (module (define (g x) x))))
	(module (define (f x) x)
		(define y (module (define (g x) (if #t (f x) x))))))
    (module (define (f (x int)) x)
	    (define y (module (define (g (x int)) x)))))

(module (define-description f (productof (t int) (u bool)))
	(define-abstraction fg type (productof (t int) (u fg)))
	(define-description ft
	  (dlambda ((t type))
		   (productof (one int) (two t))))
	(define x (product (ft bool) 1 #f))
	(define y (extract (ft bool)
			   (product (ft bool) 1 #f)
			   one)))

(match 1 (1 2) (_ 3))

(match 1 (2 2) (_ 3))

(with (module (define-abstraction t type int) 
	      (define z up-t)) 
      (z 3))

(with (module (define-datatype i (z unit) (s int)))
      z)

(with (module (define-datatype i (z unit) (s int)))
      (z #u))

(with (module (define-datatype i (z int)))
      (z 3))

(with (module (define-datatype i (z int)))
      (match (z 3)
	     (_ 2)))

(with (module (define-datatype i (z int)))
      (match (z 3)
	     ((z~ x) 2)))

(with (module (define-datatype i (z int)))
      (match (z 3)
	     ((z~ x) (z 2))))

(with (module (define-datatype i (z unit) (s int)))
      z~)

(with (module (define-datatype i (z unit) (s int)))
      (z #u))

(with (module (define-datatype i (z unit) (s int)))
      (match (z #u)
	     ((s~ x) (s x))
	     (_ (s 3))))

(with (module (define-datatype num (zero unit) (succ num)))
      (letrec ((two (succ (succ (zero #u))))
	       (one (succ (zero #u)))
	       (add (lambda (x y)
		      (match x
			     ((zero~ _) y)
			     ((succ~ x) (succ (add x y)))))))
	(add two one)))

(with (module (define-abstraction ft
		(dfunc type) (dlambda ((t type)) t))
	      (define down down-ft))
      (letrec ((num (lambda (x)
		      (down x))))
	num))

(with (module (define-datatype (tree (t type))
		(leaf t)
		(node (tree t))))
      (letrec ((numbers (lambda (x)
			  (match x
				 ((leaf~ y) (leaf y))))))
	(numbers (leaf #t))))

(with (module (define-datatype (tree (t type))
		(leaf t)
		(node (tree t))))
      (letrec ((numbers (lambda (x)
			  (match x
				 ((node~ lhs)
				  (numbers lhs))))))
	numbers))

(with (module (define-datatype (tree (t type))
		(node (tree t))))
      (letrec ((numbers (lambda (x)
			  (match x
				 ((node~ lhs)
				  (+ (numbers lhs) 1))))))
	numbers))

(with (module (define-datatype tree
		(leaf int)
		(node tree)))
      (letrec ((numbers (lambda (x)
			  (match x
				 ((leaf~ _) 1)
				 ((node~ lhs) (numbers lhs))))))
	(numbers (node (leaf 0)))))

(with (module (define-datatype (tree (t type))
		(leaf t)))
      (letrec ((numbers (lambda (x)
			  (match x
				 ((leaf~ y) (numbers (leaf y)))))))
	numbers))

(with (module (define-datatype (tree (t type))
		(node (tree t))))
      (letrec ((numbers (lambda (x)
			  (match x
				 ((node~ y) (numbers (node y)))))))
	numbers))

(with (module (define-datatype (tree (t type))
		(leaf int)
		(node (tree t))))
      (lambda (x z)
	(match x
	       ((node~ y) 
		(if #t x (node y)))
	       ((leaf~ _) z))))

(with (module (define-datatype (tree (t type))
		(node t)))
      (lambda (x z)
	(match x
	       ((node~ y) 
		(if #t x (node y)))
	       ((node~ _) z))))

(with (module (define-datatype (tree (t type))
		(node int)))
      (lambda (x)
	(match x
	       ((node~ _) x)
	       ((node~ y) (node y)))))

(let ((m (module
	  (define-abstraction tree (dfunc type) 
	    (dlambda ((t type)) (sumof (l (productof (i int))))))
	  (define-description tree-rep
	    (dlambda ((t type)) (sumof (l (productof (i int))))))
	  (define-typed node
	    (poly ((t type))
		  (subr pure ((i int)) (tree t)))
	    (plambda ((t type))
		     (lambda ((i int))
		       (up-tree (sum (tree-rep t)
				     l
				     (product (productof (i int))
					      i)))))))))
  (with m
	(lambda ((x (tree bool)))
	  (if #t 
	      (node 3)
	      x))))

(with (module
       (define-abstraction tree (dfunc type) 
	 (dlambda ((t type)) (sumof (l (productof (i int))))))
       (define-description tree-rep
	 (dlambda ((t type)) (sumof (l (productof (i int))))))
       (define-typed node
	 (poly ((t type))
	       (subr pure ((i int)) (tree t)))
	 (plambda ((t type))
		  (lambda ((i int))
		    (up-tree (sum (tree-rep t)
				  l
				  (product (productof (i int))
					   i)))))))
      (lambda ((x (tree bool)))
	(if #t 
	    (node 3)
	    x)))

(with (module (define-datatype (tree (t type))
		(leaf t)
		(node t)))
      (lambda ((z (tree int)))
	(letrec ((numbers (lambda (x)
			    (match x
				   ((leaf~ y) 0)
				   ((node~ lhs) 
				    (numbers z))))))
	  numbers)))

(with (module (define-datatype (tree (t type))
		(leaf t)
		(node (tree t))))
      (letrec ((numbers (lambda (x)
			  (match x
				 ((leaf~ _) 1)
				 ((node~ lhs) (numbers (node lhs)))))))
	numbers))

(let ((m (module (define-datatype (tree (t type))
		   (leaf t)
		   (node (tree t))))))
  (with m
	(letrec ((numbers (lambda (x)
			    (match x
				   ((leaf~ _) 1)
				   ((node~ lhs) (numbers (node lhs)))))))
	  numbers)))

(with (module (define-datatype (tree (t type))
		(leaf t)
		(node (tree t) (tree t))))
      (letrec ((numbers (lambda (x)
			  (match x
				 ((leaf~ _) 1)
				 ((node~ lhs rhs)
				  (+ (numbers lhs) (numbers rhs)))))))
	(numbers (node (leaf #t) (node (leaf #f) (leaf #t))))))


(match 1
       (1 (append (cons 1 (null)) (null))))

(with (module (define-abstraction tree (dfunc type) listof))
      (with (module (define-typed fringe
		      (subr (maxeff) ((x (tree int))) (listof int))
		      (lambda (x)
			(fringe x))))
	    fringe))

(let ((m (module (define-datatype (tree (t type))
		   (leaf t)
		   (node (tree t) (tree t))))))
  (with m
	(let ((m1 (module (define (fringe x)
			    (match x
				   ((leaf~ x) (cons x (null)))
				   ((node~ lhs rhs)
				    (append (fringe lhs) (fringe rhs))))))))
	  (with m1
		(fringe (node (leaf 1) (leaf 2)))))))

(with (module (define-abstraction tree type int)
	      (define-description num int)
	      (define leaf up-tree))
      (the (subr (maxeff) ((x num)) tree)
	   leaf))

(with (module (define-datatype (tree (t type))
		(leaf int)
		(node (tree int) (tree int))))
      (with (module
	     (define-typed fringe
	       (subr (maxeff init read) ((x (tree int))) (listof int))
	       (lambda (x) 
		 (match x
			((leaf~ x) (cons x (null)))
			((node~ lhs rhs)
			 (append (fringe lhs) (fringe rhs)))))))
	    (fringe (node (leaf 1) (leaf 2)))))

(extend (module (define x 1)
		(define y 2))
	(module (define x 3.4)
		(define z #\c)))

(extend (module (define x 1)
		(define y 2))
	(module (define x (+ y 3))
		(define z #\c)))

(with (module (define-datatype i (z unit)))
      (module (define zero (z #u))))

(module (define-datatype i (z unit))
	(define zero (lambda () (z #u))))

(match (car (match '(q w) ((list->sexp~ x) x)))
       ((sym->sexp~ x) x))

(match '(1 3) 
       ((list->sexp~ l) 
	(+ (match (car l) 
		  ((int->sexp~ i) i))
	   (match (car (cdr l)) 
		  ((int->sexp~ i) i)))))

(let ((s (open-input-stream "tests.list.fx")))
  (letrec ((loop (lambda ()
		   (if (stream-char-eof? s)
		       #u
		       (begin (stream-write-char standard-output 
						 (stream-read-char s))
			      (loop))))))
    (loop)))

(let ((cons~ 
       (plambda ((t type) (u type) (e1 effect) (e2 effect))
		(lambda ((x (listof u))
			 (s (subr e1 ((fst u) (rest (listof u))) t))
			 (f (subr e2 ((x (listof u))) t)))
		  (if (null? x)
		      (f x)
		      (s (car x) (cdr x))))))
      (nil~ (plambda ((t type) (u type) (e1 effect) (e2 effect))
		     (lambda ((x (listof u))
			      (s (subr e1 () t))
			      (f (subr e2 ((x (listof u))) t)))
		       (if (null? x)
			   (s)
			   (f x))))))
  (sexp=? (match '(b s)
		 ((list->sexp~ (nil~)) 'd)
		 ((list->sexp~ (cons~ x (cons~ y _))) x))
	  (match '(c)
		 ((list->sexp~ (cons~ x (nil~))) 'b)
		 ((list->sexp~ (cons~ x (cons~ y _))) x))))

(lambda ((x (select (module (define-abstraction t type int)
			    (define-description d (listof t))
			    (define x (up-t 0))) d)))
  x)
  

(let ((m (module (define-abstraction t type int) (define x (up-t 0))))
      (f (lambda ((m (moduleof (abs t type) (val x t)))
		  (y m..t))
	   y)))
  (f m m.x))

(module
 (define-datatype fl-def
   (make-fl-def int fl-exp))
 (define-abstraction fl-exp type int)
 (define (fl-def-var def)
   (match def
	  ((make-fl-def~ var _) var))))

(let ((^ get)
      (:= set!)
      (ref new)
      (cons~ 
       (plambda ((t type) (u type) (e1 effect) (e2 effect))
		(lambda ((x (listof u))
			 (s (subr e1 ((fst u) (rest (listof u))) t))
			 (f (subr e2 ((x (listof u))) t)))
		  (if (null? x)
		      (f x)
		      (s (car x) (cdr x))))))
      (nil~ (plambda ((t type) (u type) (e1 effect) (e2 effect))
		     (lambda ((x (listof u))
			      (s (subr e1 () t))
			      (f (subr e2 ((x (listof u))) t)))
		       (if (null? x)
			   (s)
			   (f x))))))
 ;;; Parser for full-fledged FL (courtesy of Franklyn).
 ;;; Desugars parsed FL expressions into FLK (FL Kernel) expressions
 ;;;
 ;;; . define-datatype -> define-datatype
 ;;; . sym -> sym, sym=? -> sym=?
 ;;; . list-of -> listof
 ;;; . sexpr -> sexp
 ;;; . changed exp from name in fl-def-exp
 ;;; . watch for sym->sexp missing when sym->sexp~ is used in
 ;;;   destructuring
 ;;; . the list->sexp~ was missing when willing to do a map.
 ;;; . _ was missing in parse-fl-program
 ;;; . changed (listof sym) into (listof var) in fl-exp for let.
 ;;; . faked flk-unary-prim and flk-binary-prim 
 ;;; . changed fl-def-name to fl-def-var
 ;;; . changed named lets in desugar.
 ;;; . (desugar-fl-exp rator) missing in desugar (for application)
 ;;; . replaced list by cons with nil.
 ;;; . recursion-flk uses a var (not a symbol)

  (with 
   (module (define-description flk-unary-prim string)
	   (define-description flk-binary-prim string))
   (module

  ;;; Datatype declarations

  ;;; -------------------------------------------------------------
  ;;; Syntactic datatypes for FL

					; Programs  
    (define-datatype fl-program 
      (make-fl-program fl-exp (listof fl-def)))

    (define-datatype fl-def
      (make-fl-def var fl-exp))

					; Variables
    (define-datatype var
      (make-var sym int))

    (define-abstraction fl-exp type int)

    (define fl-def-var
      (lambda (def)
	(match def
	       ((make-fl-def~ var _) var))))

					; Definitions
					; Expressions
    (define-datatype fl-exp
      (numeric-literal->fl-exp int)
      (boolean-literal->fl-exp bool)
      (symbolic-literal->fl-exp sym)
      (var->fl-exp var)	
      (if->fl-exp fl-exp fl-exp fl-exp)
      (abstraction->fl-exp (listof var) fl-exp)
      (application->fl-exp fl-exp (listof fl-exp))
      (let->fl-exp (listof var) (listof fl-exp) fl-exp)
      (letrec->fl-exp (listof var) (listof fl-exp) fl-exp)
      (pair->fl-exp fl-exp fl-exp))

    (define fl-def-exp
      (lambda (def)
	(match def
	       ((make-fl-def~ _ exp) exp))))

    (define sym->var
      (lambda (sym)
	(make-var sym 0)))

    (define var-name
      (lambda (var)
	(match var
	       ((make-var~ name num) name))))

    (define same-var? 
      (lambda (var1 var2)
	(match var1
	       ((make-var~ name1 num1)
		(match var2
		       ((make-var~ name2 num2)
			(and (sym=? name1 name2)
			     (= num1 num2))))))))

    (define fresh-var
      (let ((counter (ref 1)))
	(lambda ()
	  (let ((value (^ counter)))
	    (begin
	      (:= counter (+ (^ counter) 1))
	      (make-var (symbol fresh) value))))))

  ;;; Parsing

    (define parse-fl-program
      (lambda (sexpr)
	(match sexpr
	       ((list->sexp~ (cons~ (sym->sexp~ (symbol program))
				    (cons~ body defs)))
		(make-fl-program (parse-fl-exp body) 
				 (map parse-fl-def defs)))
	       (_ (error "PARSE-FL-PROGRAM: Syntax error - not a program")))))

    (define parse-fl-def
      (lambda (sexpr)
	(match sexpr
	       ((list->sexp~ (cons~ (sym->sexp~ (symbol define))
				    (cons~ (sym->sexp~ name)
					   (cons~ body (nil~)))))
		(make-fl-def (sym->var name) (parse-fl-exp body)))
	       (_ (error "PARSE-FL-DEF: Syntax error - not a definition")))))

    (define parse-fl-var
      (lambda (sexpr)
	(match sexpr
	       ((sym->sexp~ s) (sym->var s))
	       (_ (error "PARSE-FL-VAR: not a variable!")))))

    (define parse-fl-binding-name
      (lambda (sexpr)
	(match sexpr
	       ((list->sexp~ (cons~ name _)) (parse-fl-var name)) 
	       (_ (error "PARSE-FL-BINDING-NAME: Malformed binding")))))

    (define parse-fl-binding-exp
      (lambda (sexpr)
	(match sexpr
	       ((list->sexp~ (cons~ _ (cons~ exp (nil~))))
		(parse-fl-exp exp))
	       (_ (error "PARSE-FL-BINDING-EXP: Malformed binding")))))

    (define parse-fl-exp
      (lambda (sexpr)
	(match sexpr
	       ((int->sexp~ n) (numeric-literal->fl-exp n))
	       ((bool->sexp~ b) (boolean-literal->fl-exp b))
	       ((sym->sexp~ s) 
		(var->fl-exp (parse-fl-var (sym->sexp s))))
	       ((list->sexp~ (cons~ (sym->sexp~ (symbol symbol))
				    (cons~ (sym->sexp~ s) 
					   (nil~))))
		(symbolic-literal->fl-exp s))
	       ((list->sexp~ (cons~ (sym->sexp~ (symbol if))
				    (cons~ test
					   (cons~ con (cons~ alt (nil~))))))
		(if->fl-exp (parse-fl-exp test)
			    (parse-fl-exp con)
			    (parse-fl-exp alt)))
	       ((list->sexp~ (cons~ (sym->sexp~ (symbol lambda))
				    (cons~ (list->sexp~ vars)
					   (cons~ body (nil~)))))
		(abstraction->fl-exp (map parse-fl-var vars)
				     (parse-fl-exp body)))
	       ((list->sexp~ (cons~ (sym->sexp~ (symbol let))
				    (cons~ (list->sexp~ bindings)
					   (cons~ body (nil~)))))
		(let->fl-exp (map parse-fl-binding-name bindings)
			     (map parse-fl-binding-exp bindings)
			     (parse-fl-exp body)))
	       ((list->sexp~ (cons~ (sym->sexp~ (symbol letrec))
				    (cons~ (list->sexp~ bindings)
					   (cons~ body (nil~)))))
		(letrec->fl-exp (map parse-fl-binding-name bindings)
				(map parse-fl-binding-exp bindings)
				(parse-fl-exp body)))
	       ((list->sexp~ (cons~ (sym->sexp~ (symbol pair))
				    (cons~ left (cons~ right (nil~)))))
		(pair->fl-exp (parse-fl-exp left) (parse-fl-exp right)))
	       ((list->sexp~ (cons~ operator operands))
		(application->fl-exp (parse-fl-exp operator) 
				     (map parse-fl-exp operands)))
	       (_ (error "PARSE-FL-EXP: Unknown FL expression!")))))

  ;;; -------------------------------------------------------------
  ;;; Syntactic datatypes for FLK

    (define-datatype flk-exp
      (numeric-literal->flk-exp int)
      (boolean-literal->flk-exp bool)
      (symbolic-literal->flk-exp sym)
      (var->flk-exp var)
      (unary-call->flk-exp flk-unary-prim fl-exp)
      (binary-call->flk-exp flk-binary-prim fl-exp fl-exp)
      (abstraction->flk-exp var flk-exp)
      (application->flk-exp flk-exp flk-exp)
      (conditional->flk-exp flk-exp flk-exp flk-exp)
      (recursion->flk-exp var flk-exp)
      (pair->flk-exp flk-exp flk-exp))

  
  ;;; Desugaring FL Programs and expressions into FLK exps

    (define desugar-fl-program
      (lambda (fl-program)
	(match fl-program 
	       ((make-fl-program~ body defs)
		(desugar-letrec
		 (map fl-def-var defs)
		 (map fl-def-exp defs)
		 body)))))

    (define desugar-fl-exp
      (lambda (fl-exp)
	(match fl-exp
	       ((numeric-literal->fl-exp~ n) (numeric-literal->flk-exp n))
	       ((boolean-literal->fl-exp~ b) (boolean-literal->flk-exp b))
	       ((symbolic-literal->fl-exp~ s) (symbolic-literal->flk-exp s))
	       ((var->fl-exp~ var) (var->flk-exp var))
	       ((if->fl-exp~ test con alt)
		(conditional->flk-exp (desugar-fl-exp test)
				      (desugar-fl-exp con)
				      (desugar-fl-exp alt)))
	       ((abstraction->fl-exp~ syms body)
		(if (null? syms)
		    (abstraction->flk-exp (fresh-var)
					  (desugar-fl-exp body))
		    (letrec ((recur 
			      (lambda (vars)
				(if (null? vars)
				    (desugar-fl-exp body)
				    (abstraction->flk-exp 
				     (car vars)
				     (recur (cdr vars)))))))
		      (recur syms))))
	       ((application->fl-exp~ rator rands)
		(if (null? rands)
		    (application->flk-exp (desugar-fl-exp rator)
					  (numeric-literal->flk-exp 0))
		    (letrec ((loop (lambda (desugared-rator unsugared-rands)
				     (if (null? unsugared-rands)
					 desugared-rator
					 (loop
					  (application->flk-exp 
					   desugared-rator
					   (desugar-fl-exp
					    (car unsugared-rands)))
					  (cdr unsugared-rands))))))
		      (loop (desugar-fl-exp rator) rands))))
	       ((let->fl-exp~ vars exps body)
		(desugar-fl-exp
		 (application->fl-exp (abstraction->fl-exp vars body)
				      exps)))
	       ((letrec->fl-exp~ vars exps body)
		(desugar-letrec vars exps body))
	       ((pair->fl-exp~ left right)
		(pair->flk-exp (desugar-fl-exp left) 
			       (desugar-fl-exp right))))))

  ;;; YUK!!!
	 
    (define desugar-letrec
      (lambda (vars exps body)
	(let ((church-var (fresh-var))
	      (selector-var (fresh-var)))
	  (let ((church-fl (var->fl-exp church-var))
		(selector-fl (var->fl-exp selector-var)))
	    (application->flk-exp 
	     (recursion->flk-exp 
	      church-var
	      (abstraction->flk-exp
	       selector-var
				; Create an FL LET exp and translate to FLK
	       (desugar-fl-exp
		(let->fl-exp 
		 vars
		 (map (lambda (var) 
			(application->fl-exp 
			 church-fl
			 (cons (abstraction->fl-exp vars
						    (var->fl-exp var))
			       ([null fl-exp]))))
		      vars)
			     (application->fl-exp selector-fl exps)))))
	     (desugar-fl-exp 
	      (abstraction->fl-exp vars body))))))))))


(module (define-datatype tree (leaf int) (node tree tree))
	(define my-tree (lambda () (node (leaf 1) (leaf 0)))))

(lambda (f)
  (lambda ((w (subr write ((x bool)) bool)))
    (if #t
	f
	(lambda (x) (begin (f x) (w x))))))

(lambda (f)
  (lambda ((w (subr write ((x bool)) bool))
	   (r (subr read ((x bool)) bool)))
    (if #t
	(lambda (x) (begin (f x) (r x)))
	(lambda (x) (begin (f x) (w x))))))

(lambda (f3461 f3449 f3515 f3504)
  (lambda ((w (subr write ((x bool)) bool))
	   (r (subr read ((x bool)) bool)))
    (begin
      (if #t
	  f3515
	  (lambda (x) (begin (f3504 x) (f3515 x) (r x))))
      (if #t
	  f3461
	  (lambda (x) (begin (f3461 x) (f3504 x) (r x)))))))

(lambda (f)
  (lambda ((w (subr write ((x bool)) bool))
	   (r (subr read ((x bool)) bool)))
    (begin
      (if #t
	  (lambda (x) (begin (f x) (r x)))
	  r)
      (if #t
	  (lambda (x) (begin (f x) (w x)))
	  w))))

(plambda ((e1 effect) (e2 effect))
	 (lambda (f)
	   (lambda ((w (subr e1 ((x bool)) bool))
		    (r (subr e2 ((x bool)) bool)))
	     (if #t
		 (lambda (x) (begin (f x) (r x)))
		 (lambda (x) (begin (f x) (w x)))))))  

(let ((m (module (define-abstraction t type bool)
		 (define f (lambda (x) (up-t x))))))
  (if #t
      (with m f)
      (with m f)))

(with (module (define m (module (define-abstraction t type bool)
				(define f up-t))))
      (with m
	    (with m f)))

(let ((m (module (define-abstraction t type bool)
		 (define f up-t))))
  (with m (with m f)))

(with (module (define m (module (define-abstraction t type bool)
				(define f up-t))))
      (with m f))

(with (module (define-typed m
		(moduleof (abs t type)
			  (val f (subr (maxeff) ((x bool)) t)))
		(module (define-abstraction t type bool)
			(define f up-t))))
      (with m f))

(let ((mod (module (define m 
		     (module (define-abstraction t type bool)
			     (define f (up-t #t)))))))
  (let ((m1 (with mod m)))
    (with m1 f)))

(let ((m1 (with (module (define m 
			   (module (define-abstraction t type bool)
				   (define f (up-t #t)))))
		m)))
  (with m1 f))

(with (with (module (define m 
		      (module (define-abstraction t type bool)
			      (define f (up-t #t)))))
	     m)
      f)

(lambda ((f (select (module (define-description t (subr read () int)))
	      t)))
  (f))

(lambda ((f (select (with (module (define-description r read))
			  (module (define-description t (subr r () int))))
	      t)))
  (f))

(if #t
    (lambda ((x (select ((lambda ((x bool)) 
			   (module (define-abstraction t type int))) 
			 #t)
		  t)))
      x)
    (lambda ((x (select ((lambda ((x bool))
			   (module (define-abstraction t type int))) 
			 #t)
		  t)))
      x))

(if #t
    (lambda ((x (select ((lambda (x) 
			   (module (define-abstraction t type int))) 
			 #t)
		  t)))
      x)
    (lambda ((x (select ((lambda (x) 
			   (module (define-abstraction t type int))) 
			 #t)
		  t)))
      x))

(plambda ((e1 effect) (e2 effect))
	 (lambda (x1 x2)
	   (plambda ((f1 effect) (f2 effect))
		    (lambda ((y1 (subr f1 () bool)) (y2 (subr f2 () bool)))
		      (if #t 
			  (lambda () (begin (x1) (y1)))
			  (lambda () (begin (x2) (y2))))))))

(plambda ((e1 effect) (e2 effect))
	 (lambda ((y1 (subr e1 () bool)) x2)
	   (plambda ((f1 effect) (f2 effect))
		    (lambda (x1 (y2 (subr f2 () bool)))
		      (if #t 
			  (lambda () (begin (x1) (y1)))
			  (lambda () (begin (x2) (y2))))))))

(proj (plambda ((e1 effect) (e2 effect))
	       (lambda ((y1 (subr e1 () bool)) x2)
		 (plambda ((f1 effect) (f2 effect))
			  (lambda (x1 (y2 (subr f2 () bool)))
			    (if #t 
				(lambda () (begin (x1) (y1)))
				(lambda () (begin (x2) (y2))))))))
      write read)

((proj (plambda ((e1 effect) (e2 effect))
		(lambda ((y1 (subr e1 () bool)) x2)
		  (plambda ((f1 effect) (f2 effect))
			   (lambda (x1 (y2 (subr f2 () bool)))
			     (if #t 
				 (lambda () (begin (x1) (y1)))
				 (lambda () (begin (x2) (y2))))))))
       write read)
 (the (subr write () bool) (lambda () #t))
 (lambda () 3))

(proj ((proj (plambda ((e1 effect) (e2 effect))
		      (lambda ((y1 (subr e1 () bool)) x2)
			(plambda ((f1 effect) (f2 effect))
				 (lambda (x1 (y2 (subr f2 () bool)))
				   (if #t 
				       (lambda () (begin (x1) (y1)))
				       (lambda () (begin (x2) (y2))))))))
	     write read)
       (the (subr write () bool) (lambda () #t))
       (lambda () 3))
      read write)

(proj ((proj (plambda ((e1 effect) (e2 effect))
		      (lambda ((y1 (subr e1 () bool)) x2)
			(plambda ((f1 effect) (f2 effect))
				 (lambda (x1 (y2 (subr f2 () bool)))
				   (if #t 
				       (lambda () (begin (x1) (y1)))
				       (lambda () (begin (x2) (y2))))))))
	     write read)
       (the (subr write () bool) (lambda () #t))
       (lambda () 3))
      read read)

(with (module (define f (lambda (x) x)))
      (begin (f 1)
	     (f #t)))

(with (module (define f (lambda (x) x)))
      f)

(with (module (define-abstraction t type int)
	      (define f (lambda ((x t)) x)))
      (lambda (x)
	(f x)))

(let ((x (get (new (module (define f (lambda (x) x)))))))
  (with x
	(f 2)))

(letrec ((f (get (new (lambda () (g)))))
	 (g (lambda () 3)))
  (f))

(with (module (define-abstraction t type bool) (define x up-t))
      (lambda ((y (select (module (define-abstraction t type bool)
				  (define x up-t)) t)))
	y))

(+ (with fx 1) 2)

(with (module (define-abstraction t type bool) (define x (up-t #f)))
      (lambda ((y (select (module (define-abstraction t type bool) 
				  (define x (up-t #f))) 
		    t)))
	y))

(with (module (define-abstraction t type bool) (define x (up-t #f)))
      (lambda ((y (select (module (define-abstraction t type bool) 
				  (define x (up-t #f))) 
		    t)))
	(if #t x y)))

(with (load "tests.load.fx") f)

(if #t
    (load "tests.load.fx")
    (load "tests.load.fx"))

(with (load "tests.load.fx")
      (lambda ((w (select (load "tests.load.fx")
		    t)))
      (if (f #t)
	  (f w)
	  (up w))))

(with (load "tests.load.fx")
      (begin (f #f)
	     (f 0)
	     (f 3.2)))

(with (load "tests.load.fx")
      (begin (f #f)
	     (with (load "tests.load.fx")
		   (f 0))))

(with (load "tests.load.fx")
      (match (f 'u)
	     (`u (f 2))))

(with (load "tests.load.fx")
      (if (f #f)
	  (f 0)
	  (with (load "tests.load.fx")
		(match (f 'u)
		       (`u (f 2))))))

(lambda ((x unit))
  (if #t
      (the fx..unit x)
      (the fx..unit #u)))

(with (module (define x 1)
	      (define y (+ x 1))
	      (define-typed z int (+ y 1))
	      (define-typed w int (+ z y)))
      (if (not? (= w 5))
	  (error "weird")
	  w))

(cond ((= 1 2) (error "Major error"))
      (else 4))

(let ((m1 (module (define-typed m 
		    (moduleof (val x int))
		    (module (define x 3))))))
  (+ m1.m.x 2))

(and #t #t #f (error "Short circuit"))

[(plambda ((t type)) (lambda ((x t)) x)) int]

(if (sexp=? (unit->sexp (vector-fill! (make-vector 10 0) 1))
	    (unit->sexp #u))
    'fine
    (error "Major error in sexp=?"))

(match '1 (`1 3))

(with (load "tests.list.fx")
      (match '(1) (`(1) 3)))

(with (load "tests.list.fx")
      (match '(fx91 0) (`(fx91 0) 3)))

(with (load "tests.list.fx")
      (match '(1) (`(,x) x)))

(with (load "tests.list.fx")
      (match '(x) (`(,x) x)))

(with (load "tests.list.fx")
      (match '(x) (`(,(sym->sexp~ x)) x)))

(with (load "tests.list.fx")
      (match '(x) (`(,(sym->sexp~ x)) (sym=? x (symbol x)))))

(with (load "tests.list.fx")
      (match '(x) (`(x) 2)))

(with (load "tests.list.fx")
      (match '(1) (`(,(int->sexp~ x)) (+ x 1))))

(with (load "tests.list.fx")
      (match '(1 2) (`(,(int->sexp~ x) ,(int->sexp~ y)) (= (+ x y) 3))))

(with (load "tests.list.fx")
      (letrec ((add (lambda (s)
		      (match s
			     (`,(sym->sexp~ _) 0)
			     (`,(int->sexp~ x) x)
			     (`(,x ,y) (+ (add x) (add y)))))))
	(add '(1 ((2 s) 3)))))

(with (load "tests.list.fx")
      (if #t (match '(#u) (`(#u) #u)) #u))

(with (load "tests.list.fx")
      (let ((tail (lambda (l)
		    (match l
			   (`(,a ,@d) d)))))
	tail))

(lambda ((f (poly ((t type)) (subr pure ((x t)) t))))
  (let ((y (f 3)))
    (f #t))) 

(with (load "tests.list.fx")
      (let ((tail (lambda (l)
		    (match l
			   (`(,a ,@d) d)))))
	tail))

(+ (with (load "tests.list.fx")
	 (match '(1) (`(,(int->sexp~ x)) (+ x 1))))
   (with (load "tests.list.fx")
	 (match '(2) (`(,(int->sexp~ x)) (+ x 1)))))
