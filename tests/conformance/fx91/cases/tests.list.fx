(module
 (define cons~ 
     (plambda ((t type) (u type) (e1 effect) (e2 effect))
	      (lambda ((x (listof u))
		       (s (subr e1 ((fst u) (rest (listof u))) t))
		       (f (subr e2 ((x (listof u))) t)))
		  (if (null? x)
			  (f x)
		      (s (car x) (cdr x))))))
 (define null~ 
     (plambda ((t type) (u type) (e1 effect) (e2 effect))
	      (lambda ((x (listof u))
		       (s (subr e1 () t))
		       (f (subr e2 ((x (listof u))) t)))
		  (if (null? x)
			  (s)
		      (f x))))))
