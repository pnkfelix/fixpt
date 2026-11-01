;; A session's steps name its module's types and effects, as staged code
;; does through `with` (Heist's, `TODO.md` §211, 3): a type it describes,
;; an effect it defines, and a type it keeps abstract, which stays so.
(define-type api-type
  (moduleof (desc point (productof (x int) (y int)))
            (desc pair-of (dlambda ((a type)) (productof (l a) (r a))))
            (val origin point) (desc counted (maxeff spin (read @heap)))))
(define api (the api-type
  (module (define-type point (productof (x int) (y int)))
          (define-type (pair-of (a type)) (productof (l a) (r a)))
          (define origin point (product (x 3) (y 4)))
          (define-effect counted (maxeff spin (read @heap))))))
(define-type sealed-type (moduleof (abs t type) (val zero t) (val show (subr pure (t) int))))
(define sealed (the sealed-type
  (module (define-type t int) (define zero t 7) (define show (subr pure (t) int) (lambda (x) x)))))
(define s (sessionof api-type @heap) (make-session api))
(define k (sessionof sealed-type @heap) (make-session sealed))
(define said (subr pure (stage-failure) string)
  (lambda (why) (string-append "refused: " (extract why message))))
(define-effect sessioning
  (maxeff stage spin (read @heap) (write @heap) (read (globals s k said))))
(define in (subr sessioning ((sessionof api-type @heap) datum) string)
  (lambda (s code)
    (session-check s pure int code
      (c (tagcase c
           (expression p (int->string (p)))
           (definition d (tagcase (session-commit! s d (sum shadow #u))
                           (defined n (string-append "defined " n))
                           (failed why (string-append "not defined: " (extract why message)))))))
      (why (said why)))))
(define in-sealed (subr sessioning (datum) string)
  (lambda (code)
    (session-check k pure int code
      (c (tagcase c
           (expression p (int->string (p)))
           (definition d (tagcase (session-commit! k d (sum shadow #u))
                           (defined n (string-append "defined " n))
                           (failed why (string-append "not defined: " (extract why message)))))))
      (why (said why)))))
(define line (subr (io stdout) (string) unit)
  (lambda (s) (begin (write-out (string-append s "\n")) #u)))
(define main
  (subr (maxeff sessioning (io stdout) (read (globals in in-sealed line api))) () int)
  (lambda ()
    (begin
      (line (in s '(extract (the point origin) y)))
      (line (in s '(define g (subr pure (point) int) (lambda (q) (+ (extract q x) (extract q y))))))
      (line (in s '(g origin)))
      (line (in s '(extract (the (pair-of int) (product (l 1) (r 2))) r)))
      (line (in s '(define h (subr counted () int) (lambda () 5))))
      (line (in s '(h)))
      (line (in-sealed '(show zero)))
      (line (in-sealed '(define z t zero)))
      (line (in-sealed '(show z)))
      (line (in-sealed '(show (the t 5))))
      0)))
