;; => 7
;; A template's procedure type with a specification: its parameters named,
;; one by the use and one by the template; `(ensures r …)`'s result named;
;; a call of a global procedure, the top level's, in a clause; a test's
;; `(bool …)` result's propositions as they are.
(define pos? (subr pure ((x : int)) bool (ensures r (or (not r) (< 0 x))))
  (lambda (x) (< 0 x)))
(define-syntax define-sum
  (-> (bvar bvar) defn)
  (syntax-rules ()
    ((_ name a)
     (define name (subr pure ((a : int) (b : int)) int
                    (requires (and (<= 0 b) (implies (pos? a) (<= 0 b))))
                    (ensures r (<= a r)))
       (lambda (x y) (+ x y))))))
(define-syntax define-int-test
  (-> (bvar) defn)
  (syntax-rules ()
    ((_ name) (define name (-> ((oneof int string)) (bool (then (shape 0 int)) (else))) int?))))
(define-sum add a)
(define-int-test int-test)
(if (int-test 1) (add 3 4) 0)
