(define-syntax r-cond
  (syntax-rules (else =>)
    ((r-cond (else result1 result2 ...)) (begin result1 result2 ...))
    ((r-cond (test => result)) (let ((temp test)) (if temp (result temp))))
    ((r-cond (test => result) clause1 clause2 ...)
     (let ((temp test)) (if temp (result temp) (r-cond clause1 clause2 ...))))
    ((r-cond (test)) test)
    ((r-cond (test) clause1 clause2 ...)
     (let ((temp test)) (if temp temp (r-cond clause1 clause2 ...))))
    ((r-cond (test result1 result2 ...)) (if test (begin result1 result2 ...)))
    ((r-cond (test result1 result2 ...) clause1 clause2 ...)
     (if test (begin result1 result2 ...) (r-cond clause1 clause2 ...)))))

(define-syntax r-case
  (syntax-rules (else =>)
    ((r-case (key ...) clauses ...) (let ((atom-key (key ...))) (r-case atom-key clauses ...)))
    ((r-case key (else => result)) (result key))
    ((r-case key (else result1 result2 ...)) (begin result1 result2 ...))
    ((r-case key ((atoms ...) => result)) (if (memv key '(atoms ...)) (result key)))
    ((r-case key ((atoms ...) => result) clause clauses ...)
     (if (memv key '(atoms ...)) (result key) (r-case key clause clauses ...)))
    ((r-case key ((atoms ...) result1 result2 ...)) (if (memv key '(atoms ...)) (begin result1 result2 ...)))
    ((r-case key ((atoms ...) result1 result2 ...) clause clauses ...)
     (if (memv key '(atoms ...)) (begin result1 result2 ...) (r-case key clause clauses ...)))))

(define-syntax r-and
  (syntax-rules () ((r-and) #t) ((r-and test) test) ((r-and test1 test2 ...) (if test1 (r-and test2 ...) #f))))

(define-syntax r-or
  (syntax-rules () ((r-or) #f) ((r-or test) test)
    ((r-or test1 test2 ...) (let ((x test1)) (if x x (r-or test2 ...))))))

(define-syntax r-let
  (syntax-rules ()
    ((r-let ((name val) ...) body1 body2 ...) ((lambda (name ...) body1 body2 ...) val ...))
    ((r-let tag ((name val) ...) body1 body2 ...)
     ((letrec ((tag (lambda (name ...) body1 body2 ...))) tag) val ...))))

(define-syntax r-let*
  (syntax-rules ()
    ((r-let* () body1 body2 ...) (let () body1 body2 ...))
    ((r-let* ((name1 val1) (name2 val2) ...) body1 body2 ...)
     (let ((name1 val1)) (r-let* ((name2 val2) ...) body1 body2 ...)))))

(define-syntax r-do
  (syntax-rules ()
    ((r-do ((var init step ...) ...) (test expr ...) command ...)
     (letrec ((loop (lambda (var ...)
                      (if test
                          (begin (if #f #f) expr ...)
                          (begin command ... (loop (r-do "step" var step ...) ...))))))
       (loop init ...)))
    ((r-do "step" x) x)
    ((r-do "step" x y) y)))
