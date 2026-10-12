;;; NBODY -- the Jovian planets' orbits, stepped.
;;;
;;; From the Computer Language Benchmarks Game, via Sandmark
;;; (benchmarksgame/nbody.ml, Troestler Christophe), ported to FX-26.
;;; Steps (ours): 1000000. Answer: the energy after them, as `f64->string`
;;; writes it (the original prints it, and before, to 9 places).
;;;
;;; OCaml's records of mutable floats are one flat array of `f64`s here,
;;; seven to a body: x, y, z, vx, vy, vz, mass.

(define-type world (flatarrayof f64 @heap))
(define pi f64 3.141592653589793)
(define days-per-year f64 365.24)
(define n-bodies int 5)

(define* at (subr (read @heap) (world int int) f64)
  (lambda (w b f) (flatarray-ref w (+ (* b 7) f))))
(define* put (subr (write @heap) (world int int f64) unit)
  (lambda (w b f v) (flatarray-set! w (+ (* b 7) f) v)))

(define* body
  (subr (maxeff (write @heap) (read (globals put days-per-year pi)))
        (world int f64 f64 f64 f64 f64 f64 f64) unit)
  (lambda (w b x y z vx vy vz mass)
    (let ((solar-mass (f64* (f64* 4. pi) pi)))
      (begin (put w b 0 x) (put w b 1 y) (put w b 2 z)
             (put w b 3 (f64* vx days-per-year)) (put w b 4 (f64* vy days-per-year))
             (put w b 5 (f64* vz days-per-year)) (put w b 6 (f64* mass solar-mass))))))

(define* bodies
  (subr (maxeff (alloc @heap) (write @heap) (read (globals body put days-per-year pi))) () world)
  (lambda ()
    (let ((w (the world (make-flatarray (f64-flat) 35 0.))))
      (begin
        (body w 0 0. 0. 0. 0. 0. 0. (f64/ 1. 1.))
        (body w 1 4.84143144246472090e+00 -1.16032004402742839e+00 -1.03622044471123109e-01
              1.66007664274403694e-03 7.69901118419740425e-03 -6.90460016972063023e-05
              9.54791938424326609e-04)
        (body w 2 8.34336671824457987e+00 4.12479856412430479e+00 -4.03523417114321381e-01
              -2.76742510726862411e-03 4.99852801234917238e-03 2.30417297573763929e-05
              2.85885980666130812e-04)
        (body w 3 1.28943695621391310e+01 -1.51111514016986312e+01 -2.23307578892655734e-01
              2.96460137564761618e-03 2.37847173959480950e-03 -2.96589568540237556e-05
              4.36624404335156298e-05)
        (body w 4 1.53796971148509165e+01 -2.59193146099879641e+01 1.79258772950371181e-01
              2.68067772490389322e-03 1.62824170038242295e-03 -9.51592254519715870e-05
              5.15138902046611451e-05)
        ;; The sun's velocity is not scaled by days per year: it is 0.
        w))))

;; Body i against each body j > i.
(define* pairs (subr (maxeff (read @heap) (write @heap) spin (read (globals at put n-bodies))) (world f64 int int) unit)
  (lambda (w dt i j)
    (if (< j n-bodies)
        (let* ((dx (f64- (at w i 0) (at w j 0)))
               (dy (f64- (at w i 1) (at w j 1)))
               (dz (f64- (at w i 2) (at w j 2)))
               (dist2 (f64+ (f64+ (f64* dx dx) (f64* dy dy)) (f64* dz dz)))
               (mag (f64/ dt (f64* dist2 (f64-sqrt dist2))))
               (mj (f64* (at w j 6) mag))
               (mi (f64* (at w i 6) mag)))
          (begin
            (put w i 3 (f64- (at w i 3) (f64* dx mj)))
            (put w i 4 (f64- (at w i 4) (f64* dy mj)))
            (put w i 5 (f64- (at w i 5) (f64* dz mj)))
            (put w j 3 (f64+ (at w j 3) (f64* dx mi)))
            (put w j 4 (f64+ (at w j 4) (f64* dy mi)))
            (put w j 5 (f64+ (at w j 5) (f64* dz mi)))
            (pairs w dt i (+ j 1))))
        #u)))

(define* advance (subr (maxeff (read @heap) (write @heap) spin (read (globals at put n-bodies pairs))) (world f64 int) unit)
  (lambda (w dt i)
    (if (< i n-bodies)
        (begin (pairs w dt i (+ i 1)) (advance w dt (+ i 1)))
        (letrec ((moves (subr (maxeff (read @heap) (write @heap) spin (read (globals at put n-bodies))) (int) unit)
                   (lambda (i)
                     (if (< i n-bodies)
                         (begin (put w i 0 (f64+ (at w i 0) (f64* dt (at w i 3))))
                                (put w i 1 (f64+ (at w i 1) (f64* dt (at w i 4))))
                                (put w i 2 (f64+ (at w i 2) (f64* dt (at w i 5))))
                                (moves (+ i 1)))
                         #u))))
          (moves 0)))))

(define* potential (subr (maxeff (read @heap) spin (read (globals at n-bodies))) (world int int f64) f64)
  (lambda (w i j e)
    (if (< j n-bodies)
        (let* ((dx (f64- (at w i 0) (at w j 0)))
               (dy (f64- (at w i 1) (at w j 1)))
               (dz (f64- (at w i 2) (at w j 2)))
               (d (f64-sqrt (f64+ (f64+ (f64* dx dx) (f64* dy dy)) (f64* dz dz)))))
          (potential w i (+ j 1) (f64- e (f64/ (f64* (at w i 6) (at w j 6)) d))))
        e)))

(define* energy (subr (maxeff (read @heap) spin (read (globals at n-bodies potential))) (world int f64) f64)
  (lambda (w i e)
    (if (< i n-bodies)
        (let* ((vx (at w i 3)) (vy (at w i 4)) (vz (at w i 5))
               (k (f64* (f64* .5 (at w i 6)) (f64+ (f64+ (f64* vx vx) (f64* vy vy)) (f64* vz vz)))))
          (energy w (+ i 1) (potential w i (+ i 1) (f64+ e k))))
        e)))

;; The sun given the momentum that leaves the whole at rest.
(define* offset (subr (maxeff (read @heap) (write @heap) spin (read (globals at put n-bodies pi))) (world int f64 f64 f64) unit)
  (lambda (w i px py pz)
    (if (< i n-bodies)
        (offset w (+ i 1) (f64+ px (f64* (at w i 3) (at w i 6))) (f64+ py (f64* (at w i 4) (at w i 6)))
                (f64+ pz (f64* (at w i 5) (at w i 6))))
        (let ((solar-mass (f64* (f64* 4. pi) pi)))
          (begin (put w 0 3 (f64/ (f64-neg px) solar-mass)) (put w 0 4 (f64/ (f64-neg py) solar-mass))
                 (put w 0 5 (f64/ (f64-neg pz) solar-mass)))))))

(define* doit
  (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin
                (read (globals bodies body put at days-per-year pi n-bodies pairs advance potential energy offset)))
        (int) string)
  (lambda (n)
    (let ((w (bodies)))
      (letrec ((steps (subr (maxeff (read @heap) (write @heap) spin (read (globals advance at put n-bodies pairs)))
                            (int) unit)
                 (lambda (k) (if (= k 0) #u (begin (advance w .01 0) (steps (- k 1)))))))
        (begin (offset w 0 0. 0. 0.) (steps n) (f64->string (energy w 0 0.)))))))

(doit 1000000)
