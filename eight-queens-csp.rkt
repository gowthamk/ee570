(define (attacks? qi qj delta-rows)
  (or (= qi qj) (= (abs (- qi qj)) delta-rows)))

(define (list-of n f)
  (if (= n 0) '() (cons (f) (list-of (- n 1) f))))

(define (tabulate n f)
  (if (<= n 0) '() (append (tabulate (- n 1) f) 
                           (list (f (- n 1))))))

(define (for-each-pair f l)
  (unless (null? l)
    (let ((x (for-each-indexed (lambda (x2 i) 
            (f (first l) x2 (+ i 1))) (rest l))))
      (for-each-pair f (rest l)))))

(define (check-queens new-column old-columns)
  (for-each-indexed
    (lambda (old-column i)
      (when (attacks? new-column old-column (+ i 1))
        (fail)))
    old-columns))

(define (place-n-queens-by-backtracking n)
  (define (loop row columns)
    (if (= (length columns) n)
      columns
      (let* ((column (an-integer-between 0 (- n 1)))
            (x (place-queen row column)))
        (check-queens column columns)
        (loop (+ 1 row) (cons column columns)))))
  (loop 0 '()))

(define-structure domain-variable
                  domain
                  before-demons
                  after-demons)

(define (create-domain-variable domain)
  (when (null? domain) (fail))
  (make-domain-variable domain '() '()))

(define (attach-before-demon! demon x)
  (local-set-domain-variable-before-demons!
    x (cons demon (domain-variable-before-demons x)))
  (demon))

(define (attach-after-demon! demon x)
  (local-set-domain-variable-after-demons!
    x (cons demon (domain-variable-after-demons x)))
  (demon))

(define (restrict-domain! x domain)
  (when (null? domain) (fail))
  (when (< (length domain)
           (length (domain-variable-domain x)))
    (for-each (lambda (demon) (demon))
              (domain-variable-before-demons x))
    (local-set-domain-variable-domain! x domain)
    (for-each (lambda (demon) (demon))
              (domain-variable-after-demons x))))

(define (assert-unary-constraint-gfc! constraint x)
  (restrict-domain! x (remove-if-not 
                        (lambda (xe) (constraint xe)) 
                        (domain-variable-domain x))))

(define (assert-binary-constraint-gfc! constraint x y)
  (for-each
    (lambda (v)
      (attach-after-demon!
        (lambda ()
          (when (bound? x)
            (restrict-domain! y 
              (remove-if-not (lambda (ye) (constraint (binding x) ye)) 
                             (domain-variable-domain y))))
          (when (bound? y)
            (restrict-domain! x 
              (remove-if-not (lambda (xe) (constraint xe (binding y))) 
                             (domain-variable-domain x)))))
        v))
    (list x y)))

(define (assert-unary-constraint-ac! constraint x)
  (restrict-domain! x (remove-if-not 
                        (lambda (xe) (constraint xe)) 
                        (domain-variable-domain x))))

(define (assert-binary-constraint-ac! constraint x y)
  (attach-after-demon!
    (lambda ()
      (restrict-domain! y 
        (remove-if-not 
          (lambda (ye) 
            (some (lambda (xe) (constraint xe ye))
                  (domain-variable-domain x))) 
        (domain-variable-domain y))))
    x)
  (attach-after-demon!
    (lambda ()
      (restrict-domain! x
        (remove-if-not 
          (lambda (xe) 
            (some (lambda (ye) (constraint xe ye))
                  (domain-variable-domain y))) 
        (domain-variable-domain x))))
    y))

(define (place-n-queens-by-constraints n) 
  (define (attach-gui-demon var i) 
    (attach-after-demon! 
      (lambda () (when (bound? var) 
                   (place-queen i (binding var)))) 
     var))
  (let* ((domain (tabulate n (lambda (i) i)))
         (vars (list-of n (lambda () 
            (create-domain-variable domain))))
         ;; Add GUI helper as post-demon
         (x (for-each-indexed attach-gui-demon vars))
         ;; the only constraint is that they should not attack
         ;; each other
         (x (for-each-pair 
              (lambda (var1 var2 diff) 
                (assert-constraint!
                  (lambda (qa qb) (not (attacks? qa qb diff))) 
                  (list var1 var2))) 
              vars)))
    (csp-solution vars first)))
