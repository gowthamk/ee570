#lang racket

(require "./clause_rewrite.rkt")
(require "./set-ops.rkt")

;; Helpers
(define UNSAT 'unsat)

(define (panic str v) 
  (display v)
  (raise str))

(define (map l f)
  (if (null? l) '()
    (cons (f (first l)) (map (rest l) f))))

(define (foldl l acc f)
  (if (null? l) acc
    (foldl (rest l) (f (first l) acc) f)))

;; Clause predicates
(define (true-clause? c)
  (cond 
    ((and (= 1 (length c)) 
          (eq? (first c) #t)) #t)
    (else #f)))

(define (empty-clause? c)
  (cond 
    ((and (= 1 (length c)) 
          (eq? (first c) #f)) #t)
    (else #f)))

(define (unit-clause? clause)
  (cond ((and (= (length clause) 1) 
              (symbol? (first clause))) #t)
        ((and (= (length clause) 1)
              (list? (first clause))) 
          (case (first (first clause))
            ((not) #t)
            (else #f)))
        (else #f)))

;; Functions
(define (set-of-vars-in clauses)
  (foldl clauses '() (lambda (clause acc)
      (foldl clause acc (lambda (lit acc) 
        (cond 
          ((symbol? lit) (set-union (list lit) acc))
          ((or (eq? lit #t) (eq? lit #f)) acc)
          ((and (list? lit) (= (length lit) 2)) 
            (case (first lit)
              ((not) (if (symbol? (second lit))
                       (set-union (list (second lit)) acc)
                       acc))
              (else (panic "Not a literal" lit))))
          (else (panic "Not a literal" lit))))))))

(define (create-lem-clauses vars)
  (map vars (lambda (var)
      (list var (list 'not var)))))

(define (chose-variable clauses)
  (cond 
    ((null? clauses) (panic "No clauses!"))
    ((null? (first clauses)) (panic "Empty clause!"))
    ((symbol? (first (first clauses))) (first (first clauses)))
    ((list? (first (first clauses))) (second (first (first clauses))))
    (else (panic "Clause contains non-literal" clauses))))

(define (clause-to-cnf clause)
  (if (> (length clause) 1) 
      (cons 'or clause)
      (first clause)))

(define (to-cnf clauses) 
  (cons 'and (map clauses clause-to-cnf)))

(define  (clause-from-cnf cnf)
    (cond
      ((symbol? cnf) (list cnf))
      ((or (eq? cnf #t) (eq? cnf #f)) (list cnf))
      ((and (list? cnf) (not (null? cnf)))
        (case (first cnf)
          ((not) (list cnf))
          ((or) (rest cnf))
          (else (panic "Invalid CNF" cnf))))
      (else (panic "Invalid CNF" cnf))))

(define (from-cnf cnf)
  (cond 
    ((symbol? cnf) (list (clause-from-cnf cnf)))
    ((or (eq? cnf #t) (eq? cnf #f)) (list (list cnf)))
    ((and (list? cnf) (not (null? cnf)))
      (case (first cnf)
        ((and) (map (rest cnf) clause-from-cnf))
        (else (list (clause-from-cnf cnf)))))
    (else (panic "Invalid CNF" cnf))))

(define (apply-subst subst clauses)
  (let* ((var (first subst))
         (val (second subst)))
    (map clauses (lambda (clause)
      (map clause (lambda (lit) 
        (cond 
          ((symbol? lit) (if (eq? lit var) val lit))
          ((or (eq? lit #t) (eq? lit #f)) lit)
          ((and (list? lit) (= (length lit) 2)) 
            (case (first lit)
              ((not) (if (eq? (second lit) var) 
                       (list 'not val) 
                       lit))
              (else (panic "Not a literal" lit))))
          (else (panic "Not a literal" lit)))))))))

(define (calc-subst unit)
  (cond ((symbol? (first unit)) 
          (list (first unit) '#t))
        ((list? (first unit)) 
         (list (second (first unit)) '#f))))

(define (unit-clauses clauses)
  (foldl clauses '() 
         (lambda (clause acc) 
             (if (unit-clause? clause)
               (append acc (list clause))
               acc))))

(define (over-approx scs)
  (let* ((n-left (foldl scs 0 
                    (lambda (sc acc) 
                      (if (or (true-clause? sc) (empty-clause? sc))
                        (+ 1 acc) acc)))))
    (- (length scs) n-left)))

(define  (unit-propagate hcs)
  (let* ((units (unit-clauses hcs))
         (substs (foldl units '() 
            (lambda (unit acc) 
              (unify-binds acc (list (calc-subst unit))))))
         (hcs (foldl substs hcs 
            (lambda (subst acc) (apply-subst subst acc))))
         (vars1 (set-of-vars-in hcs))
         (cnf (boolean-simplify (to-cnf hcs)))
         (simple-hcs (from-cnf cnf))
         (vars2 (set-of-vars-in simple-hcs))
         (lem-clauses (create-lem-clauses (set-minus vars1 vars2)))
         )
    (cond ((eq? cnf #f) (raise UNSAT))
          ((eq? cnf #t) (list substs lem-clauses))
          (else (list substs (append simple-hcs lem-clauses))))))

(define (simplify-clauses substs scs)
  (let* ((scs (foldl substs scs 
            (lambda (subst acc) (apply-subst subst acc))))
         (sc-formulas (map scs clause-to-cnf))
         (simple-scs (map sc-formulas (lambda (scf) 
                (clause-from-cnf (boolean-simplify scf)))))
         (n-empty (foldl simple-scs 0 (lambda (sc acc) 
                     (if (empty-clause? sc) (+ 1 acc)
                       acc)))))
    (list n-empty simple-scs)))

(define (dpll clauses assmts)
  (let* ((x (unit-propagate clauses))
         (new-assmts (first x))
         (clauses (second x))
         (assmts (append assmts new-assmts)))
    (cond 
      ((null? clauses) assmts)
      (else (let* ((v (chose-variable clauses))
                   (clauses1 (cons (list v) clauses))
                   (clauses2 (cons (list (list 'not v)) clauses)))
              (with-handlers ([(lambda (v) (eq? v UNSAT)) 
                               (lambda (v) (dpll clauses2 assmts))])
                     (dpll clauses1 assmts)))))))

(define (dpll-minsat hcs scs assmts lb)
  (let* ((x (unit-propagate hcs))
         (new-assmts (first x))
         (hcs (second x))
         (assmts (append assmts new-assmts))
         (y (simplify-clauses assmts scs))
         (n-empty (first y))
         (scs (second y))
         (ub (lambda () (+ n-empty (over-approx scs)))))
    (cond 
      ((null? hcs) 
      ;; If hard constraints are satisfied, then propagate this
      ;; solution only if it is better
        (cond ((<= n-empty lb) (list '() lb)) 
               (else (list assmts n-empty))))
      ;; If all soft-constraints are UNSAT, then only consider
      ;; hard constraints.
      ((= n-empty (length scs)) (list (dpll hcs assmts) n-empty))
      ((<= (ub) lb) (list '() lb))
      (else (let* ((v (chose-variable hcs))
                   (hcs1 (cons (list v) hcs))
                   (hcs2 (cons (list (list 'not v)) hcs))
                   (modellb1 (with-handlers ([(lambda (v) (eq? v UNSAT)) 
                               (lambda (v) (list '() -1))])
                     (dpll-minsat hcs1 scs assmts lb)))
                   (model1 (first modellb1))
                   (lb1 (second modellb1))
                   ;; If 1st dpll-minsat succeeded, then surely lb1 > lb.
                   ;; If it can't better lb, then lb1 = lb
                   ;; If 1st dpll-minsat results in UNSAT, then lb1 = -1
                   (reallb1 (max lb lb1))
                   (modellb1 (list model1 reallb1))
                   (modellb2 (with-handlers ([(lambda (v) (eq? v UNSAT)) 
                               (lambda (v) (if (= lb1 -1) 
                             ;; Both branches are UNSAT. So UNSAT.
                                             (raise UNSAT)
                                             (modellb1)))])
                     (dpll-minsat hcs2 scs assmts reallb1)))
                   (lb2 (second modellb2)))
              (if (> lb2 reallb1) modellb2 modellb1))))))

(define (sat-solve hcs scs)
  (with-handlers ([(lambda (v) (eq? v UNSAT)) 
                   (lambda (v) (display "UNSAT\n"))])
    (let* ((x (dpll-minsat hcs scs '() 0))
           (model (first x))
           (n (second x)))
       (begin (display "SAT\n")
              (display "Max number of unsat soft-constraints : ")
              (display n)
              (display "\n")
              (display "Model:\n")
              (display model)))))
