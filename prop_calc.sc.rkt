(module p1 racket

(define (panic str) (display str))

(define (assert flag)
  (if (eq? flag #t) 0
    (panic "assertion failed")))

(define (mymap l f)
  (if (null? l) '()
    (cons (f (first l)) (mymap (rest l) f))))

(define (foldl l acc f)
  (if (null? l) acc
    (let ((v (foldl (rest l) acc f)))
      (f (first l) v))))

(define (foldr l acc f)
  (if (null? l) acc
    (foldr (rest l) (f (first l) acc) f)))

(define (concat l1 l2)
  (foldr l1 l2 cons))

(define (bindeq? bind1 bind2)
  (let* ((prop1 (first bind1))
         (assert (symbol? prop1))
         (val1 (cadr bind1))
         (assert (boolean? val1))
         (prop2 (first bind2))
         (assert (symbol? prop2))
         (val2 (cadr bind2))
         (assert (boolean? val2)))
    (and (eq? prop1 prop2) (eq? val1 val2))))
  
(define (exists needle l)
  (if (null? l) #f
    (if (bindeq? (first l) needle) #t
      (exists needle (rest l)))))
  
(define (consistent bind binds)
  (if (null? binds) #t
    (if (consistent bind (rest binds))
         (let* ((headb (first binds))
                (propb (first headb))
                (assert (symbol? propb))
                (assb (cadr headb))
                (prop (first bind))
                (assert (symbol? prop))
                (ass (cadr bind)))
           (if (eq? prop propb)
             (if (eq? ass assb) #t #f)
             #t))
         #f)))

(define (unify-binds binds1 binds2)
  (if (null? binds1) binds2
    (let* ((bind (first binds1))
          (binds (unify-binds (rest binds1) binds2)))
       (if (null? binds) '() 
           (if (consistent bind binds) 
               (if (exists bind binds) binds (cons bind binds))
               '())))))
  
(define (unify-rows row1 row2 sem-fn)
  (let* ((binds1 (first row1))
         (val1 (cadr row1))
         (x (assert (boolean? val1)))
         (binds2 (first row2))
         (val2 (cadr row2))
         (x (assert (boolean? val2)))
         (binds (if (null? binds1) binds2 
                    (if (null? binds2) binds1 
                        (unify-binds binds1 binds2))))
         (val (sem-fn val1 val2)))
    (if (null? binds) '()
        (cons binds (cons val '())))))
  
(define (unify-tables tab1 tab2 sem-fn)
  (let* ((tabtab (mymap tab1
           (lambda (row1) 
             (foldl tab2 '() 
                (lambda (row2 rows) 
                  (let* ((row (unify-rows row1 row2 sem-fn)))
                    (if (null? row) rows
                        (cons row rows))))))))
         (tab (foldl tabtab '() 
            (lambda (subtab rows) 
              (concat subtab rows)))))
    tab))
  
(define (truth-table prop) 
  (cond
    ((symbol? prop)
      (let* ((binds1 (cons (cons prop '(#t)) '()))
             (row1 (cons binds1 '(#t)))
             (binds2 (cons (cons prop '(#f)) '()))
             (row2 (cons binds2 '(#f))))
        (cons row1 (cons row2 '()))))
    ((and (list? prop) (not (null? prop))) 
      (case (first prop) 
        ((not) 
          (let* ((x (assert (= (length (rest prop)) 1)))
                 (tab (truth-table (cadr prop))))
            (mymap tab (lambda (row) 
                       (cons (first row) (cons (not (cadr row)) '()))))))
        ((and)
           (let* ((props (rest prop))
                  (x (assert (> (length props) 1)))
                  (tables (mymap props truth-table))
                  (sem-fn (lambda (x y) (and x y)))) 
             (foldl (rest tables) (first tables) 
                    (lambda (tab acc) 
                      (unify-tables acc tab sem-fn)))))
        ((or)
           (let* ((props (rest prop))
                  (x (assert (> (length props) 1)))
                  (tables (mymap props truth-table))
                  (sem-fn (lambda (x y) (or x y)))) 
             (foldl (rest tables) (first tables) 
                    (lambda (tab acc) 
                      (unify-tables acc tab sem-fn)))))
        ((iff)
           (let* ((props (rest prop))
                  (x (assert (> (length props) 1)))
                  (tables (mymap props truth-table))
                  (sem-fn (lambda (x y) (eq? x y)))) 
             (foldl (rest tables) (first tables) 
                    (lambda (tab acc) 
                      (unify-tables acc tab sem-fn)))))))
    ((eq? prop '#t) (cons (cons '() (cons #t '())) '()))
    ((eq? prop '#f) (cons (cons '() (cons #f '())) '()))
    (else (panic "Invalid proposition - empty"))))
  
)