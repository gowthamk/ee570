(module p1 racket
 
(provide boolean-simplify)
(provide unify-binds)
  
(define (id x) x)

(define (panic str) 
  (display str)
  (raise str))

;;; Truth Model
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

(define (is-tautology tab)
  (foldl tab #t (lambda (row acc)
      (and (second row) acc))))
  
(define (truth-tables-match? prop1 prop2)
  (is-tautology (truth-table (list 'iff prop1 prop2))))
  
;;; Axiomatic  
(define (ensurelist l)
  (if (list? l) l (list l)))
  
(define (allprefsufs l) 
  (if (null? l) (list (list '() '()))
      (cons (list '() l)
            (map  (lambda (prefsuf) 
                   (list (cons (first l) (first prefsuf))
                         (second prefsuf)))
                  (allprefsufs (rest l))))))  

(define (pattern-variable? pattern) (memq pattern '(e e1 e2 e3)))

(define (pattern-list-variable? pattern) (memq pattern '(e... e1... e2... e3...)))

(define (lookup-pattern-variable pattern-variable bindings)
  (cond
    ((null? bindings) #f)
    ((eq? pattern-variable (first (first bindings)))
      (second (first bindings)))
    (else (lookup-pattern-variable
      pattern-variable (rest bindings)))))
  
(define (consistent? bind binds)
  (if (null? binds) #t
    (if (consistent? bind (rest binds))
         (let* ((headb (first binds))
                (propb (first headb))
                (assb (cadr headb))
                (prop (first bind))
                (ass (cadr bind)))
           (if (eq? prop propb)
             (if (eq? ass assb) #t #f)
             #t))
         #f)))
  
(define (unifiable? binds1 binds2) 
  (cond
    ((or (memq #f binds1) (memq #f binds2)) #f)
    ((or (null? binds1) (null? binds2)) #t)
    (else 
     (let* ((bind (first binds1)))
        (if (consistent? bind binds2)
            (unifiable? (rest binds1) binds2)
            #f)))))
  
(define (extend env binds) 
  (append env binds))
  
(define (emptyenv)
  '())
  
(define (collabmatch env splits pat1 pat2)
  (if (null? splits) (list #f)
      (let* ((split (first splits))
             (pre (first split))
             (suf (second split))
             (binds1 (match env pat1 pre))
             (binds2 (if (memq #f binds1) (list #f) 
                       (match (extend env binds1) pat2 suf)))
             (binds (lambda () 
                      (append binds1 binds2))))
        (cond 
          ((or (memq #f binds1) (memq #f binds2))
            (collabmatch env (rest splits) pat1 pat2))
           (else (binds))))))
  
(define (match env pattern expression)
  (cond
    ((pattern-variable? pattern) 
     (if (unifiable? env (list (list pattern expression)))
         (list (list pattern expression))
         (list #f)))
    ((pattern-list-variable? pattern) (list (list pattern expression)))
    ((and (list? pattern)
      (= (length pattern) 1)
      (pattern-list-variable? (first pattern)))
      (list (list (first pattern) expression)))
    ((and (list? pattern) (not (null? pattern)))
      (if (and (list? expression) (not (null? expression)))
          (if (pattern-list-variable? (first pattern))
              (let* ((prefsufs (allprefsufs expression))
                     (binds (collabmatch env prefsufs (first pattern) (rest pattern))))
                (if (memq #f binds) (list #f) binds))
              (let* ((binds1 (match env (first pattern) (first expression)))
                     (binds2 (if (memq #f binds1) (list #f) 
                               (match (extend env binds1)(rest pattern) 
                                 (rest expression))))
                     (binds (lambda () 
                      (append binds1 binds2))))
                (if (or (memq #f binds1) (memq #f binds2)) 
                    (list #f)
                    (binds))))
          (list #f)))
    ((equal? pattern expression) '())
    (else (list #f))))

(define (instantiate pattern bindings)
  (cond 
    ((pattern-variable? pattern)
     (lookup-pattern-variable pattern bindings))
    ((pattern-list-variable? pattern)
      (lookup-pattern-variable pattern bindings))
    ((and (list? pattern) (not (null? pattern)))
      (append (ensurelist (instantiate (first pattern) bindings))
      (instantiate (rest pattern) bindings)))
    (else pattern)))

(define (applicable? rule expression)
  (not (memq #f (match (emptyenv) (first rule) expression))))

(define (first-applicable-rule rules expression)
  (cond ((null? rules) #f)
    ((applicable? (first rules) expression) (first rules))
    (else (first-applicable-rule (rest rules) expression))))

(define (apply-rule rule expression)
  (let* ((binds (match (emptyenv) (first rule) expression))
         (newexp (instantiate (third rule) binds)))
    (id newexp)))

(define (apply-rules rules expression)
  (let ((rule (first-applicable-rule rules expression)))
    (if rule
        (let* ((newexp (apply-rule rule expression))
               (newexp1 (rewrite rules newexp)))
          (id newexp1))
        expression)))

(define (rewrite rules expression)
  (if (list? expression)
      (let* ((expr (map (lambda (expression) 
                         (rewrite rules expression))
                       expression))
            (simpexpr (apply-rules rules expr)))
        (id simpexpr))
      (id expression)))

(define *PropCalcRules*
 '(; not #t --> #f
   ((not #t)
    -~->
    #f)
   ; not #f --> #t
   ((not #f)
    -~->
    #t)
   ; double negation
   ((not (not e))
    -~->
    e)
   ; and
   (and
    -~->
    #t)
   ; and p
   ((and e)
    -~->
    e)
   ; and #t
   ((and e1... #t e2...)
    -~->
    (and e1... e2...))
   ; and #f
   ((and e1... #f e2...)
    -~->
    #f)
   ; nested and
   ((and e1... (and e2...) e3...)
    -~->
    (and e1... e2... e3...))
   ; duplicate props in and
   ((and e1... e e2... e e3...)
    -~->
    (and e1... e e2... e3...))
   ; contradictions in and - 1
   ((and e1... e e2... (not e) e3...)
    -~->
    #f)
   ; contradictions in and - 2
   ((and e1... (not e) e2... e e3...)
    -~->
    #f)
   ; or
   (or
    -~->
    #f)
   ; or P
   ((or e)
    -~->
    e)
   ; or #f
   ((or e1... #f e2...)
    -~->
    (or e1... e2...))
   ; or #t
   ((or e1... #t e2...)
    -~->
    #t)
   ; nested or
   ((or e1... (or e2...) e3...)
    -~->
    (or e1... e2... e3...))
   ; duplicate props in or
   ((or e1... e e2... e e3...)
    -~->
    (or e1... e e2... e3...))
   ; LEM - 1
   ((or e1... e e2... (not e) e3...)
    -~->
    #t)
   ; LEM - 2
   ((and e1... (not e) e2... e e3...)
    -~->
    #t)
   ))

(define (boolean-simplify pcexpr) 
  (rewrite *PropCalcRules* pcexpr))

)
