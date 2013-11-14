(module p1 racket


(provide set-union)
(provide set-intersection)
(provide set-minus)

(define (foldl l acc f)
  (if (null? l) acc
    (let ((v (foldl (rest l) acc f)))
      (f (first l) v))))

(define (zip2 l1 l2) 
  (if (null? l1) '()
      (cons (cons (first l1) (cons (first l2) '())) 
            (zip2 (rest l1) (rest l2)))))
  
(define (fold2 l1 l2 acc f) 
  (foldl (zip2 l1 l2) acc (lambda (x1x2 acc) 
        (f (car x1x2) (cadr x1x2) acc))))

(define (exists needle l)
  (if (null? l) #f
    (if (eq? (first l) needle) #t
      (exists needle (rest l)))))
  
(define (set-union a b)
  (if (null? a)
    (if (null? b) null (set-union b null))
    (let* ((x (first a))
          (xs (set-union (rest a) b)))
      (if (exists x xs) xs
        (cons x xs)))))

(define (set-intersection a b)
  (if (null? a) null
    (let ((x (first a))
          (xs (set-intersection (rest a) b)))
      (if (exists x b)
        (set-union (cons x null) xs)
        xs))))

(define (set-minus a b)
  (if (null? a) null
    (foldl a null
      (lambda (x acc)
        (if (exists x b) acc
          (set-union (cons x null) acc))))))
)
