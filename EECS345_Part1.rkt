;Timothy Kuo, Andrew Hwang, Faraz Ahmed

(load "simpleParser.scm")

;interprets the file for Java/C like program
(define interpret
  (lambda (filename)
    (M_state (parser filename) '(() ()))))

;M_opera returns the value of the expression
(define M_expression
  (lambda (expression state)
    (cond
      ((or (eq? (operator expression) '*)
           (eq? (operator expression) '/)
           (eq? (operator expression) '+)
           (eq? (operator expression) '-)
           (eq? (operator expression) '%)
           (eq? (operator expression) '==)
           (eq? (operator expression) '>)
           (eq? (operator expression) '<)
           (eq? (operator expression) '<=)
           (eq? (operator expression) '>=)
           (eq? (operator expression) '!)
           (eq? (operator expression) '!=)
           (eq? (operator expression) '&&)
           (eq? (operator expression) '||)) (M_value expression state))
      ((eq? (operator expression) 'while) (M_state_while (operand1 expression) (operand2 expression)  state))
      ((eq? (operator expression) 'var) (M_declare expression state))
      ((eq? (operator expression) '=) (M_assign expression state))
      ((eq? (operator expression) 'return) (M_return expression state))
      ((and (eq? (operator expression) 'if) (ifelse? expression)) (M_state_if_else (operand1 expression) (operand2 expression) (else expression) state))
      ((eq? (operator expression) 'if) (M_state_if (operand1 expression) (operand2 expression) state))
      (else (error 'unknown "unknown operator")))))

;returns the state after implementing the parse tree
(define M_state
  (lambda (parsetree state)
    (cond
      ((null? parsetree) state)
      ((list? (car parsetree)) (M_state (cdr parsetree) (M_state (car parsetree) state)))
      (else (M_expression parsetree state)))))
                               
                                          
;M_return returns the value of the expression
(define M_return
  (lambda (expression state)
      (if (eq? (operator expression) 'return)
          (M_value (operand1 expression) state))))

;M_declare is a variable declaration, if no value is given, it will give the value of the variable as 'null x = 5
(define M_declare
  (lambda (declaration s)
    (cond
      ((or (eq? 'false (M_lookup (operand1 declaration) s))
           (eq? 'true (M_lookup (operand1 declaration) s))
           (number? (M_lookup (operand1 declaration) s)))
           (error 'unknown "variable already declared"))
      ((not (null? (checkOperand2 declaration))) (M_insert (operand1 declaration) (M_value (operand2 declaration) s) s))
      (else (M_insert (operand1 declaration) 'null s)))))

;check to see if operand2 exists, ex. (var x) and (var x 5)
(define checkOperand2 cddr)

;M_assign assigns a variable with a value, the variable has to be declared
(define M_assign
  (lambda (assign s)
     (if (or (eq? (M_lookup (operand2 assign) s) 'undefined) (eq? (M_lookup (operand1 assign) s) 'undefined))
        (error 'unknown "variable not declared")
        (M_insert (operand1 assign) (M_value (operand2 assign) s) (M_remove (operand1 assign) s)))))


;returns all the values in the state
(define getAllValues cadr)
;returns all the variables in the state
(define getAllVar car)

;M_insert inserts the variable and the value into the state
(define M_insert
  (lambda (var value s)
    (cons (cons var (getAllVar s)) (cons (cons value (getAllValues s)) '()))))

;M_remove removes the variable and its value from the state
(define M_remove
  (lambda (var s)
    (cond
      ((null? s) s)
      ((eq? (getFirstVar s) var) (restOfState s))
      (else (M_insert (getFirstVar s) (getFirstValue s) (M_remove var (restOfState s)))))))

;M_lookup returns the value of the variable given from the state
(define M_lookup
  (lambda (name state)
    (cond
      ((null? (car state)) 'undefined)
      ((list? name) (M_value name state))
      ((number? name) (M_value name state))
      ((eq? name (getFirstVar state)) (getFirstValue state))
      (else (M_lookup name (restOfState state))))))

;returns the first variable in the state
(define getFirstVar
  (lambda (s)
        (caar s)))

;returns the first value in the state
(define getFirstValue
  (lambda (s)
        (caadr s)))

;returns the rest of the state
(define restOfState
  (lambda (s)
    (cons (cdar s) (cons (cdadr s) '()))))

;an atom is not null, not a list, and not an operator
(define atom?
  (lambda (x)
    (cond
      ((eq? '- x) #f)
      ((eq? '+ x) #f)
      ((eq? '* x) #f)
      ((eq? '/ x) #f)
      ((eq? '% x) #f)
      ((eq? '== x) #f)
      ((eq? '!= x) #f)
      ((eq? '>= x) #f)
      ((eq? '<= x) #f)
      ((eq? '> x) #f)
      ((eq? '< x) #f)
      ((eq? '! x) #f)
      ((eq? '|| x) #f)
      ((eq? '&& x) #f)
      ((eq? '= x) #f)
      ((or (eq? 'false x) (eq? 'true x)) #f) 
      (else (and (not (number? x)) (not (null? x)) (not (pair? x)))))))

;determines the value of a mathematical expression, variables are allowed if they have already been declared and assigned
(define M_value
  (lambda (expression s)
    (cond
      ((number? expression) expression)
      ((atom? expression) (M_lookup expression s))
      ((eq? 'true expression) #t) 
      ((eq? 'false expression) #f) 
      ((eq? '+ (operator expression)) (+ (M_value (operand1 expression) s) (M_value (operand2 expression) s)))
      ((and (null? (checkOperand2 expression)) (eq? '- (operator expression))) (- 0 (M_value (operand1 expression) s))) 
      ((eq? '- (operator expression)) (- (M_value (operand1 expression) s) (M_value (operand2 expression) s)))
      ((eq? '* (operator expression)) (* (M_value (operand1 expression) s) (M_value (operand2 expression) s)))
      ((eq? '/ (operator expression)) (quotient (M_value (operand1 expression) s) (M_value (operand2 expression) s)))
      ((eq? '% (operator expression)) (remainder (M_value (operand1 expression) s) (M_value (operand2 expression) s)))
      ((eq? '== (operator expression)) (boolean (eq? (M_value (operand1 expression) s) (M_value (operand2 expression) s))))
      ((eq? '!= (operator expression)) (boolean (not (eq? (M_value (operand1 expression) s) (M_value (operand2 expression) s)))))
      ((eq? '< (operator expression)) (boolean (< (M_value (operand1 expression) s) (M_value (operand2 expression) s))))
      ((eq? '> (operator expression)) (boolean (> (M_value (operand1 expression) s) (M_value (operand2 expression) s))))
      ((eq? '<= (operator expression)) (boolean (<= (M_value (operand1 expression) s) (M_value (operand2 expression) s))))
      ((eq? '>= (operator expression)) (boolean (>= (M_value (operand1 expression) s) (M_value (operand2 expression) s))))
      ((eq? '&& (operator expression)) (boolean (myAnd (M_value (operand1 expression) s) (M_value (operand2 expression) s))))
      ((eq? '|| (operator expression)) (boolean (myOr (M_value (operand1 expression) s) (M_value (operand2 expression) s))))
      ((eq? '! (operator expression)) (boolean (myNot (M_value (operand1 expression) s))))
      ((eq? 'true (M_value expression s)) 'true)
      ((eq? 'false (M_value expression s)) 'false)
      (else (error 'unknown "unknown expression")))))

;operator in prefix notation
(define operator car)

;operand1 in prefix notation
(define operand1 cadr)

;operand2 in prefix notation
(define operand2 caddr)

;M_state_while continually does the statement as long as the condition is true 
(define M_state_while
  (lambda (condition statement state)
    (if (boolean2 (M_value condition state))
       (M_state_while condition statement (M_state statement state))
       state)))

;M_state_if does the statement if the condition is true
(define M_state_if
  (lambda (condition statement state)
    (if (boolean2 (M_value condition state))
        (M_state statement state)
        state)))

;M_state_if_else operates an if or else statement
(define M_state_if_else
  (lambda (condition statement1 statement2 state)
    (cond
      ((boolean2 (M_value condition state)) (M_state statement1 state))
      (else (M_state statement2 state)))))

;ifelse? determines if it is an if else statement
(define ifelse?
  (lambda (expression)
    (if (pair? (cdddr expression))
        #t
        #f)))

;the else operand
(define else cadddr)

;M_return returns the value of the expression
(define M_return
  (lambda (expression state)
    (if (eq? (operator expression) 'return)
        (M_value (operand1 expression) state))))

;returns the string version of #t and #f
(define boolean
  (lambda (expression)
    (if expression
        'true
        'false)))

;returns the # version of true and false
(define boolean2
  (lambda (expression)
    (if (eq? 'true expression)
        #t
        #f)))

;myAnd is a wrapper function for 'and and will return correctly whether the inputs are 'true, 'false, #t, or #f
(define myAnd
  (lambda (e1 e2)
    (cond
      ((and (eq? 'true e1) (eq? 'true e2)) #t)
      ((and (eq? #t e1) (eq? 'true e2)) #t)
      ((and (eq? 'true e1) (eq? #t e2)) #t)
      ((and (eq? #t e1) (eq? #t e2)) #t)
      (else #f))))

;myOr is a wrapper function for 'or and will return correctly whether the inputs are 'true, 'false, #t, or #f        
(define myOr
  (lambda (e1 e2)
    (cond
      ((and (eq? 'false e1) (eq? 'false e2)) #f)
      ((and (eq? #f e1) (eq? 'false e2)) #f)
      ((and (eq? 'false e1) (eq? #f e2)) #f)
      ((and (eq? #f e1) (eq? #f e2)) #f)
      (else #t))))

;myNot is a wrapper function for 'not and will return correctly whether the inputs are 'true, 'false, #t, or #f
(define myNot
  (lambda (e)
    (cond
      ((eq? 'false e) #t)
      ((eq? #f e) #t)
      ((eq? 'true e) #f)
      ((eq? #t e ) #f))))
                         