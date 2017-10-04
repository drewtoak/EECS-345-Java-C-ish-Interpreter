;Timothy Kuo, Andrew Hwang, Faraz Ahmed

(load "simpleParser.scm")

;interprets the file for Java/C like program
(define interpret
  (lambda (filename)
    (call/cc
     (lambda (return)
       (M_state (parser filename) (cons (parser filename) '()) '(() ()) return return return '())))))

;execute begin body
(define M_begin
  (lambda (expression full_expression state return break continue throw)
    (cond
      ((null? expression) state)
      ((eq? (type expression) 'var) (M_begin (restOfExpression expression) full_expression (M_declare (declareVar expression) state) return break continue throw)) 
      (else (M_begin (restOfExpression expression) full_expression (M_state (currentExp expression) full_expression state return break continue throw) return break continue throw)))))

;returns the state after implementing the parse tree
(define M_state
  (lambda (parsetree full_expression state return break continue throw)
    (cond
      ((null? parsetree) state)
      ((list? (operator parsetree)) (M_state (nextOperation parsetree) full_expression (M_state (operator parsetree) full_expression state return break continue throw) return break continue throw))
      ((eq? (operator parsetree) 'while) (M_state_while (operand1 parsetree) full_expression (operand2 parsetree) state return throw))
      ((and (eq? (operator parsetree) 'try) (null? (finally_body parsetree))) (pop (M_try (try_body parsetree) (cons parsetree full_expression) (push state) return break continue throw)))
      ((eq? (operator parsetree) 'try) (pop (M_try_finally (try_body parsetree) (cons parsetree full_expression) (push state) return break continue throw)))
      ((eq? (operator parsetree) 'var) (M_declare parsetree state))
      ((and (singleState? state) (eq? (operator parsetree) 'continue)) (error "illegal continue"))
      ((eq? (operator parsetree) 'continue) (continue (pop state)))
      ((eq? (operator parsetree) 'begin) (pop (M_begin (restOfExpression parsetree) full_expression (push state) return break continue throw)))
      ((and (singleState? state) (eq? (operator parsetree) 'break)) (error "illegal break"))
      ((eq? (operator parsetree) 'break) (break (pop state)))
      ((and (eq? (operator parsetree) 'throw) (null? (catch_body (currentExp full_expression)))) (error "no catch"))
      ((and (pair? throw) (eq? (operator parsetree) 'throw)) ((currentThrow throw) (M_catch (currentExp full_expression) (restOfExpression full_expression) (M_insert 'random (M_value (operand1 parsetree) state) (push (pop state))) return break continue (restOfThrow throw))))
      ((eq? (operator parsetree) 'throw) (error "no where to throw"))
      ((eq? (operator parsetree) '=) (M_assign parsetree state state))
      ((eq? (operator parsetree) 'return) (return (M_return parsetree state)))
      ((and (eq? (operator parsetree) 'if) (ifelse? parsetree)) (M_state_if_else (operand1 parsetree) full_expression (operand2 parsetree) (else parsetree) state return break continue throw))
      ((eq? (operator parsetree) 'if) (M_state_if (operand1 parsetree) full_expression (operand2 parsetree) state return break continue throw))
      (else (M_value parsetree state)))))

;M_return returns the value of the expression
(define M_return
  (lambda (expression state)
       (if (eq? (operator expression) 'return)
        (M_value (operand1 expression) state)))) 

;execute try body
(define M_try
  (lambda (expression full_expression state return break continue oldthrow)
    (call/cc
     (lambda (throw)
       (letrec ((loop (lambda (expression full_expression state return break continue throw)
                        (cond
                          ((null? expression) state)
                          (else (loop (restOfExpression expression) full_expression (M_state (operator expression) full_expression state return break continue throw) return break continue throw))))))
         (loop expression full_expression state return break continue (cons throw oldthrow)))))))

;execute try body if there is a finally body 
(define M_try_finally
  (lambda (expression full_expression state return break continue oldthrow)
    (call/cc
     (lambda (throw)
       (letrec ((loop (lambda (expression full_expression state return break continue throw)
                        (cond
                          ((null? expression) (M_finally (finally_body (currentExp full_expression)) full_expression (push (pop state)) return break continue throw))
                          (else (loop (restOfExpression expression) full_expression (M_state (currentExp expression) full_expression state return break continue throw) return break continue throw))))))
         (loop expression full_expression state return break continue (cons throw oldthrow)))))))

;execute catch body
(define M_catch
  (lambda (expression full_expression state return break continue throw)
    (letrec ((loop (lambda (catch_expression full_expression state return break continue throw)
              (cond
                ((and (null? catch_expression) (null? (finally_body expression))) state)
                ((null? catch_expression) (M_finally (finally_body expression) full_expression (push (pop state)) return break continue throw))
                (else (loop (restOfExpression catch_expression) full_expression (M_state (currentExp catch_expression) full_expression state return break continue throw) return break continue throw))))))
      (loop (catch_finally_body (catch_body expression)) full_expression (M_insert (exception (catch_body expression)) (M_lookup 'random (getFirstLayer state)) (M_remove 'random state)) return break continue throw))))

;execute finally body
(define M_finally
  (lambda (expression full_expression state return break continue throw)
    (letrec ((loop (lambda (expression full_expression state return break continue throw)
                     (cond
                       ((null? expression) state)
                       (else (loop (restOfExpression expression) full_expression (M_state (currentExp expression) full_expression state return break continue throw) return break continue throw))))))
      (loop (restOfExpression expression) full_expression state return break continue throw))))
                                            
;M_declare is a variable declaration, if no value is given, it will give the value of the variable as 'null x = 5
(define M_declare
  (lambda (declaration s)
    (cond
      ((or (eq? 'false (M_lookup (operand1 declaration) s))
           (eq? 'true (M_lookup (operand1 declaration) s))
           (number? (M_lookup (operand1 declaration) s)))
           (error (operand1 declaration) "variable already declared"))
      ((not (null? (checkOperand2 declaration))) (M_insert (operand1 declaration) (M_value (operand2 declaration) s) s))
      (else (M_insert (operand1 declaration) 'null s)))))

;M_assign assigns a variable with a value, the variable has to be declared
(define M_assign
  (lambda (assign s fullState)
    (cond
      ((null? s) s)
      ((singleState? s) (M_assign_single_state assign s fullState))
      ((inFirstLayer? (operand1 assign) (getFirstLayer s)) (cons (M_assign_single_state assign (getFirstLayer s) fullState) (list (restOfLayers s))))
      (else (cons (getFirstLayer s) (list (M_assign assign (restOfLayers s) fullState)))))))

(define M_assign_single_state
  (lambda (assign singleState fullState)
     (if (or (eq? (M_value (operand2 assign) fullState) 'undefined) (eq? (M_lookup (operand1 assign) fullState) 'undefined))
        (error 'unknown "variable not declared")
        (M_insert (operand1 assign) (M_value (operand2 assign) fullState) (M_remove (operand1 assign) singleState)))))

;M_insert inserts the variable and the value into the state
(define M_insert
  (lambda (var value s)
    (cond
      ((singleState? s) (cons (cons var (getAllVar s)) (cons (cons value (getAllValues s)) '())))
      (else (cons (M_insert var value (getFirstLayer s)) (otherLayers s))))))

;M_remove removes the variable and its value from the state
(define M_remove
  (lambda (var s)
    (cond
      ((null? s) s)
      ((singleState? s) (M_remove_single_state var s))
      ((inFirstLayer? var (getFirstLayer s)) (cons (M_remove_single_state var (getFirstLayer s)) (otherLayers s)))
      (else (cons (getFirstLayer s) (list (M_remove var (restOfLayers s))))))))

(define M_remove_single_state
  (lambda (var s)
    (cond
      ((null? s) s)
      ((eq? (getFirstVar s) var) (restOfState s))
      (else (M_insert (getFirstVar s) (getFirstValue s) (M_remove_single_state var (restOfState s)))))))

;M_lookup returns the value of the variable given from the state
(define M_lookup
  (lambda (name state)
    (cond
      ((null? state) 'undefined)
      ((singleState? state) (checkLayer name state))
      ((inFirstLayer? name (getFirstLayer state)) (checkLayer name (getFirstLayer state)))
      (else (M_lookup name (restOfLayers state))))))

;determines the value of a mathematical expression, variables are allowed if they have already been declared and assigned
(define M_value
  (lambda (expression s)
    (cond
      ((number? expression) expression)
      ((atom? expression) (M_lookup expression s))
      ((eq? 'true expression) #t) ;if true and false are in a list it is (operator expression)
      ((eq? 'false expression) #f) ;if true and false are in a list it is (operator expression) otherwise, if it's a string its expression
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

;M_state_while continually does the statement as long as the condition is true 
(define M_state_while
  (lambda (condition full_expression statement state return throw)
    (call/cc
     (lambda (break)
       (letrec ((loop (lambda (condition full_expression statement state return break throw)
                        (if (boolean2 (M_value condition state))
                               (loop condition full_expression statement (M_state_while_stmt statement full_expression state return break throw) return break throw)
                               state))))
         (loop condition full_expression statement state return break throw))))))

(define M_state_while_stmt
  (lambda (statement full_expression state return break throw)
    (call/cc
     (lambda (continue)
       (M_state statement full_expression state return break continue throw)))))

;M_state_if does the statement if the condition is true
(define M_state_if
  (lambda (condition full_expression statement state return break continue throw)
    (if (boolean2 (M_value condition state))
        (M_state statement full_expression state return break continue throw)
         state)))

;M_state_if_else operates an if or else statement
(define M_state_if_else
  (lambda (condition full_expression statement1 statement2 state return break continue throw)
    (cond
      ((boolean2 (M_value condition state)) (M_state statement1 full_expression state return break continue throw))
      (else (M_state statement2 full_expression state return break continue throw)))))

;abstractions

(define currentThrow car)

(define restOfThrow cdr)

(define catch_finally_body cddr)

(define checkOperand2 cddr)

(define getAllValues cadr)

(define getAllVar car)

(define otherLayers cdr)

(define getFirstLayer car)

(define pop cadr)

(define type caar)

(define restOfExpression cdr)

(define restOfLayers cadr)

(define declareVar car)

(define currentExp car)

(define try_body cadr)

(define finally_body cadddr)

(define exception caadr)  

(define nextOperation cdr)

(define catch_body caddr)

(define catch_finally_body cddr)

(define operator car)

(define operand1 cadr)

(define operand2 caddr)

(define else cadddr)

;helper methods

;adding new frame to state
(define push
  (lambda (state)
    (cons '(() ()) (list state))))

;checking if there is only one frame in the state
(define singleState?
  (lambda (state)
    (cond
      ((null? (cadr state)) #t)
      ((atom2? (caadr state)) #t)
      (else #f))))

;checking if element is in first layer of state
(define inFirstLayer?
  (lambda (name state)
    (cond
      ((null? (getAllVar state)) #f)
      ((eq? name (getFirstVar state)) #t)
      (else (inFirstLayer? name (restOfState state))))))

;checking if element is in layer of the state
(define checkLayer
  (lambda (name state)
    (cond
      ((null? (getAllVar state)) 'undefined)
      ((number? name) (M_value name state))
      ((eq? name (getFirstVar state)) (getFirstValue state))
      (else (checkLayer name (restOfState state))))))

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

;used for checking in singleState?
(define atom2?
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
      ((or (eq? 'false x) (eq? 'true x)) #t) 
      (else (and (not (null? x)) (not (pair? x)))))))

;ifelse? determines if it is an if else statement
(define ifelse?
  (lambda (expression)
    (if (pair? (cdddr expression))
        #t
        #f)))

;returns the string version of #t and #f
(define boolean
  (lambda (expression)
    (if expression
        'true
        'false)))

;returns the # version of true and false
(define boolean2
  (lambda (expression)
    (if (or (eq? 'true expression) (eq? #t expression))
        #t
        #f)))

(define myAnd
  (lambda (e1 e2)
    (cond
      ((and (eq? 'true e1) (eq? 'true e2)) #t)
      ((and (eq? #t e1) (eq? 'true e2)) #t)
      ((and (eq? 'true e1) (eq? #t e2)) #t)
      ((and (eq? #t e1) (eq? #t e2)) #t)
      (else #f))))
        
(define myOr
  (lambda (e1 e2)
    (cond
      ((and (eq? 'false e1) (eq? 'false e2)) #f)
      ((and (eq? #f e1) (eq? 'false e2)) #f)
      ((and (eq? 'false e1) (eq? #f e2)) #f)
      ((and (eq? #f e1) (eq? #f e2)) #f)
      (else #t))))

(define myNot
  (lambda (e)
    (cond
      ((eq? 'false e) #t)
      ((eq? #f e) #t)
      ((eq? 'true e) #f)
      ((eq? #t e ) #f))))