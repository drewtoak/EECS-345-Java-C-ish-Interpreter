;Timothy Kuo, Andrew Hwang, Faraz Ahmed

(load "classParser.scm")

;interprets the file for Java/C like program
(define interpret
  (lambda (filename classname)
    (call/cc
     (lambda (return)
       (executeMain
        (initialClassState (parser filename) '(()()) (list (parser filename)) '() (string->symbol classname) (string->symbol classname))
        (list (parser filename)) (string->symbol classname) return (string->symbol classname) (string->symbol classname))))))


(define insertClass
  (lambda (name closure state)
    (M_insert name closure state)))

;checks if parent class exists
(define hasParentClass?
  (lambda (parsetree)
    (if (pair? (caddr parsetree))
        #t
        #f)))

;gets parent class
(define getParentClass
  (lambda (parsetree)
    (car (cdaddr parsetree))))

(define classBody cadddr)

(define getFieldState caddr)

(define classClosure
  (lambda (parsetree state full_expression throw class this)
    (if (hasParentClass? parsetree)
        (makeClassClosure
         (getParentClass parsetree)
         (functionState (classBody parsetree) (getMethodState (lookup (getParentClass parsetree) state this)) state class this)
         (fieldState (classBody parsetree) (getFieldState (lookup (getParentClass parsetree) state this)) state full_expression throw class this))
        (makeClassClosure
         '()
         (functionState (classBody parsetree) '(()()) state class this)
         (fieldState (classBody parsetree) '(()()) state full_expression throw class this)))))

(define makeClassClosure
  (lambda (parentClassName funcState fieldState)
    (cons parentClassName (cons funcState (cons fieldState '())))))

(define functionState
  (lambda (parsetree funcState state class this)
    (cond
      ((null? parsetree) funcState)
      ((list? (operator parsetree)) (functionState (restOfExpression parsetree) (functionState (operator parsetree) funcState state class this) state class this))
      ((or (eq? (operator parsetree) 'static-function) (eq? (operator parsetree) 'function))
       (funcInsert (funcName parsetree) (funcClosure (restOfFunc parsetree) class) funcState this))
      (else (functionState (restOfExpression parsetree) funcState state class this)))))

(define fieldState
  (lambda (parsetree field_state state full_expression throw class this)
    (cond
      ((null? parsetree) field_state)
      ((list? (operator parsetree)) (fieldState (restOfExpression parsetree) (fieldState (operator parsetree) field_state state full_expression throw class this) state full_expression throw class this))
      ((or (eq? (operator parsetree) 'static-function) (eq? (operator parsetree) 'function)) field_state)
      ((eq? (operator parsetree) 'var) (declare parsetree full_expression field_state throw class this))
      ((eq? (operator parsetree) '=) (assign parsetree full_expression field_state throw class this))
      (else (fieldState (restOfExpression parsetree) field_state state full_expression throw class this)))))

(define initialClassState
  (lambda (parsetree state full_expression throw class this)
    (cond
      ((null? parsetree) state)
      ((list? (operator parsetree)) (initialClassState (restOfExpression parsetree)
                                                       (initialClassState (operator parsetree) state full_expression throw class this) full_expression throw class this))
      ((eq? 'class (operator parsetree)) (insertClass (operand1 parsetree) (classClosure parsetree state full_expression throw (operand1 parsetree) this) state))
      (else (initialClassState (restOfExpression parsetree) state full_expression throw class this)))))

(define createNewInstance
  (lambda (className classClosure)
    (cons className (cons (boxValues (getAllValues (getFieldState classClosure))) '()))))

(define boxValues
  (lambda (values)
    (if (null? values)
        '()
        (append (boxValues (cdr values)) (cons (box (car values)) '())))))
    
;getClass for left hand side of dot expression
(define getClass
  (lambda (expression state this)
    (cond
      ((and (list? expression) (eq? 'new (operator expression))) (className expression))
      (else expression))))
     
;interprets the function inside its function environment
(define interpretFunc
  (lambda (funcBody funcEnv full_expression throw class this)
    (call/cc
     (lambda (return)
       (pop (M_state funcBody full_expression funcEnv return return return throw class this))))))

;executes the M_state function
(define executeMain
  (lambda (state full_expression classname return class this)
    (M_state (lookup 'main (getMethodState (lookup classname state this)) this)
             full_expression
             (push state) return return return '() (lookup class state this) this)))

(define getMethodState cadr)

;creates the initial/top-level state that contains global variables and functions with its values and closures respectively
(define initialState
  (lambda (parsetree state full_expression throw class this)
    (cond
      ((null? parsetree) state)
      ((list? (operator parsetree)) (initialState (restOfExpression parsetree)
                                                  (initialState (operator parsetree) state full_expression throw class this) full_expression throw class this))
      ((or (eq? (operator parsetree) 'static-function) (eq? (operator parsetree) 'function))
       (funcInsert (funcName parsetree) (funcClosure (restOfFunc parsetree) class) state this))
      ((eq? (operator parsetree) 'var) (M_declare parsetree full_expression state throw class this))
      ((eq? (operator parsetree) '=) (M_assign parsetree full_expression state throw class this))
      (else (initialState (restOfExpression parsetree) (initialState (currentExp parsetree) state full_expression throw class this) full_expression throw class this)))))


;determines the value of a mathematical expression, variables are allowed if they have already been declared and assigned
(define M_value
  (lambda (expression full_expression s throw class this)
    (cond
      ((number? expression) expression)
      ((and (atom? expression) (eq? 'null (lookupVar expression s full_expression throw class this))) (error "using before assigning"))
      ((atom? expression) (lookupVar expression s full_expression throw class this))
      ((eq? 'true expression) #t) ;if true and false are in a list it is (operator expression)
      ((eq? 'false expression) #f) ;if true and false are in a list it is (operator expression) otherwise, if it's a string its expression
      ((eq? 'dot (operator expression)) (dotlookup expression s full_expression throw class this))
      ((eq? (operator expression) 'funcall) (callFunc (funcName expression)
                                                      (getFuncEnv (getActualParams expression)
                                                                  (getFormalParams (funcName expression) s full_expression throw class this) 
                                                                  (push s) full_expression throw class this)
                                                      full_expression throw class this)) 
      ((eq? '+ (operator expression)) (+ (M_value (operand1 expression) full_expression s throw class this) (M_value (operand2 expression) full_expression s throw class this)))
      ((and (null? (checkOperand2 expression)) (eq? '- (operator expression))) (- 0 (M_value (operand1 expression) full_expression s throw class this))) 
      ((eq? '- (operator expression)) (- (M_value (operand1 expression) full_expression s throw class this) (M_value (operand2 expression) full_expression s throw class this)))
      ((eq? '* (operator expression)) (* (M_value (operand1 expression) full_expression s throw class this) (M_value (operand2 expression) full_expression s throw class this)))
      ((eq? '/ (operator expression)) (quotient (M_value (operand1 expression) full_expression s throw class this) (M_value (operand2 expression) full_expression s throw class this)))
      ((eq? '% (operator expression)) (remainder (M_value (operand1 expression) full_expression s throw class this) (M_value (operand2 expression) full_expression s throw class this)))
      ((eq? '== (operator expression)) (boolean (eq? (M_value (operand1 expression) full_expression s throw class this) (M_value (operand2 expression) full_expression s throw class this))))
      ((eq? '!= (operator expression)) (boolean (not (eq? (M_value (operand1 expression) full_expression s throw class this) (M_value (operand2 expression) full_expression s throw class this)))))
      ((eq? '< (operator expression)) (boolean (< (M_value (operand1 expression) full_expression s throw class this) (M_value (operand2 expression) full_expression s throw class this))))
      ((eq? '> (operator expression)) (boolean (> (M_value (operand1 expression) full_expression s throw class this) (M_value (operand2 expression) full_expression s throw class this))))
      ((eq? '<= (operator expression)) (boolean (<= (M_value (operand1 expression) full_expression s throw class this) (M_value (operand2 expression) full_expression s throw class this))))
      ((eq? '>= (operator expression)) (boolean (>= (M_value (operand1 expression) full_expression s throw class this) (M_value (operand2 expression) full_expression s throw class this))))
      ((eq? '&& (operator expression)) (boolean (myAnd (M_value (operand1 expression) full_expression s throw class this) (M_value (operand2 expression) full_expression s throw class this))))
      ((eq? '|| (operator expression)) (boolean (myOr (M_value (operand1 expression) full_expression s throw class this) (M_value (operand2 expression) full_expression s throw class this))))
      ((eq? '! (operator expression)) (boolean (myNot (M_value (operand1 expression) full_expression s throw class this))))
      ((eq? 'new (operator expression)) (createNewInstance (operand1 expression) (lookup (operand1 expression) s this))) ;TODO possible side effects
      ((eq? 'true (M_value expression full_expression s throw class this)) 'true)
      ((eq? 'false (M_value expression full_expression s throw class this)) 'false)
      (else (error 'unknown "unknown expression")))))


;returns the state after implementing the parse tree
(define M_state
  (lambda (parsetree full_expression state return break continue throw class this)
    (cond
      ((null? parsetree) state)
      ((list? (operator parsetree)) (M_state (nextOperation parsetree) full_expression (M_state (operator parsetree) full_expression state return break continue throw class this) return break continue throw class this))
      ((or (eq? (operator parsetree) 'function) (eq? (operator parsetree) 'static-function)) (funcInsert (funcName parsetree) (funcClosure (restOfFunc parsetree) class) state this))
      ((eq? (operator parsetree) 'funcall) (M_FuncState (funcName parsetree)
                                                        (getFuncEnv (getActualParams parsetree)
                                                                    (getFormalParams (funcName parsetree) state full_expression throw class this)
                                                                    (push state) full_expression throw class this)
                                                        full_expression throw class this))
      ((eq? (operator parsetree) 'while) (M_state_while (operand1 parsetree) full_expression (operand2 parsetree) state return throw class this))
      ((and (eq? (operator parsetree) 'try) (null? (finally_body parsetree))) (pop (M_try (try_body parsetree) (cons parsetree full_expression) (push state) return break continue throw)))
      ((eq? (operator parsetree) 'try) (pop (M_try_finally (try_body parsetree) (cons parsetree full_expression) (push state) return break continue throw class this)))
      ((eq? (operator parsetree) 'var) (M_declare parsetree full_expression state throw class this))
      ((and (singleState? state) (eq? (operator parsetree) 'continue)) (error "illegal continue"))
      ((eq? (operator parsetree) 'continue) (continue (pop state)))
      ((eq? (operator parsetree) 'begin) (pop (M_begin (restOfExpression parsetree) full_expression (cons (getFirstLayer state) (list state)) return break continue throw class this)))
      ((and (singleState? state) (eq? (operator parsetree) 'break)) (error "illegal break"))
      ((eq? (operator parsetree) 'break) (break (pop state)))
      ((and (eq? (operator parsetree) 'throw) (null? (catch_body (currentExp full_expression)))) (error "no catch"))
      ((and (pair? throw) (eq? (operator parsetree) 'throw)) ((currentThrow throw) (M_catch (currentExp full_expression) (restOfExpression full_expression) (M_insert 'random (M_value (operand1 parsetree) full_expression state throw) (push (pop state))) return break continue (restOfThrow throw))))
      ((eq? (operator parsetree) 'throw) (error "no where to throw"))
      ((eq? (operator parsetree) '=) (M_assign parsetree full_expression state throw class this))
      ((eq? (operator parsetree) 'returnState) (return (state_changer (M_return parsetree full_expression state throw class this) state)))
      ((eq? (operator parsetree) 'return) (return (M_return parsetree full_expression state throw class this)))
      ((and (eq? (operator parsetree) 'if) (ifelse? parsetree)) (M_state_if_else (operand1 parsetree) full_expression (operand2 parsetree) (else parsetree) state return break continue throw class this))
      ((eq? (operator parsetree) 'if) (M_state_if (operand1 parsetree) full_expression (operand2 parsetree) state return break continue throw class this))
      (else (M_value parsetree full_expression state throw class this)))))

;executes begin body
(define M_begin
  (lambda (expression full_expression state return break continue throw class this)
    (cond
      ((null? expression) state)
      ((eq? (type expression) 'var) (M_begin (restOfExpression expression) full_expression (M_declare (declareVar expression) full_expression state throw class this) return break continue throw class this)) 
      (else (M_begin (restOfExpression expression) full_expression (M_state (currentExp expression) full_expression state return break continue throw class this) return break continue throw class this)))))

;interprets the function body within the scope of the function environment
(define M_FuncState
  (lambda (name funcEnv full_expression throw class this)
    (cond
      ((not (list? name)) (interpretFunc (modified_body (body (lookupMethod name funcEnv full_expression throw (lookup (car this) funcEnv this) this))) funcEnv full_expression throw (lookup (car this) funcEnv this) this)) 
      ((eq? 'this (operand1 name)) (interpretFunc (modified_body (body (lookupMethod name funcEnv full_expression throw (lookup (car this) funcEnv this) this))) funcEnv full_expression throw (lookup (car this) funcEnv this) this))
      ((eq? 'super (operand1 name)) (interpretFunc (modified_body (body (lookupMethod name funcEnv full_expression throw class this))) funcEnv full_expression throw (lookup (car class) funcEnv this) this))
      ((list? (operand1 name)) (interpretFunc (modified_body (body (lookupMethod name funcEnv full_expression throw (lookup (newClassName name) funcEnv this) this))) funcEnv full_expression throw (lookup (newClassName name) funcEnv this) (createNewInstance (newClassName name) (lookup (newClassName name) funcEnv this)))) ;looking up class name new A().f()
      ((eq? (lookup (operand1 name) funcEnv this) 'undefined) (interpretFunc (modified_body (body (lookupMethod name funcEnv full_expression throw (lookup (car (lookupVar (operand1 name) funcEnv full_expression throw class this)) funcEnv this) this))) funcEnv full_expression throw (lookup (car (lookupVar (operand1 name) funcEnv full_expression throw class this)) funcEnv this) (lookupVar (operand1 name) funcEnv full_expression throw class this)))
      (else (interpretFunc (modified_body (body (lookupMethod name funcEnv full_expression throw (lookup (car (lookup (operand1 name) funcEnv this)) funcEnv this) this))) funcEnv full_expression throw (lookup (car (lookup (operand1 name) funcEnv this)) funcEnv this) (lookup (operand1 name) funcEnv this)))))) ;variable (a.f())

;M_return returns the value of the expression
(define M_return
  (lambda (expression full_expression state throw class this)
       (M_value (operand1 expression) full_expression state throw class this)))

;execute try body
(define M_try
  (lambda (expression full_expression state return break continue oldthrow class this)
    (call/cc
     (lambda (throw)
       (letrec ((loop (lambda (expression full_expression state return break continue throw class this)
                        (cond
                          ((null? expression) state)
                          (else (loop (restOfExpression expression) full_expression (M_state (operator expression) full_expression state return break continue throw class this) return break continue throw class this))))))
         (loop expression full_expression state return break continue (cons throw oldthrow) class this))))))

;execute try body if there is a finally body 
(define M_try_finally
  (lambda (expression full_expression state return break continue oldthrow class this)
    (call/cc
     (lambda (throw)
       (letrec ((loop (lambda (expression full_expression state return break continue throw class this)
                        (cond
                          ((null? expression) (M_finally (finally_body (currentExp full_expression)) full_expression (push (pop state)) return break continue throw class this))
                          (else (loop (restOfExpression expression) full_expression (M_state (currentExp expression) full_expression state return break continue throw class this) return break continue throw class this))))))
         (loop expression full_expression state return break continue (cons throw oldthrow) class this))))))

;execute catch body
(define M_catch
  (lambda (expression full_expression state return break continue throw class this)
    (letrec ((loop (lambda (catch_expression full_expression state return break continue throw class this)
              (cond
                ((and (null? catch_expression) (null? (finally_body expression))) state)
                ((null? catch_expression) (M_finally (finally_body expression) full_expression (push (pop state)) return break continue throw class this))
                (else (loop (restOfExpression catch_expression) full_expression (M_state (currentExp catch_expression) full_expression state return break continue throw class this) return break continue throw class this))))))
      (loop (catch_finally_body (catch_body expression)) full_expression (M_insert (exception (catch_body expression)) (lookup 'random (getFirstLayer state) this) (M_remove 'random state)) return break continue throw class this))))

;execute finally body
(define M_finally
  (lambda (expression full_expression state return break continue throw class this)
    (letrec ((loop (lambda (expression full_expression state return break continue throw class this)
                     (cond
                       ((null? expression) state)
                       (else (loop (restOfExpression expression) full_expression (M_state (currentExp expression) full_expression state return break continue throw class this) return break continue throw class this))))))
      (loop (restOfExpression expression) full_expression state return break continue throw class this))))

;M_state_while continually does the statement as long as the condition is true 
(define M_state_while
  (lambda (condition full_expression statement state return throw class this)
    (call/cc
     (lambda (break)
       (letrec ((loop (lambda (condition full_expression statement state return break throw class this)
                        (if (boolean2 (M_value condition full_expression state throw class this))
                               (loop condition full_expression statement (M_state_while_stmt statement full_expression state return break throw class this) return break throw class this)
                               state))))
         (loop condition full_expression statement state return break throw class this))))))

(define M_state_while_stmt
  (lambda (statement full_expression state return break throw class this)
    (call/cc
     (lambda (continue)
       (M_state statement full_expression state return break continue throw class this)))))

;M_state_if does the statement if the condition is true
(define M_state_if
  (lambda (condition full_expression statement state return break continue throw class this)
    (if (boolean2 (M_value condition full_expression state throw class this))
        (M_state statement full_expression state return break continue throw class this)
         state)))

;M_state_if_else operates an if or else statement
(define M_state_if_else
  (lambda (condition full_expression statement1 statement2 state return break continue throw class this)
    (cond
      ((boolean2 (M_value condition full_expression state throw class this)) (M_state statement1 full_expression state return break continue throw class this))
      (else (M_state statement2 full_expression state return break continue throw class this)))))
                                            
;M_declare is a variable declaration, if no value is given, it will give the value of the variable as 'null x = 5
(define M_declare
  (lambda (declaration full_expression s throw class this)
    (cond
      ((not (null? (checkOperand2 declaration))) (M_insert (operand1 declaration) (M_value (operand2 declaration) full_expression s throw class this) s))
      (else (M_insert (operand1 declaration) 'null s)))))

(define declare
  (lambda (declaration full_expression s throw class this)
    (cond
      ((not (null? (checkOperand2 declaration))) (insert (operand1 declaration) (M_value (operand2 declaration) full_expression s throw class this) s))
      (else (insert (operand1 declaration) 'null s)))))

;M_assign assigns a variable with a value, the variable has to be declared
(define M_assign
  (lambda (assign full_expression state throw class this)
    (cond
      ((null? state) state)
      ((and (not (list? (operand2 assign))) (or (eq? (M_value (operand2 assign) full_expression state throw class this) 'undefined) (eq? (lookupVar (operand1 assign) state full_expression throw class this) 'undefined))) (error 'unknown "variable not declared"))
      ((not (list? (operand2 assign))) (begin (set-box! (M_lookupVar (operand1 assign) state class this) (M_value (operand2 assign) full_expression state throw class this)) state))
      ((eq? (lookupVar (operand1 assign) state full_expression throw class this) 'undefined) (error "variable not declared"))
      ((eq? (operator (operand2 assign)) 'funcall)  (begin (set-box! (M_lookup (operand1 assign) state class this) (M_value (operand2 assign) full_expression state throw class this)) state))
      ((eq? (M_value (operand2 assign) full_expression state throw class this) 'undefined) (error "variable not declared"))
      (else (begin (set-box! (M_lookupVar (operand1 assign) state class this) (M_value (operand2 assign) full_expression state throw class this)) state)))))

(define assign
  (lambda (assign full_expression state throw class this)
    (insert (operand1 assign) (M_value (operand2 assign) full_expression state throw class this) (M_remove (operand1 assign) state))))

;M_insert inserts the variable and the value into the first layer of the state
(define M_insert
  (lambda (var value s)
    (cond
      ((singleState? s) (cons (cons var (getAllVar s)) (cons (cons (box value) (getAllValues s)) '())))
      (else (cons (M_insert var value (getFirstLayer s)) (otherLayers s))))))

(define insert
  (lambda (var value s)
    (if (singleState? s)
        (cons (cons var (getAllVar s)) (cons (cons value (getAllValues s)) '()))
        (cons (M_insert var value (getFirstLayer s)) (otherLayers s)))))

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

;M_lookup returns the box of the variable given from the state.
(define M_lookup
  (lambda (name state class this)
    (cond
      ((null? state) 'undefined)
      ((list? name) (M_dotlookup name state class this))
      ((singleState? state) (checkLayer name state))
      ((inFirstLayer? name (getFirstLayer state)) (checkLayer name (getFirstLayer state)))
      (else (M_lookup name (restOfLayers state) class this)))))

(define M_lookupVar
  (lambda (variable state class this)
    (cond
      ((null? state) 'undefined)
      ((list? variable) (M_dotlookup variable state class this))
      ((singleState? state) (checkLayer variable state))
      ((inFirstLayer? variable (getFirstLayer state)) (checkLayer variable (getFirstLayer state)))
      (else (M_lookupValue variable (getAllVar (getFieldState class)) (getAllValues this))))))

(define M_dotlookup
  (lambda (dotexpression state class this)
    (cond
      ((null? state) 'undefined)
      ((list? (operand1 dotexpression)) (M_lookupValue (operand2 dotexpression)
                                                     (getAllVar (getFieldState (lookup (newClassName dotexpression) state this)))
                                                     (getAllValues (createNewInstance (newClassName dotexpression) (lookup (newClassName dotexpression) state this)))))
      ((eq? (operand1 dotexpression) 'this) (M_lookupValue (operand2 dotexpression)
                                                         (getAllVar (getFieldState (lookup (car this) state this)))
                                                         (getAllValues this))) ;'this'
      ((eq? (operand1 dotexpression) 'super) (M_lookupValue (operand2 dotexpression)
                                                          (getAllVar (getFieldState (lookup (car class) state this)))
                                                          (getAllValues this))) ;super
      (else (M_lookupValue (operand2 dotexpression)
                         (getAllVar (getFieldState (lookup (car (lookup (operand1 dotexpression) state this)) state this)))
                         (getAllValues (lookup (operand1 dotexpression) state this))))))) ;variables

(define M_lookupValue
  (lambda (variable fieldNames fieldValues)
    (cond
      ((null? fieldNames) (error "variable does not exist"))
      ((eq? (car fieldNames) variable) (getFieldValue (length (cdr fieldNames)) fieldValues))
      (else (M_lookupValue variable (cdr fieldNames) fieldValues)))))

;lookup returns the value of the variable given from the state.
(define lookup
  (lambda (name state this)
    (cond
      ((null? state) 'undefined)
      ((list? name) (lookup (operand2 name) state this))
      ((singleState? state) (checkLayer-unbox name state))
      ((inFirstLayer? name (getFirstLayer state)) (checkLayer-unbox name (getFirstLayer state)))
      (else (lookup name (restOfLayers state) this)))))

(define lookupVar
  (lambda (variable state full_expression throw class this)
    (cond
      ((null? state) 'undefined)
      ((list? variable) (dotlookup variable state full_expression throw class this))
      ((singleState? state) (checkLayer-unbox variable state))
      ((inFirstLayer? variable (getFirstLayer state)) (checkLayer-unbox variable (getFirstLayer state)))
      (else (lookupValue variable (getAllVar (getFieldState class)) (getAllValues this))))))

(define lookupLH
  (lambda (variable state full_expression throw class this)
    (cond
      ((null? state) 'undefined)
      ((and (list? variable) (not (list? (operand1 variable)))) (lookupLH (operand1 variable) state full_expression throw class this))
      ((and (list? variable) (eq? (operator variable) 'funcall)) (dotlookup variable state full_expression throw class this))
      ((list? variable) (dotlookup (operand1 variable) state full_expression throw class this))
      ((eq? (lookup variable state this) 'undefined) (lookupValue variable (getAllVar (getFieldState class)) (getAllValues this)))
      (else (lookup variable state this)))))

(define lookupValue
  (lambda (variable fieldNames fieldValues)
    (cond
      ((null? fieldNames) (error "variable does not exist"))
      ((eq? (car fieldNames) variable) (unbox (getFieldValue (length (cdr fieldNames)) fieldValues)))
      (else (lookupValue variable (cdr fieldNames) fieldValues)))))

(define getFieldValue
  (lambda (index fieldValues)
    (if (zero? index)
        (car fieldValues)
        (getFieldValue (- index 1) (cdr fieldValues)))))

(define dotlookup
  (lambda (dotexpression state full_expression throw class this)
    (cond
      ((null? state) 'undefined)
      ((and (list? (operand1 dotexpression)) (eq? (operator dotexpression) 'funcall))
       (callFunc (funcName dotexpression)
                 (getFuncEnv (getActualParams dotexpression)
                             (getFormalParams (funcName dotexpression) state full_expression throw class (lookupLH (funcName dotexpression) state full_expression throw class this))
                             (push state) full_expression throw class (lookupLH (funcName dotexpression) state full_expression throw class this))
                 full_expression throw class (lookupLH (funcName dotexpression) state full_expression throw class this)))
      ((and (list? (operand1 dotexpression)) (eq? (operator (operand1 dotexpression)) 'new))
       (lookupValue (operand2 dotexpression)
                    (getAllVar (getFieldState (lookup (newClassName dotexpression) state this)))
                    (getAllValues (createNewInstance (newClassName dotexpression) (lookup (newClassName dotexpression) state this)))))
      ((list? (operand1 dotexpression))
       (lookupValue (operand2 dotexpression)
                    (getAllVar (getFieldState (lookup (car (lookupLH dotexpression state full_expression throw class this)) state this)))
                    (getAllValues (lookupLH dotexpression state full_expression throw class this))))
      ((eq? (operand1 dotexpression) 'this) (lookupValue (operand2 dotexpression)
                                                         (getAllVar (getFieldState (lookup (car this) state this)))
                                                         (getAllValues this))) ;'this'
      ((eq? (operand1 dotexpression) 'super) (lookupValue (operand2 dotexpression)
                                                          (getAllVar (getFieldState (lookup (car class) state this)))
                                                          (getAllValues this))) ;super
      (else (lookupValue (operand2 dotexpression)
                         (getAllVar (getFieldState (lookup (car (lookup (operand1 dotexpression) state this)) state this)))
                         (getAllValues (lookup (operand1 dotexpression) state this))))))) ;variables

(define lookupMethod
  (lambda (expression state full_expression throw class this)
    (cond
      ((null? state) 'undefined)
      ((not (list? expression)) (lookup expression (getMethodState (lookup (car this) state this)) this)) ; implied 'this'
      ((and (list? (operand1 expression)) (eq? (operator expression) 'funcall)) (dotlookup expression state full_expression throw class this))
      ((and (list? (operand1 expression)) (eq? (newClassName expression) 'new)) (lookup (operand2 expression) (getMethodState (lookup (newClassName expression) state this)) this)) ;'new'
      ((list? (operand1 expression)) (lookup (operand2 expression) (getMethodState (lookupLH (newClassName expression) state full_expression throw class this)) this))
      ((eq? (operand1 expression) 'this) (lookup (operand2 expression) (getMethodState (lookup (car this) state this)) this)) ;'this'
      ((eq? (operand1 expression) 'super) (lookup (operand2 expression) (getMethodState (lookup (car class) state this)) this)) ;super
      ((eq? (lookup (operand1 expression) state this) 'undefined) (lookup (operand2 expression) (getMethodState (lookup (car (lookupVar (operand1 expression) state full_expression throw class this)) state this)) this))
      (else (lookup (operand2 expression) (getMethodState (lookup (car (lookup (operand1 expression) state this)) state this)) this))))) ;variables

;abstractions

(define outerScope cadr)

(define className cadr)

(define funcName cadr)

(define getActualParams cddr)

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

(define funcName cadr)

(define restOfFunc cddr)

(define param car)

(define body cadr)

(define getFirstParam car)

(define restOfParams cdr)

;helper methods

;modifies the body so that 'return is changed to 'returnState 
(define modified_body
  (lambda (funcBody)
    (cond
      ((null? funcBody) '())
      ((list? (operator funcBody)) (cons (modified_body (currentExp funcBody)) (modified_body (restOfExpression funcBody))))
      ((eq? (operator funcBody) 'function) funcBody)
      ((eq? (operator funcBody) 'return) (cons 'returnState (restOfExpression funcBody)))
      (else (cons (currentExp funcBody) (modified_body (restOfExpression funcBody)))))))

;calls the function within its function environment and returns a value instead of a state
(define callFunc
  (lambda (name funcEnv full_expression throw class this)
    (cond
      ((not (list? name)) (interpretFunc (body (lookupMethod name funcEnv full_expression throw (lookup (car this) funcEnv this) this)) funcEnv full_expression throw (lookup (car this) funcEnv this) this)) 
      ((eq? 'this (operand1 name)) (interpretFunc (body (lookupMethod name funcEnv full_expression throw (lookup (car this) funcEnv this) this)) funcEnv full_expression throw (lookup (funcClass (lookupMethod name funcEnv full_expression throw (lookup (car this) funcEnv this) this)) funcEnv this) this))
      ((eq? 'super (operand1 name)) (interpretFunc (body (lookupMethod name funcEnv full_expression throw class this)) funcEnv full_expression throw (lookup (car class) funcEnv this) this))
      ((and (list? (operand1 name)) (eq? (operator (operand1 name)) 'new)) (interpretFunc (body (lookupMethod name funcEnv full_expression throw (lookup (newClassName name) funcEnv this) this)) funcEnv full_expression throw (lookup (newClassName name) funcEnv this) (createNewInstance (newClassName name) (lookup (newClassName name) funcEnv this)))) ;looking up class name new A().f()
      ((list? (operand1 name)) (interpretFunc (body (lookupMethod name funcEnv full_expression throw (lookup (car (lookupLH name funcEnv full_expression throw class this)) funcEnv this) this)) funcEnv full_expression throw (lookup (car (lookupLH name funcEnv full_expression throw class this)) funcEnv this) (lookupLH name funcEnv full_expression throw class this)))
      (else (interpretFunc (body (lookupMethod name funcEnv full_expression throw (lookup (car (lookup (operand1 name) funcEnv this)) funcEnv this) this)) funcEnv full_expression throw (lookup (car (lookup (operand1 name) funcEnv this)) funcEnv this) (lookup (operand1 name) funcEnv this)))))) ;variable (a.f())

(define newClassName cadadr)

;get the formal parameters of the function given
(define getFormalParams
  (lambda (name state full_expression throw class this)
    (car (lookupMethod name state full_expression throw class this))))

;called when it sees returnState -- changes the global variables of the state to return a state rather than a value
(define state_changer
  (lambda (getValue state)
    state))

;gets the function environment of the function when it is called that includes the initial/top-level state and its parameters 
(define getFuncEnv
  (lambda (actualParameters formalParameters state full_expression throw class this)
    (cond
      ((not (eq? (length actualParameters) (length formalParameters))) (error "Mismatched Parameters"))
      ((null? actualParameters) state)
      (else (getFuncEnv (restOfParams actualParameters) (restOfParams formalParameters)
                    (M_insert (getFirstParam formalParameters) (M_value (getFirstParam actualParameters) full_expression (outerScope state) throw class this) state)
                    full_expression throw class this)))))

;inserts the function name and its closure into the top-level state
(define funcInsert
  (lambda (name closure env this)
    (cond
      ((singleState? env) (cons (cons name (getAllVar env)) (cons (cons (box closure) (getAllValues env)) '())))
      (else (cons (cons (cons name (getAllVar (getFirstLayer env))) (cons (cons (box closure) (getAllValues (getFirstLayer env))) '())) (cons (restOfLayers env) '()))))))

;creates the function closure of the function that includes the parameters, body, and the empty state (for now)
(define funcClosure
  (lambda (function classname)
    (cons (param function) (cons (body function) (cons classname '())))))

(define funcClass caddr)

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

;checking if element is in the current layer of the state
(define checkLayer
  (lambda (name state)
    (cond
      ((null? (getAllVar state)) 'undefined)
      ((eq? name (getFirstVar state)) (getFirstValue state))
      (else (checkLayer name (restOfState state))))))

(define checkLayer-unbox
  (lambda (name state)
    (cond
      ((null? (getAllVar state)) 'undefined)
      ((eq? name (getFirstVar state)) (unbox (getFirstValue state)))
      (else (checkLayer-unbox name (restOfState state))))))

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
      ((box? x) #t)
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