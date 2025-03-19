#lang racket
;(require "simpleParser.rkt")

; Group Project 1: Simple Language Interpreter
; Emi Hutter-DeMarco, Zeynep Bastas, Shreyhan Lakhina

;**************************************************************************************************
; Abstractions and Helper Functions
;**************************************************************************************************

; Expression Evaluation Abstractions
; (op firstoperand secondoperand) -> (+ 5 10)
; since secondoperand isnt required, optionalsecondoperand is used to test if it exists (for example (- 10) is valid.)
(define operator car)
(define firstoperand cadr)
(define optionalsecondoperand cddr)
(define secondoperand caddr)

; if and while abstractions
; (if (condition) (stmt1) (stmt2))
; (if (conditiob) (stmt1))
(define condition cadr)
(define stmt1 caddr)
; elif exists to check if stmt2 exists
(define elif cdddr)
(define stmt2 cadddr)
; (while (condition) (loopbody)
(define loopbody cddr)

; m_state abstractions to see which statement we are currently processing
(define currentstatement car)
(define nextstatement cdr)

; the return value for our return statment
; (return returnvalue)
(define returnvalue cadr)

; the state is stored in the following form ((x y ...) (5 12 ...))
(define emptystate '(()()))
; list of all variables declared
(define variable-names car)
; first variable of the list of variables
(define firstvar caar)
; all other variables except first variable
(define restvar cdar)
; list of values associated to each variable
(define variable-values cadr)
; first value of the list of values, corresponding to the first variable
(define firstval caadr)
; rest of values from list of values
(define restval cdadr)

;ADDED
(define currentInnerStatement caar)
(define finally cadddr)
(define catch caddr)
(define catchvariable caaddr)
(define try cadr)
(define throw cadr)

;********************************************************************************************************************

; checks if a given input is an atom (not a list and not null)
(define atom?
  (lambda (a)
    (not (or (pair? a) (null? a)))))

; adds a variable binding to the state
(define addBinding
  (lambda (var value state)
    (list
     (cons var (variable-names state))
     (cons value (variable-values state)))))

; returns the current value of a variable in the state
(define checkBindingValue
  (lambda (var state)
    (cond
      ((null? (variable-names state)) (error 'badstmt "Variable never declared"))
      ((and (eq? (firstvar state) var) (eq? (firstval state) 'novalue)) (error 'badstmt "Variable never assigned"))
      ((eq? (firstvar state) var) (firstval state))
      (else (checkBindingValue var (list (restvar state) (restval state)))))))

; checks if a variable has been declared
(define checkBindingExists
  (lambda (var state)
    (cond
      ((null? (variable-names state)) #f)
      ((eq? (firstvar state) var) #t)
      (else (checkBindingExists var (list (restvar state) (restval state)))))))

; removes a variable from the state
(define removeBinding
  (lambda (var state)
    (cond
      ((null? (variable-names state)) emptystate)
      ((eq? (firstvar state) var) (list (restvar state) (restval state)))
      (else (list (list (firstvar state) (variable-names (removeBinding var (list (restvar state) (restval state))))) (list (firstval state) (variable-values (removeBinding var (list (restvar state) (restval state))))))))))

; updates the value of a variable in the state
(define updateBinding
  (lambda (var value state)
    (addBinding var value (removeBinding var state))))

;assign given variable a particular value

;creates a new layer for the state
(define inner_state
  (lambda (state)
    (list null null state)))
;pops the newest layer from the state
(define pop_inner_state
  (lambda (state)
    (if (null? (cddr state))
      (error 'error "Can't pop")
      (caddr state))))

;********************************************************************************************************************

; returns the value of an expression using the current state
(define M_value
  (lambda (expression state)
    (M_value-cps expression state (lambda (v) v))))
      
(define M_value-cps
  (lambda (expression state return)
    (cond
      ((number? expression) expression)
      ((atom? expression) (checkBindingValue expression state))
      ((eq? '+ (operator expression)) (M_value-cps (firstoperand expression) state (lambda (v1) (M_value-cps (secondoperand expression) state (lambda (v2) (return (+ v1 v2)))))))
      ((and (eq? '- (operator expression)) (null? (optionalsecondoperand expression))) (M_value-cps (firstoperand expression) state (lambda (v1) (M_value-cps (secondoperand expression) state (lambda (v2) (return (+ v1 v2)))))))
      ((eq? '- (operator expression)) (M_value-cps (firstoperand expression) state) (lambda (v) (return (- 0 v))))
      ((eq? '* (operator expression)) (M_value-cps (firstoperand expression) state (lambda (v1) (M_value-cps (secondoperand expression) state (lambda (v2) (return (* v1 v2)))))))
      ((eq? '/ (operator expression)) (M_value-cps (firstoperand expression) state (lambda (v1) (M_value-cps (secondoperand expression) state (lambda (v2) (return (quotient v1 v2)))))))
      ((eq? '% (operator expression)) (M_value-cps (firstoperand expression) state (lambda (v1) (M_value-cps (secondoperand expression) state (lambda (v2) (return (remainder v1 v2)))))))
      ; value could be boolean
      (else (M_boolean expression state)))))

; returns the value of a boolean using the current state
(define M_boolean
  (lambda (expression state)
    (M_bool-cps expression state (lambda (v) v))))

(define M_bool-cps
  (lambda (expression state return)
    (cond
      ((eq? expression 'true) #t)                                                                                     
      ((eq? expression 'false) #f)
      ((atom? expression) (checkBindingValue expression state))
      ((eq? '! (operator expression)) (M_bool-cps (firstoperand expression) state (lambda (v1) (return (not v1)))))
      ((eq? '&& (operator expression)) (M_bool-cps (firstoperand expression) state (lambda (v1) (M_bool-cps (secondoperand expression) state (lambda (v2) (return (and v1 v2)))))))
      ((eq? '|| (operator expression)) (M_bool-cps (firstoperand expression) state (lambda (v1) (M_bool-cps (secondoperand expression) state (lambda (v2) (return (or v1 v2)))))))
      ((eq? '== (operator expression)) (M_bool-cps (firstoperand expression) state (lambda (v1) (M_bool-cps (secondoperand expression) state (lambda (v2) (return (eq? v1 v2)))))))
      ((eq? '!= (operator expression)) (M_bool-cps (firstoperand expression) state (lambda (v1) (M_bool-cps (secondoperand expression) state (lambda (v2) (return (not (eq? v1 v2))))))))
      ((eq? '< (operator expression)) (M_bool-cps (firstoperand expression) state (lambda (v1) (M_bool-cps (secondoperand expression) state (lambda (v2) (return (< v1 v2)))))))
      ((eq? '> (operator expression)) (M_bool-cps (firstoperand expression) state (lambda (v1) (M_bool-cps (secondoperand expression) state (lambda (v2) (return (> v1 v2)))))))
      ((eq? '<= (operator expression)) (M_bool-cps (firstoperand expression) state (lambda (v1) (M_bool-cps (secondoperand expression) state (lambda (v2) (return (<= v1 v2)))))))
      ((eq? '>= (operator expression)) (M_bool-cps (firstoperand expression) state (lambda (v1) (M_bool-cps (secondoperand expression) state (lambda (v2) (return (>= v1 v2)))))))
      (else (error 'badop "Invalid Operator")))))

; checks for the 5 types of statements defined and branches accordingly
(define M_statement
  (lambda (stmt state return next break continue throw)
    (cond
      ((eq? 'var (operator stmt)) (M_declare stmt state))
      ((eq? '= (operator stmt)) (M_assign stmt state))
      ((eq? 'begin (operator stmt)))
      ((eq? 'if (operator stmt)) (M_if stmt state))
      ((eq? 'while (operator stmt)) (M_while stmt state))
      ((eq? 'break (operator stmt)))
      ((eq? 'continue (operator stmt)))
      ((eq? 'throw (operator stmt)))
      ((eq? 'catch (operator stmt)))
      ((eq? 'finally (operator stmt)))
      ((eq? 'return (operator stmt)) (M_return stmt state))
      (else (error 'badstmt "Invalid Statement")))))

;********************************************************************************************************************

; runs when a new variable is declared
(define M_declare
  (lambda (stmt state)
    (cond
      ; ensures variables arent re declared
      ((eq? (checkBindingExists (firstoperand stmt) state) #t) (error 'badstmt "Redeclaring a variable"))
      ; if variable declared with no value, mark it accordingly
      ((null? (optionalsecondoperand stmt)) (addBinding (firstoperand stmt) 'novalue state))
      ; otherwise add the value to the state too
      (else (addBinding (firstoperand stmt) (M_value (secondoperand stmt) state) state)))))

; runs when a variable is assigned a new value
(define M_assign
  (lambda (stmt state)
    (cond
      ; ensures variable is declared
      ((eq? (checkBindingExists (firstoperand stmt) state) #f) (error 'badstmt "Variable never declared"))
      ; ensures the variable is not assigned to a value that doesnt exist
      ((eq? (M_value (secondoperand stmt) state) 'novalue) (error 'badstmt "Variable never assigned"))
      ; otherwise update value as expected
      (else (updateBinding (firstoperand stmt) (M_value (secondoperand stmt) state) state)))))

; runs when an if statemnt is created
(define M_if
  (lambda (stmt state)
    ; if condition is true, run statment1
    (if (eq? (M_boolean (condition stmt) state) #t)
        (M_statement (stmt1 stmt) state)
        ; if conditon is false, and an else statement exists, run statement2
        (if (null? (elif stmt))
            state
            (M_statement (stmt2 stmt) state)))))

; runs when a while statement is created
(define M_while
  (lambda (stmt state)
    ; while conditon is true, run the loop body
     (if (eq? (M_boolean (condition stmt) state) #t)
         (M_while stmt (M_state (loopbody stmt) state))
         state)))

; runs when a return statement is issued
(define M_return
  (lambda (stmt state)
    (cond
      ; if the return statement is a number, return that number
      ((number? (M_value (returnvalue stmt) state)) (M_value (returnvalue stmt) state))
      ; if the return statement is a boolean, convert it to english true/false
      ((eq? (M_boolean (returnvalue stmt) state) #t) 'true)
      (else 'false))))

; runs the whole program by running statements line by line
(define M_state
  (lambda (tree state)
    (if (null? tree)
        state
        (M_state (nextstatement tree) (M_statement (currentstatement tree) state)))))

;********************************************************************************************************************

; runs the interpreter by providing a testfile to run
;(define interpret
;  (lambda (filename)
;    (M_state (parser filename) emptystate)))

