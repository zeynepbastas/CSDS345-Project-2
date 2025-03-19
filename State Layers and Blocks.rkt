#lang racket
(define (extend-state state)
  "Adds a new layer to the state."
  (cons '() state))

(define (pop-state state)
  "Removes the top layer from the state."
  (cdr state))

;; Helper Functions for State Management
(define (lookup-variable var state)
  (cond
    [(null? state) (error "Variable not found")]
    [(assoc var (car state)) => cadr] ;; Found in top layer, return value
    [else (lookup-variable var (cdr state))])) ;; Check next layer

(define (update-variable var value state)
  (if (null? state)
      (error "Variable not found for update")
      (if (assoc var (car state))
          (cons (cons (list var value) (cdr (car state))) (cdr state)) ;; Update in this layer
          (cons (car state) (update-variable var value (cdr state)))))) ;; Check next layer

(define (add-variable var value state)
  (cons (cons (list var value) (car state)) (cdr state))) ;; Add to top layer

;; Block Handling
(define (enter-block state)
  (cons '() state)) ;; Push new empty layer

(define (exit-block state)
  (if (null? state)
      (error "Cannot exit from an empty state")
      (cdr state))) ;; Remove top layer

;; Statement Execution
(define (M_state stmt state)
  (match stmt
    [`(block ,stmts) (M_state-seq stmts (enter-block state))] ;; Handle blocks separately
    [`(define ,var ,val) (add-variable var (M_value val state) state)] ;; Variable definition
    [`(set! ,var ,val) (update-variable var (M_value val state) state)] ;; Variable update
    [_ (error "Unknown statement")]))

(define (M_state-seq stmts state)
  (if (null? stmts)
      (exit-block state) ;; End of block, remove top layer
      (M_state-seq (cdr stmts) (M_state (car stmts) state)))) ;; Process statements recursively

