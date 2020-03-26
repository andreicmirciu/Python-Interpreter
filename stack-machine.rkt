#lang racket
;; Mirciu Andrei-Constantin 323CD
;; TEMA 1 PP
(require "opcodes.rkt")
(provide make-stack-machine)
(provide run-stack-machine)
(provide get-stack)
(provide get-varnames)
(provide get-consts)
(provide get-names)
(provide get-code)
(provide get-IC)
(provide empty-stack)
(provide make-stack)
(provide push)
(provide pop)
(provide top)

;; Am implementat iteratori folosind liste.
(define current car)

(define next cdr)

;; Am ales să reprezint stiva de execuție ca o listă.
(define empty-stack '())

(define (make-stack) empty-stack)

(define (push element stack)
  (cons element stack))

(define (top stack)
  (car stack))

(define (pop stack)
  (cdr stack))

;; Am ales să reprezint mașina stivă ca o listă alcătuită din cele 4 segmente de date,
;; un counter ca să știu la ce instrucțiune sunt și stiva de execuție.
(define (make-stack-machine stack co-varnames co-consts co-names co-code IC)
  (list co-varnames co-consts co-names co-code IC stack))

;; Funcțiile `get-varnames`, `get-consts`, `get-names`,
;; `get-code`, `get-stack`, `get-IC` primesc o mașină stivă și întorc
;; componenta respectivă.

;; ex:
;; > (get-varnames (make-stack-machine empty-stack 'dummy-co-varnames (hash) (hash) (list) 0))
;; 'dummy-co-varnames
(define (get-varnames stack-machine)
  (current stack-machine))

;; ex:
;; > (get-consts (make-stack-machine empty-stack (hash) 'dummy-co-consts (hash) (list) 0))
;; 'dummy-co-consts
(define (get-consts stack-machine)
  (current (next stack-machine)))

;; ex:
;; > (get-names (make-stack-machine empty-stack (hash) (hash) 'dummy-co-names (list) 0))
;; 'dummy-co-names
(define (get-names stack-machine)
  (current (next (next stack-machine))))

;; ex:
;; > (get-code (make-stack-machine empty-stack (hash) (hash) (hash) 'dummy-co-code 0))
;; dummy-co-code
(define (get-code stack-machine)
  (current (next (next (next stack-machine)))))

;; Întoarce stiva de execuție.
;; ex:
;; > (get-stack (make-stack-machine 'dummy-exec-stack (hash) (hash) (hash) (list) 0))
;; dummy-exec-stack
;; https://docs.racket-lang.org/reference/pairs.html#%28def._%28%28lib._racket%2Flist..rkt%29._append%2A%29%29
(define (get-stack stack-machine)
  (append* (next (next (next (next (next stack-machine)))))))

;; Întoarce instruction counterul.
;; ex:
;; > (get-code (make-stack-machine empty-stack (hash) (hash) (hash) (list) 0))
;; 0
(define (get-IC stack-machine)
  (current (next (next (next (next stack-machine))))))

(define symbols (list 'CO-VARNAMES 'CO-CONSTS 'CO-NAMES 'CO-CODE 'INSTRUCTION-COUNTER 'STACK))

;; Funcția get-symbol-index găsește index-ul simbolului în listă.
(define (get-symbol-index symbol)
  (let iter ((list-symbols symbols) (counter 0))
  (if (equal? (car list-symbols) symbol)
      counter
      (iter (cdr list-symbols) (add1 counter)))))

;; Funcția update-stack-machine întoarce o nouă mașină stivă,
;; înlocuind componenta corespondentă simbolului cu item-ul dat în parametri.
;; > (get-varnames (update-stack-machine "new-varnames" 'CO-VARNAMES stack-machine))
;; "new-varnames"
;; > (get-names (update-stack-machine "new-names" 'CO-NAMES stack-machine))
;; "new-names"
;; https://docs.racket-lang.org/reference/pairs.html#%28def._%28%28lib._racket%2Flist..rkt%29._list-set%29%29
(define (update-stack-machine item symbol stack-machine)
  (list-set stack-machine (get-symbol-index symbol) item))

;; Funcția push-exec-stack primește o mașină stivă și o valoare
;; și întoarce o nouă mașină, unde valoarea este pusă pe stiva de execuție
(define (push-exec-stack value stack-machine)
  (update-stack-machine (push value (get-stack stack-machine)) 'STACK stack-machine))

;;  Funcția pop-exec-stack primește o mașină stivă
;;  și întoarce o nouă mașină, aplicând pop pe stiva de execuție.
(define (pop-exec-stack stack-machine)
  (update-stack-machine (pop (get-stack stack-machine)) 'STACK stack-machine))

;; Am implementat tot subsetul de instrucțiuni folosite în co-code, mai puțin pe
;; cele pentru care era precizat că se pot omite (GET_ITER, SETUP_LOOP, POP_BLOCK).
;; Toate instrucțiunile primesc o mașină stivă și eventual un anumit indice,
;; returnând o nouă mașină stivă pe care s-a aplicat operația respectivă.
;; https://elf.cs.pub.ro/pp/19/teme/racket-pypp
;; https://docs.racket-lang.org/reference/hashtables.html#%28def._%28%28quote._~23~25kernel%29._hash-ref%29%29
;; https://docs.racket-lang.org/reference/hashtables.html#%28def._%28%28quote._~23~25kernel%29._hash-set%29%29
(define (POP_TOP stack-machine)
  (pop-exec-stack stack-machine))

(define (LOAD_CONST stack-machine const_i)
  (push-exec-stack (hash-ref (get-consts stack-machine) const_i) stack-machine))

(define (LOAD_GLOBAL stack-machine func_i)
  (push-exec-stack (hash-ref (get-names stack-machine) func_i) stack-machine))

(define (STORE_FAST stack-machine var_i)
  (pop-exec-stack (update-stack-machine (hash-set (get-varnames stack-machine) var_i (top (get-stack stack-machine))) 'CO-VARNAMES stack-machine)))
  
(define (LOAD_FAST stack-machine var_i)
  (push-exec-stack (hash-ref (get-varnames stack-machine) var_i) stack-machine))

(define (BINARY_MODULO stack-machine)
  (define TOS (top (get-stack stack-machine)))
  (define TOS1 (top (pop (get-stack stack-machine))))
  (define result (modulo TOS1 TOS))
  (update-stack-machine (push result (pop (pop (get-stack stack-machine)))) 'STACK stack-machine))

(define (BINARY_ADD stack-machine)
  (define TOS (top (get-stack stack-machine)))
  (define TOS1 (top (pop (get-stack stack-machine))))
  (define result (+ TOS1 TOS))
  (update-stack-machine (push result (pop (pop (get-stack stack-machine)))) 'STACK stack-machine))

(define (BINARY_SUBTRACT stack-machine)
  (define TOS (top (get-stack stack-machine)))
  (define TOS1 (top (pop (get-stack stack-machine))))
  (define result (- TOS1 TOS))
  (update-stack-machine (push result (pop (pop (get-stack stack-machine)))) 'STACK stack-machine))

(define (INPLACE_ADD stack-machine)
  (define TOS (top (get-stack stack-machine)))
  (define TOS1 (top (pop (get-stack stack-machine))))
  (define result (+ TOS1 TOS))
  (update-stack-machine (push result (pop (pop (get-stack stack-machine)))) 'STACK stack-machine))

(define (INPLACE_SUBTRACT stack-machine)
  (define TOS (top (get-stack stack-machine)))
  (define TOS1 (top (pop (get-stack stack-machine))))
  (define result (- TOS1 TOS))
  (update-stack-machine (push result (pop (pop (get-stack stack-machine)))) 'STACK stack-machine))

(define (INPLACE_MODULO stack-machine)
  (define TOS (top (get-stack stack-machine)))
  (define TOS1 (top (pop (get-stack stack-machine))))
  (define result (modulo TOS1 TOS))
  (update-stack-machine (push result (pop (pop (get-stack stack-machine)))) 'STACK stack-machine))

(define (JUMP_ABSOLUTE stack-machine target)
  (update-stack-machine (/ target 2) 'INSTRUCTION-COUNTER stack-machine))

(define (COMPARE_OP stack-machine i)
  (define TOS (top (get-stack stack-machine)))
  (define TOS1 (top (pop (get-stack stack-machine))))
  (define result ((get-cmpop i) TOS1 TOS))
  (update-stack-machine (push result (pop (pop (get-stack stack-machine)))) 'STACK stack-machine))

(define (POP_JUMP_IF_FALSE stack-machine target)
  (define TOS (top (get-stack stack-machine)))
    (if (equal? TOS #f)
        (pop-exec-stack (JUMP_ABSOLUTE stack-machine target))
        (pop-exec-stack stack-machine)))

(define (POP_JUMP_IF_TRUE stack-machine target)
  (define TOS (top (get-stack stack-machine)))
    (if (equal? TOS #t)
        (pop-exec-stack (JUMP_ABSOLUTE stack-machine target))
        (pop-exec-stack stack-machine)))

(define (FOR_ITER stack-machine delta)
  (define TOS (top (get-stack stack-machine))) 
        (if (null? TOS)
            (pop-exec-stack (JUMP_ABSOLUTE stack-machine (+ (* (get-IC stack-machine) 2) (+ delta 2))))
            (update-stack-machine (push (current TOS) (push (next TOS) (pop (get-stack stack-machine)))) 'STACK stack-machine)))

;; https://docs.racket-lang.org/reference/procedures.html#%28def._%28%28lib._racket%2Fprivate%2Fbase..rkt%29._apply%29%29
;; https://docs.racket-lang.org/reference/pairs.html#%28def._%28%28lib._racket%2Flist..rkt%29._take%29%29
;; https://docs.racket-lang.org/reference/pairs.html#%28def._%28%28lib._racket%2Flist..rkt%29._drop%29%29
(define (CALL_FUNCTION stack-machine argc)
  (let iter ((counter argc) (result '()) (stack (get-stack stack-machine)))
    (if (< counter 0)
          (update-stack-machine (push (apply (get-function (car (take result 1))) (drop result 1)) stack) 'STACK stack-machine)
        (iter (sub1 counter) (push (top stack) result) (pop stack)))))

(define (RETURN_VALUE stack-machine)
  stack-machine)

;; Funcția get-operation primește o pereche (alcătuită dintr-o instrucțiune și un indice)
;; și o mașină stivă, verificând ce operație trebuie executată.
(define (get-operation pair stack-machine)
  (cond
    ((equal? (car pair) 'POP_TOP) (POP_TOP stack-machine))
    ((equal? (car pair) 'LOAD_CONST) (LOAD_CONST stack-machine (cdr pair)))
    ((equal? (car pair) 'LOAD_GLOBAL) (LOAD_GLOBAL stack-machine (cdr pair)))
    ((equal? (car pair) 'STORE_FAST) (STORE_FAST stack-machine (cdr pair)))
    ((equal? (car pair) 'LOAD_FAST) (LOAD_FAST stack-machine (cdr pair))) 
    ((equal? (car pair) 'BINARY_MODULO) (BINARY_MODULO stack-machine))
    ((equal? (car pair) 'BINARY_ADD) (BINARY_ADD stack-machine))
    ((equal? (car pair) 'BINARY_SUBTRACT) (BINARY_SUBTRACT stack-machine))
    ((equal? (car pair) 'INPLACE_ADD) (INPLACE_ADD stack-machine))
    ((equal? (car pair) 'INPLACE_SUBTRACT) (INPLACE_SUBTRACT stack-machine))
    ((equal? (car pair) 'INPLACE_MODULO) (INPLACE_MODULO stack-machine))
    ((equal? (car pair) 'JUMP_ABSOLUTE) (JUMP_ABSOLUTE stack-machine (cdr pair)))
    ((equal? (car pair) 'COMPARE_OP) (COMPARE_OP stack-machine (cdr pair)))
    ((equal? (car pair) 'POP_JUMP_IF_FALSE) (POP_JUMP_IF_FALSE stack-machine (cdr pair)))
    ((equal? (car pair) 'POP_JUMP_IF_TRUE) (POP_JUMP_IF_TRUE stack-machine (cdr pair)))
    ((equal? (car pair) 'FOR_ITER) (FOR_ITER stack-machine (cdr pair)))
    ((equal? (car pair) 'CALL_FUNCTION) (CALL_FUNCTION stack-machine (cdr pair)))
    ((equal? (car pair) 'RETURN_VALUE) (RETURN_VALUE stack-machine))
    (else stack-machine)))

;; Funcția run-stack-machine execută operații pană epuizează co-code.
;; Funcția get-operation-pair extrage câte o pereche (ce conține o instrucțiune și un indice) 
;; din co-code, pereche ce va fi ulterior folosită de funcția get-operation.
;; https://docs.racket-lang.org/reference/pairs.html#%28def._%28%28quote._~23~25kernel%29._list-tail%29%29
(define (run-stack-machine stack-machine)
  (define (get-operation-pair)
    (let ((IC (get-IC stack-machine)) (co-code (get-code stack-machine)))
      (if (= IC 0)
          (car co-code)
          (car (list-tail co-code IC)))))
  (if (< (get-IC stack-machine) (length (get-code stack-machine)))
      (run-stack-machine (get-operation (get-operation-pair) (update-stack-machine (add1 (get-IC stack-machine)) 'INSTRUCTION-COUNTER stack-machine) ))
      stack-machine))
