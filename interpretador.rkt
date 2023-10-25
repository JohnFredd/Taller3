#lang eopl

;; Hernan David Cisneros Vargas 2178192
;; John Freddy Belalcar Rojas 2182464
;; Julián David Rendon Cardona 2177387

;---------------------------------------------------------------------------------------
;---------------------------------------------------------------------------------------

;******************************************************************************************
;;;;; Interpretador para lenguaje con notación infija

;; La definición BNF para las expresiones del lenguaje:
;;
;;  <programa>          :=  <expresion>
;;                          un-programa (exp)
;;  <expresion>         :=  <numero>
;;                          numero-lit (num)
;;                      :=  "\""<texto> "\""
;;                          texto-lit (txt)
;;                      :=  <identificador>
;;                          var-exp (id)
;;                      := (<expresion> <primitiva-binaria> <expresion>)
;;                          primapp-bin-exp (exp1 prim-binaria exp2)
;;                      :=  <primitiva-unaria> (<expresion>)
;;                          primapp-un-exp (prim-unaria exp)
;;                      :=  Si <expresion> entonces <expresion>  sino <expresion> finSI
;;                          condicional-exp (test-exp true-exp false-exp)
;;                      :=  declarar (<identificador> = <expresion> (;)) { <expresion> }
;;                          variableLocal-exp (ids exps cuerpo)
;;                      :=  procedimiento (<identificador>*',') haga <expresion> finProc
;;                          procedimiento-ex (ids cuero)
;;                      :=  "evaluar" expresion  (expresion ",")*  finEval
;;                          app-exp(exp exps)
;;                      :=  recursivo  {identificador ({identificador}*(,)) = <expresion>}* haga <expresion> finRec
;;                          recursivo-exp (nombres-procedimientos idss cuerpos cuerpoRecursivo)
;;  <primitiva-binaria> :=  + (primitiva-suma)
;;                      :=  ~ (primitiva-resta)
;;                      :=  / (primitiva-div)
;;                      :=  * (primitiva-multi)
;;                      :=  concat (primitiva-concat)
;;  <primitiva-unaria>  :=  longitud (primitiva-longitud)
;;                      :=  add1 (primitiva-add1)
;;                      :=  sub1 (primitiva-sub1)
;;
;******************************************************************************************

;******************************************************************************************

(define scanner-spec-simple-interpreter
'((white-sp
   (whitespace) skip)
  (comment
   ("%" (arbno (not #\newline))) skip)
  (identificador
   ("@" letter (arbno (or letter digit "?"))) symbol)
  (numero
   (digit (arbno digit)) number)
  (numero
   ("-" digit (arbno digit)) number)
  (numero
   (digit (arbno digit) "." (arbno digit)) number)
  (numero
   ("-" digit (arbno digit) "." (arbno digit)) number)
  (texto
   ("\"" (arbno (not #\")) "\"") symbol)
  ))

;Especificación Sintáctica (gramática)

(define grammar-simple-interpreter
  '((programa (expresion) un-programa)
    (expresion (numero) numero-lit)
    (expresion (identificador) var-exp) 
    (expresion (texto) texto-lit)
    (expresion
     ("(" expresion primitiva-binaria expresion ")") primapp-bin-exp)
    (expresion
     (primitiva-unaria "(" expresion ")") primapp-un-exp)
    (expresion
     ("Si" expresion "entonces" expresion "sino" expresion "finSI") condicional-exp)
    (expresion
     ("declarar" "(" (separated-list identificador "=" expresion ";") ")" "{" expresion "}") variablelocal-exp)
    (expresion
     ("procedimiento" "(" (separated-list identificador ",") ")" "haga" expresion "finProc") procedimiento-ex)
    (expresion
     ("evaluar" expresion "(" ( separated-list expresion "," ) ")" "finEval") app-exp)
    (expresion
     ("recursivo" "{" (arbno identificador "(" (separated-list identificador ";") ")" "=" expresion) "}"  "haga" expresion "finRec") recursivo-exp)
    
    
    ;;;;;;

    (primitiva-binaria ("+") primitiva-suma)
    (primitiva-binaria ("-") primitiva-resta)
    (primitiva-binaria ("/") primitiva-div)
    (primitiva-binaria ("*") primitiva-multi)
    (primitiva-binaria ("concat") primitiva-concat)

    ;;;;;;
    
    ;;(primitiva-unaria ("longitud") primitiva-longitud)
    (primitiva-unaria ("add1") primitiva-add1)
    (primitiva-unaria ("sub1") primitiva-sub1)))

;Construidos automáticamente:

(sllgen:make-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)))

;*******************************************************************************************
;Parser, Scanner, Interfaz

;El FrontEnd (Análisis léxico (scanner) y sintáctico (parser) integrados)

(define scan&parse
  (sllgen:make-string-parser scanner-spec-simple-interpreter grammar-simple-interpreter))

;El Analizador Léxico (Scanner)

(define just-scan
  (sllgen:make-string-scanner scanner-spec-simple-interpreter grammar-simple-interpreter))


;El Interpretador (FrontEnd + Evaluación + señal para lectura )


(define interpretador
  (sllgen:make-rep-loop  "--> "
    (lambda (pgm) (eval-program  pgm)) 
    (sllgen:make-stream-parser 
      scanner-spec-simple-interpreter
      grammar-simple-interpreter)))


;*******************************************************************************************
;El Interprete

;eval-program: <programa> -> numero
; función que evalúa un programa teniendo en cuenta un ambiente dado (se inicializa dentro del programa)

(define eval-program
  (lambda (pgm)
    (cases programa pgm
      (un-programa (body)
                 (eval-expression body (init-env))))))




; Ambiente inicial
(define init-env
  (lambda ()
    (extend-env
     '(@a @b @c @d @e)
     '(1 2 3 "hola" "FLP")
     (empty-env))))

;(define init-env
;  (lambda ()
;     (empty-env)))


;eval-expression: <expression> <enviroment> -> numero
; evalua la expresión en el ambiente de entrada
(define eval-expression
  (lambda (exp env)
    (cases expresion exp
      (numero-lit (datum) datum)
      (var-exp (id) (buscar-variable env id))
      (texto-lit (txt) txt)
      (primapp-bin-exp (exp1 prim-binaria exp2)
                   (let ((args (eval-exps (list exp1 exp2) env)))
                     (aplicar-primitiva-bin prim-binaria args)))
      (primapp-un-exp (prim-unaria exp)
                   (let ((args (eval-exp exp env)))
                     (aplicar-primitiva-un prim-unaria args)))
      (condicional-exp (test-exp true-exp false-exp)
              (if (true-value? (eval-expression test-exp env))
                  (eval-expression true-exp env)
                  (eval-expression false-exp env)))
      (variablelocal-exp (ids exps cuerpo)
               (let ((args (eval-exps exps env)))
                 (eval-expression cuerpo
                                  (extend-env ids args env))))
      (procedimiento-ex (ids cuerpo)
                (cerradura ids cuerpo env))
      (app-exp (exp exps)
               (let ((procedimiento (eval-expression exp env))
                     (args (eval-exps exps env)))
                 (if (procVal? procedimiento)
                     (aplicar-procedimiento procedimiento args)
                     (eopl:error 'eval-expression
                                 "Attempt to apply non-procedure ~s" procedimiento))))
      (recursivo-exp (nombres-procedimientos idss cuerpos cuerpo-recursivo)
                  (eval-expression cuerpo-recursivo
                                   (extend-env-recursively nombres-procedimientos idss cuerpos env))))))
      



; funciones auxiliares para aplicar eval-expression a cada elemento de una 
; lista de operandos (expresiones)
(define eval-exps
  (lambda (exps env)
    (map (lambda (x) (eval-exp x env)) exps)))

(define eval-exp
  (lambda (exp env)
    (eval-expression exp env)))

;apply-primitive: <primitiva> <list-of-expression> -> numero
(define aplicar-primitiva-bin
  (lambda (prim-bin args)
    (cases primitiva-binaria prim-bin
      (primitiva-suma () (+ (car args) (cadr args)))
      (primitiva-resta () (- (car args) (cadr args)))
      (primitiva-multi () (* (car args) (cadr args)))
      (primitiva-div () (/ (car args) (cadr args)))
      (primitiva-concat () (string->symbol (string-append (substring (symbol->string (car args)) 0 (- (string-length (symbol->string (car args))) 1))
                                                          (substring (symbol->string (cadr args))  1 (string-length (symbol->string (cadr args)) )))))
      )))

(define aplicar-primitiva-un
  (lambda (prim-un args)
    (cases primitiva-unaria prim-un
      ;;(primitiva-longitud () (longitud (ambiente? (car args))))
      (primitiva-add1 () (+ (car args) 1))
      (primitiva-sub1 () (- (car args) 1)))))

;true-value?: determina si un valor dado corresponde a un valor booleano falso o verdadero
(define true-value?
  (lambda (x)
    (not (zero? x))))

;*******************************************************************************************
;Procedimientos
(define-datatype procVal procVal?
  (cerradura
   (lista-ID (list-of symbol?))
   (exp expresion?)
   (amb ambiente?)))

;apply-procedure: evalua el cuerpo de un procedimientos en el ambiente extendido correspondiente
(define aplicar-procedimiento
  (lambda (proc args)
    (cases procVal proc
      (cerradura (lista-ID exp amb)
               (eval-expression exp (extend-env lista-ID args amb))))))

;*******************************************************************************************
;Ambientes

;definición del tipo de dato ambiente
(define-datatype ambiente ambiente?
  (vacio)
  (extendido (syms (list-of symbol?))
                       (vals (list-of scheme-value?))
                       (env ambiente?))
  (recursively-extended-env-record (proc-names (list-of symbol?))
                                   (idss (list-of (list-of symbol?)))
                                   (bodies (list-of expresion?))
                                   (amb ambiente?)))

(define scheme-value? (lambda (v) #t))

;empty-env:      -> enviroment
;función que crea un ambiente vacío
(define empty-env  
  (lambda ()
    (vacio)))       ;llamado al constructor de ambiente vacío 


;extend-env: <list-of symbols> <list-of numbers> enviroment -> enviroment
;función que crea un ambiente extendido
(define extend-env
  (lambda (syms vals env)
    (extendido syms vals env)))

;extend-env-recursively: <list-of symbols> <list-of <list-of symbols>> <list-of expressions> environment -> environment
;función que crea un ambiente extendido para procedimientos recursivos
(define extend-env-recursively
  (lambda (proc-names idss bodies old-env)
    (recursively-extended-env-record
     proc-names idss bodies old-env)))


;función que busca un símbolo en un ambiente
(define buscar-variable
  (lambda (env sym)
    (cases ambiente env
      (vacio ()
             (eopl:error 'empty-env "No binding for ~s" sym))
      (extendido (syms vals old-env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (buscar-variable old-env sym))))
      (recursively-extended-env-record (proc-names idss bodies old-env)
                                       (let ((pos (list-find-position sym proc-names)))
                                         (if (number? pos)
                                             (cerradura (list-ref idss pos)
                                                      (list-ref bodies pos)
                                                      env)
                                             (buscar-variable old-env sym)))))))


;****************************************************************************************
;Funciones Auxiliares

; funciones auxiliares para encontrar la posición de un símbolo
; en la lista de símbolos de unambiente

(define list-find-position
  (lambda (sym los)
    (longitud (lambda (sym1) (eqv? sym1 sym)) los)))

(define longitud
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((longitud-r (longitud pred (cdr ls))))
              (if (number? longitud-r)
                (+ longitud-r 1)
                #f))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;  a)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;declarar (
;;      @radio=2.5;
;;      @areaCirculo= procedimiento (@radio) haga ((3.1416 * @radio) * @radio) finProc
;;     ) { 
;;         evaluar @areaCirculo (@radio) finEval  
;;       }