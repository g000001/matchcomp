;;; Copyright (c) 1990 by Christian Queinnec. All rights reserved.
;;; 22 July 90, version 2.13
;;;===============================================================

;;; This program is distributed in the hope that it will be useful.
;;; Use and copying of this software and preparation of derivative works
;;; based upon this software are permitted, so long as the following
;;; conditions are met:
;;;      o credit to the authors is acknowledged following current
;;;        academic behaviour
;;;      o no fees or compensation are charged for use, copies, or
;;;        access to this software
;;;      o this copyright notice is included intact.
;;; This software is made available AS IS, and no warranty is made about 
;;; the software or its performance. 

;;; Bug descriptions, use reports, comments or suggestions are welcome.
;;; Send them to    queinnec@poly.polytechnique.fr   or to:
;;;      Christian Queinnec
;;;      Laboratoire d'Informatique de l'X
;;;      Ecole Polytechnique
;;;      91128 Palaiseau
;;;      France

;;;===============================================
;;;          A naive pattern-match compiler
;;;  Christian Queinnec   
;;;  Ecole Polytechnique & INRIA - Rocquencourt
;;;          queinnec@poly.polytechnique.fr
;;;===============================================
;;; These programs are not efficient. They only define a
;;; simple but useful pattern match compiler. The generated 
;;; code is purely functional and tail recursive. This file
;;; also contains an tentative lispish syntax for patterns.

;;; The pattern match compiler is fully described in a companion
;;; paper: Compilation of Non-Linear, Second Order Patterns on
;;;        S-Expressions, Christian Queinnec, PLILP 90, Link\"oping,
;;;        Sweden, August 1990, LNCS 456.

;;; How to use it: 
;;;   first load it 
;;;   then read how are defined patterns 
;;;       (the grammar is in comments somewhere below)
;;;   then use the three macros:
;;;       (match-lambda pattern . body)
;;;       (match-all-lambda pattern . body)
;;;       (match-case expression 
;;;           (pattern1 . body1) ... (patternN . bodyN) )

;;; NOTE for portability: This file uses defmacro, error and gensym
;;; which are non standard in Scheme.

;;; The file successively contains the compiler, macros and the
;;; standardizer (which converts a pattern to the reduced pattern
;;; language).

;;;===========================================================1
;;; The pattern compiler

(define (compile-match-meaning f)
  (case (car f)
    ((*sexp) (compile-match-sexp-meaning))
    ((*quote) (compile-match-quote-meaning (cadr f)))
    ((*or) (compile-match-or-meaning (cadr f) (caddr f)))
    ((*and) (compile-match-and-meaning (cadr f) (caddr f)))
    ((*not) (compile-match-not-meaning (cadr f)))
    ((*setq) (compile-match-setq-meaning (cadr f) (caddr f)))
    ((*eval) (compile-match-eval-meaning (cadr f)))
    ((*cons) (compile-match-cons-meaning (cadr f) (caddr f)))
    ((*ssetq-append) (compile-match-ssetq-append-meaning 
                      (cadr f) (caddr f) (cadddr f) ))
    ((*eval-append) (compile-match-eval-append-meaning 
                     (cadr f) (caddr f) ))
    ((*end-ssetq) (compile-match-end-ssetq-meaning (cadr f)))
    ((*times) (compile-match-times-meaning (cadr f) (caddr f) (cadddr f)))
    ((*end-times) (compile-match-end-times-meaning (cadr f)))
    ((*success) (compile-match-success-meaning (cadr f)))
    ((*check) (compile-match-check-meaning (cadr f)))
    (else (match-wrong "Unrecognized primitive pattern" f)) ) )

(define (compile-match-sexp-meaning)
  (lambda (e r a m k) (k e r)) )

(define (compile-match-quote-meaning ee)
  (lambda (e r a m k) 
    `(and (equal? ,e ',ee) ,(k e r)) ) )

(define (compile-match-cons-meaning f1 f2)
  (lambda (e r a m k)
    `(and (pair? ,e)
          ,((compile-match-meaning f1)
            `(car ,e) r a.init m.init 
            (lambda (ee rr)
              ((compile-match-meaning f2)
               `(cdr ,e) rr a m k ) ) ) ) ) )

(define (compile-match-or-meaning f1 f2)
  (lambda (e r a m k)
    `(or ,((compile-match-meaning f1) e r a m k)
         ,((compile-match-meaning f2) e r a m k) ) ) )

(define (compile-match-and-meaning f1 f2)
  (lambda (e r a m k)
    ((compile-match-meaning f1)
     e r a m (lambda (ee rr)
               ((compile-match-meaning f2)
                e rr a m k ) ) ) ) )

(define (compile-match-not-meaning f)
  (lambda (e r a m k)
    `(if ,((compile-match-meaning f) 
           e r a m (lambda (ee rr) `#t) )
         #f
         ,(k e r) ) ) )

(define (compile-match-setq-meaning n f)
  (lambda (e r a m k)
    ((compile-match-meaning f)
     e r a m (lambda (ee rr)
               (if (eq? (lookup rr n) unbound-pattern)
                   `(let ((,n ,e))
                         ,(k e (extend rr n n)) )
                   (match-wrong "Cannot rebind pattern" n) ) ) ) ) )

(define (compile-match-eval-meaning n)
  (lambda (e r a m k)
    (let ((form (lookup r n)))
      (if (eq? form unbound-pattern)
          (match-wrong "Unbound pattern" n)
          (if (pair? form) ;; here form = (cut head tail promise)
              `(segment-check ,e ,(cadr form) ,(caddr form)
                       ,(let ((g (gensym)))
                           `(lambda (,g) 
                               (if (null? ,g) ,(k g r) #f) ) ) )
              `(and (equal? ,form ,e) ,(k e r)) ) ) ) ) )

(define (compile-match-ssetq-append-meaning n f1 f2)
  (lambda (e r a m k)
    ((compile-match-meaning f1)
     e r (extend a.init n 
            (lambda (ee rr)
              (if (eq? (lookup rr n) unbound-pattern)
                  (let ((g (gensym)))
                    `(letrec ((,g (delay (set! ,n (cut ,e ,ee))))
                              (,n 'wait) )
                       ,((compile-match-meaning f2)
                         ee (extend rr n `(cut ,e ,ee ,g)) a m k ) ) )
                  (match-wrong "cannot rebind pattern" n) ) ) )
     m.init (lambda (ee rr)
              (match-wrong "*ssetq-append not ended" f1) ) ) ) )

(define (compile-match-eval-append-meaning n f)
  (lambda (e r a m k)
    (let ((form (lookup r n)))
      (if (eq? (lookup r n) unbound-pattern)
          (match-wrong "Unbound segment" n)
          (let ((g (gensym)))
            (if (pair? form)  ;; here form = (cut head tail promise)
              `(segment-check ,e ,(cadr form) ,(caddr form)
                       (lambda (,g)
                         ,((compile-match-meaning f)
                           g r a m k ) ) )
              `(term-check ,e ,form 
                     (lambda (,g) 
                       ,((compile-match-meaning f)
                         g r a m k ) ) ) ) ) ) ) ) )

(define (compile-match-end-ssetq-meaning n)
  (lambda (e r a m k)
    ((lookup a n) e r) ) )

(define (compile-match-times-meaning n f1 f2)
  (lambda (e r a m k)
    (let ((g (gensym)) (try (gensym)))
      `(letrec 
        ((,try 
           (lambda (,g)
             (or ,((compile-match-meaning f2)
                   g r a m k )
                 ,((compile-match-meaning f1)
                   g r a.init 
                       (extend m.init n 
                          (lambda (ee rr)
                            (if (eq? rr r)
                                `(,try ,ee)
                                ;; This will always lead to match-wrong:
                                ((compile-match-times-meaning n f1 f2)
                                 ee rr a m k ) ) ) )
                       (lambda (ee rr)
                         (match-wrong "Times not ended" f1) ) ) ) ) ))
        (,try ,e) ) ) ) )

(define (compile-match-end-times-meaning n)
  (lambda (e r a m k)
    ((lookup m n) e r) ) )

(define (compile-match-success-meaning form)
  (lambda (e r a m k)
    `(and (begin ,@(force-all-segments r) ,form) 
          ,(k e r)) ) )

(define (compile-match-check-meaning predicate)
  (lambda (e r a m k)
    `(and (begin ,@(force-all-segments r) (,predicate ,e))
          ,(k e r) ) ) )

(define (a.init n)
  (lambda (e r)
    (match-wrong "No current ssetq for" n) ) )

(define (m.init n)
  (lambda (e r)
    (match-wrong "No current repetition named" n) ) )

(define (r.init n)
  unbound-pattern )

(define unbound-pattern (gensym))

(define (extend fn pt im)
  (cons (cons pt im) fn) )

(define (lookup r n)
  (if (pair? r)
      (if (eq? (caar r) n) (cdar r)
          (lookup (cdr r) n) )
      (r n) ) )

;;; Emit all the force forms needed for segment variables that
;;; are not yet forced. Look in R for these variables.
(define (force-all-segments r)
  (if (pair? r)
      (let ((form (cdar r)))
        (if (pair? form) ;; here form = (cut head tail promise)
            (cons `(force ,(cadddr form))
                  (force-all-segments (cdr r)) )
            (force-all-segments (cdr r)) ) )
      '() ) )

;;;===========================================================2
;;; Some library functions that appear in the generated code.

;;; Compare the beginning of term E against the term EE
(define (term-check e ee fn)
  (if (and (pair? e)
           (pair? ee)
           (equal? (car e) (car ee)) )
      (term-check (cdr e) (cdr ee) fn)
      (if (null? ee) (fn e) #f) ) )

;;; Compare the term E and the segment (CUT HEAD TAIL)
(define (segment-check e head tail fn)
  (if (eq? head tail)
      (fn e)
      (if (pair? e)
          (if (equal? (car e) (car head))
              (segment-check (cdr e) (cdr head) tail fn)
              #f )
          #f ) ) )

(define (cut e ee)
  (if (eq? e ee) '()
      (cons (car e) (cut (cdr e) ee)) ) )

;;;===========================================================3
;;; The matching macros. Match failure return #f as is usual in Lisp.

;;; If true displays the code generated by the pattern compiler.
(define *show-pattern-expansion* #f)
' (define *show-pattern-expansion* #t)

(defmacro match-lambda (pattern . body)
  (let* ((g (gensym)) (k (gensym))
         (code ((compile-match-meaning 
                   `(*and ,(normalize-pattern pattern)
                          (*success (,k (begin . ,body))) ) )
                g r.init a.init m.init
                (lambda (ee rr) `#f) ))
         (function `(lambda (,g) (call/cc (lambda (,k) ,code)))) )
    (if *show-pattern-expansion* (display function))
    function ) )

(defmacro match-all-lambda (pattern . body)
  (let* ((g (gensym))
         (code ((compile-match-meaning 
                   `(*and ,(normalize-pattern pattern)
                          (*success (begin ,@body #f)) ) )
                g r.init a.init m.init
                (lambda (ee rr) `#f) ))
         (function `(lambda (,g) ,code)) )
    (if *show-pattern-expansion* (display function))
    function ) )

;;; Some examples of match-case appear below.
(defmacro match-case (tag . clauses)
  (let ((k (gensym))
        (g (gensym)) )
    `(let ((,g ,tag))
       (call/cc 
        (lambda (,k)
          (or ,@(mapcar (lambda (clause) 
                          `((match-lambda ,(car clause)
                                          (,k (begin . ,(cdr clause))) )
                            ,g ) )
                        clauses )
                (error "Unsuccessful match-case") ) ) ) ) ) )

;;;===========================================================4
;;; The standardizer converts patterns with an 
;;; extended syntax into pattern within the reduced pattern set.
;;; The extended language use the following approximate grammar:
;;; pat     := ( patlist )
;;;          | ?- | ?x | <constant>
;;; patlist := ( pat . patlist ) | <nothing> | pat ...
;;;          | ??- | ??x | ???- | ???x
;;; As it stands it is not very convenient but a good syntax, with
;;; the simplicity of the backquote facility, has yet to be invented.
;;; We nevertheless offer the three-dots convention of extend-syntax
;;; which meaning is a sequence of the preceding pattern.

;;; You can also define your own macro-patterns which are expanded before
;;; being used (see defmacro-pattern below).
;;; To define macro-pattern use the following macro: variables
;;; will be bound to the arguments of the pattern (see examples below).
;;; A macro-pattern is simply rewritten into another pattern.
(defmacro defmacro-pattern (name variables . body)
  `(begin
    (set! r.macro-pattern
         (extend r.macro-pattern
                 ',name
                 (lambda ,variables . ,body) ) )
    ',name ) )

;;; The environment binding name to macro-pattern
(define (r.macro-pattern name)
  #f )

(define (macro-pattern? e)
  (and (pair? e)
       (lookup r.macro-pattern (car e)) ) )

;;;===============================================================5
;;; Standardization of patterns (very weak for now)
;;; Usual patterns such as ?x, ?-, ??y, ??-, ???x or ???- are
;;; represented as symbols. Other choices may be taken such as
;;; making ? a macro-character.

(define (term-variable? e)
  (and (symbol? e)
       (> (string-length (symbol->string e)) 1)
       (char=? (string-ref (symbol->string e) 0) #\?) ) )

(define (segment-variable? e)
  (and (symbol? e)
       (> (string-length (symbol->string e)) 2)
       (char=? (string-ref (symbol->string e) 0) #\?)
       (char=? (string-ref (symbol->string e) 1) #\?) ) )

(define (lispish-segment-variable? e)
  (and (symbol? e)
       (> (string-length (symbol->string e)) 3)
       (char=? (string-ref (symbol->string e) 0) #\?)
       (char=? (string-ref (symbol->string e) 1) #\?)
       (char=? (string-ref (symbol->string e) 2) #\?) ) )

(define (term-variable-true-name e)
  (let ((s (symbol->string e)))
    (string->symbol (substring s 1 (string-length s))) ) )

(define (segment-variable-true-name e)
  (let ((s (symbol->string e)))
    (string->symbol (substring s 2 (string-length s))) ) )

(define (lispish-segment-variable-true-name e)
  (let ((s (symbol->string e)))
    (string->symbol (substring s 3 (string-length s))) ) )

;;;===============================================================6
;;; The normalization of the pattern extended syntax.

(define (normalize-pattern e)
  ((standardize-pattern e) 
   r.init
   (lambda (pattern rr) pattern) ) )

;(define (standardize-pattern e)
;  (match-case e
;    ( (*check macro-pattern?) (standardize-macro-pattern e) )
;    ( (*quote ?-)  (standardize-sexp) )
;    ( (*check term-variable?) (standardize-term-variable e) )
;    ( (*check atom?) (standardize-quote e) )
;    ( (*sexp) (standardize-patterns e) ) ) )

(define (standardize-pattern e)
  (cond ((macro-pattern? e) (standardize-macro-pattern e))
        ((eq? e '?-) (standardize-sexp))
        ((term-variable? e) (standardize-term-variable e))
        ((atom? e) (standardize-quote e))
        (t (standardize-patterns e)) ) )

;(define (standardize-patterns e*)
;  (match-case (car e*)
;    ( (*quote ??-) (standardize-any (cdr e*)) )
;    ( (*check segment-variable?) 
;      (standardize-segment-variable (car e*) (cdr e*)) )
;    ( (*sexp)
;      (standardize-cons (car e*) (cdr e*)) ) ) )

(define (standardize-patterns e*)
  (if (pair? e*)
      (cond ((eq? (car e*) '??-) (standardize-any (cdr e*)))
	    ((eq? (car e*) '???-) (standardize-lispish-any (cdr e*)))
	    ((lispish-segment-variable? (car e*))
	     (standardize-lispish-segment-variable (car e*) (cdr e*)) )
	    ((segment-variable? (car e*))
	     (standardize-segment-variable (car e*) (cdr e*)) )
	    (t (standardize-cons (car e*) (cdr e*))) )
      (standardize-quote e*) ) )

(define (standardize-repetition e e*)
  (lambda (r c) 
    ((standardize-pattern e)
     r
     (lambda (f rr)
       ((standardize-patterns e*)
        rr
        (lambda (f* rrr)
          (let ((label (gensym)))
               (c `(*times ,label
                           (*cons ,f (*end-times ,label))
                           ,f* )
                  rrr ) ) ) ) ) ) ) )

(define (standardize-sexp)
  (lambda (r c)
    (c `(*sexp) r) ) )

(define (standardize-cons f f*)
  (if (and (pair? f*) (eq? (car f*) '...))
      (standardize-repetition f (cdr f*))
      (standardize-real-cons f f*) ) )

(define (standardize-real-cons f f*)
  (lambda (r c)
    ((standardize-pattern f)
     r
     (lambda (pattern1 rr)
       ((standardize-patterns f*)
        rr
        (lambda (pattern2 rrr)
          (c `(*cons ,pattern1 ,pattern2) rrr) ) ) ) ) ) )

(define (standardize-term-variable e)
  (lambda (r c)
    (let ((name (term-variable-true-name e)))
      (if (eq? (lookup r name) unbound-pattern)
          (c `(*setq ,name (*sexp)) 
             (extend r name 'term) )
          (c `(*eval ,name) r) ) ) ) )

(define (standardize-quote e)
  (lambda (r c)
    (c `(*quote ,e) r) ) )

(define (standardize-segment-variable e f*)
  (lambda (r c)
    (let ((name (segment-variable-true-name e)))
      (if (eq? (lookup r name) unbound-pattern)
          ((standardize-patterns f*)
           (extend r name 'segment)
           (lambda (pattern rr)
             (let ((label (gensym)))
               (c `(*ssetq-append 
                    ,name 
                    (*times ,label
                            (*cons (*sexp) (*end-times ,label))
                            (*end-ssetq ,name) )
                            ,pattern )
                  rr ) ) ) )
          ((standardize-patterns f*)
           r
           (lambda (pattern rr)
             (c `(*eval-append ,name ,pattern) rr) ) ) ) ) ) )

(define (standardize-lispish-segment-variable e f*)
  (if (null? f*)
      (lambda (r c)
        (let ((name (lispish-segment-variable-true-name e)))
          (if (eq? (lookup r name) unbound-pattern)
              (c `(*setq ,name (*sexp))
                 (extend r name 'segment) )
              (c `(*eval ,name) r) ) ) )
      (standardize-segment-variable e f*) ) )

(define (standardize-any f*)
  (lambda (r c)
    ((standardize-patterns f*)
     r
     (lambda (pattern rr)
       (let ((label (gensym)))
         (c `(*times ,label
                  (*cons (*sexp) (*end-times ,label))
                  ,pattern )
            rr ) ) ) ) ) )

(define (standardize-lispish-any f*)
  (if (null? f*)
      (lambda (r c) (c `(*sexp) r))
      (standardize-any f*) ) )

(define (standardize-macro-pattern e)
  (apply (lookup r.macro-pattern (car e)) (cdr e)) )

;;;===============================================================7
;;; Three examples of macro-patterns: 

;;; Convert n-ary *or into binary *or
(defmacro-pattern *or (e . e*)
  (lambda (r c)
    (if (pair? e*)
        ((standardize-pattern e)
         r
         (lambda (pattern1 rr)
           ((standardize-pattern `(*or . ,e*))
            r
            (lambda (pattern2 rrr)
              (if (coherent-environment? rr rrr)
                  (c `(*or ,pattern1 ,pattern2) rrr)
                  (match-wrong "Incompatible alternative") ) ) ) ) )
        ((standardize-pattern e) r c) ) ) )

;;; check coherency between arms of alternative patterns:
;;; For instance (match-lambda (*or ?x ?y) t) is not coherent
;;; while (match-lambda (*or (?x ?y) (?y ?x)) t) is coherent.
(define (coherent-environment? r rr)
  (letrec ((look (lambda (n r)
                   (and (pair? r)
                        (or (eq? (caar r) n)
                            (look n (cdr r)) ) ) )))
    (if (pair? r)
        (and (look (caar r) rr)
             (coherent-environment? (cdr r) rr) )
        #t ) ) )

;;; Convert n-ary *and into binary *and
(defmacro-pattern *and (e . e*)
  (lambda (r c)
    (if (pair? e*)
        ((standardize-pattern e)
         r
         (lambda (pattern1 rr)
           ((standardize-pattern `(*and . ,e*))
            rr
            (lambda (pattern2 rrr)
              (c `(*and ,pattern1 ,pattern2) rrr) ) ) ) )
        ((standardize-pattern e) r c) ) ) )

;;; Normalize *not patterns
(defmacro-pattern *not (e)
  (lambda (r c)
    ((standardize-pattern e)
     r
     (lambda (pattern rr)
       (c `(*not ,pattern) r) ) ) ) )

;;;===============================================================8
;;; report an error (implementation dependent)

(define (match-wrong . args)
  (apply error args) )
