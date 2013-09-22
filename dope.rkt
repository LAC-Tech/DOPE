#lang racket

#|
2012, 2013 - Lewis Potter

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
|#

#|
DOPE - Declarative Protype Object Extension.
    
Features:
- Prototype based, no distinction between classes and instances.
- Multiple inheritance, methods are looked up in depth first search
- Declarative syntax, can create an object with a single macro, no need to clone
  and mutate
- Immutable objects, which can be inherited by and inherit from mutable ones

thanks to: 
-rapacity, offby1, jeapostrophe, jonrafkind, mithos28, neilv, asumu and 
 everyone in #racket on freenode
|#

(require racket/serialize)
(require rackunit)
(require racket/contract)
(require unstable/list) 

(provide
 make-object (rename-out [make-object object])
 make-immutable-object (rename-out [make-immutable-object object-immutable])
 def-object
 def-immutable-object
 root
 @ (rename-out [@ object-apply])
 @self (rename-out [@self object-apply-self])
 ! (rename-out [! object-set!])
 ^ (rename-out [^ object-parents])
 method
 (contract-out
  [object-unique-keys (-> object? (listof any/c))]
  [object-keys (-> object? (hash/c any/c exact-positive-integer?))]
  [object-depth (-> object? exact-positive-integer?)]
  [object? (-> object? boolean?)]
  [object-copy (-> object? object?)]))

#|
an object is represented internally as a struct, with a field for a plain 
hashtable, and a field for a parents. the struct returns a procedure which 
takes as an argument a key to the slotfield
|#
(serializable-struct object ([parents #:mutable] slots)
  #:property prop:procedure
  (λ (self msg)
    (define parents (object-parents self)) ; table that is referenced if key is not found
    (define slots (object-slots self)) ; internal hash-table
    ;will be false if no message is found
    (define (lookup msg)
      (for/first ([parent (in-list parents)]
                  #:when [not (null? (parent msg))])
        (parent msg)))
    (match msg
      ['_slots slots]
      ['parents parents]      
      ['clone (object self slots)]
      [_ (hash-ref slots msg 
                   ;if the key is not in the tables slots, recursively look up parents
                   (λ() (match parents
                          ['#() null] ;if the parents slot is empty return null
                          [_ (let ([result (lookup msg)])                                                   
                                  (if (not result) null result))])))])))

;get parents
(define-syntax-rule (^ tbl)
  (tbl '_parents))

(define-syntax parse-single-slot
  (syntax-rules (def-method)
    [(_ key value) `(key . ,value)]
    [(_ def-method (id args ...) body ...)
     `(id . ,(method (args ...) body ...))]))

; transforms "[k v] ..." to "`((k . ,v) ...)"
(define-syntax-rule (parse-slots (key value ...) ...)
  (list (parse-single-slot key value ...) ...))

;root table
(define root (object (list) (make-hash)))

#|
convenient "constructor" macro for tables. This should be the public interface.
|#

(define-syntax make-object
  (syntax-rules ()
    [(make-object [k v ...] ...)
     (object (list root) (make-hash (parse-slots [k v ...] ...)))]
    [(make-object #:parents (p ...) [k v ...] ...)
     (object (list p ...) (make-hash (parse-slots [k v ...] ...)))]))

; I find this short hand useful. perhaps too much syntactic sugar...
(define-syntax-rule (def-object id tbl ...)
  (define id (make-object tbl ...)))

; Setting a value in a table
(define-syntax-rule (! tbl key value)
  (hash-set! (object-slots tbl) key value))

#|
Returns all the keys of the tables slots, but omits the parents keys that it
still responds to
|#
(define (object-unique-keys tbl)
  (hash-keys (object-slots tbl)))

#|
Recursively finds all the keys in a table, by searching its parentss, then its 
parents parents etc
|#
(define (object-keys-list tbl)
  (match tbl
    [(== root) (object-unique-keys tbl)]
    [_ (append* (object-unique-keys tbl) 
                (for/list ([p [tbl 'parents]]) 
                  (object-keys-list p)))]))

#|
Returns a hashof all the messages a table can respond to. The key values of the
hash are the locations of those keys, and the values are how many of its 
ancestors also respond to that key
|#
(define (object-keys tbl)
  ;Groups identical keys together
  (define grouped-keys [group-by eq? (object-keys-list tbl)])
  ;Transforms a group of identical keys into a hash table element
  (define (keys-to-element group) `(,(car group) . ,(length group)))
  (make-hash (map keys-to-element grouped-keys)))

;The depth of a table, ie the maximum distance between it and root
(define (object-depth tbl)
  (match tbl
    [(== root) 0]
    [_ (add1 (apply max (for/list ([t [tbl 'parents]]) (object-depth t))))]))

#|
  like lambda but implicitly adds a self argument. because if you had to add in
  self manually, this would be no better than python.
|#
(define-syntax (method stx) 
  (syntax-case stx ()
    [(_ (args ...) body ...) 
     (with-syntax 
         ([self (syntax-local-introduce (syntax-local-get-shadower #'self))]) 
       #'(lambda (self args ...) body ...))]))

; Applying a method
(define-syntax-rule (@ tbl method args ...)
     (apply [tbl method] (list tbl args ...)))

; Applying a method to self
(define-syntax (@self stx)
  (syntax-case stx ()
    [(_ method args ...)
      (with-syntax ([self (syntax-local-introduce (syntax-local-get-shadower #'self))]) 
        #'(@ self method args ...))]))

;Deep table copy
(define (object-copy tbl)
  (object [tbl '_parent] (hash-copy [tbl '_slots])))

;;; IMMUTABLE TABLES

(define-syntax make-immutable-object
  (syntax-rules ()
    [(_ [k v ...] ...)
     (object (list root) (make-immutable-hash (parse-slots [k v ...] ...)))]
    [(_ #:parents (p ...) [k v ...] ...)
     (object (list p ...) (make-immutable-hash (parse-slots [k v ...] ...)))]))

(define-syntax-rule (def-immutable-object id tbl ...)
  (define id (make-immutable-object tbl ...)))

#|

TESTS

|#
(module+ test
  (require rackunit)

(def-object t1 [x 1])
(def-object t2 #:parents (t1) [y 4])
(def-object t3 #:parents (t2) [z 5])
(def-object t4 #:parents (t3) [a 0])

(check-equal? (t2 'x) 1)
(check-equal? [object-keys t4] 
              [make-hash '((x . 1) (a . 1) (y . 1) (z . 1))])

;check it responds correctly to an unrecognised message
(check-equal? (t2 'adsad) null)

(def-object posn
  [x 4]
  [y 3]     
  [magnitude (method () 
               (sqrt (+ (sqr [self 'x]) (sqr [self 'y]))))]
  [add-x (method (x) (+ [self 'x] x))])

(def-object posn-new #:parents (posn))

(check-equal? (@ posn 'magnitude) 5)
(check-equal? (@ posn-new 'magnitude) 5)

#| Multiple inheritance stuff |#
(def-object homo-sapien [personality 'curious])
(def-object mother #:parents(homo-sapien) [gender 'female])
(def-object father #:parents(homo-sapien) [gender 'male] [personality 'drunk])
(def-object takes-after-mom #:parents(mother father))
(def-object takes-after-dad #:parents(father mother))
(def-object mule-child #:parents(takes-after-mom mother))

; Inheritance lookup is left right
(check-equal? (takes-after-mom 'gender) 'female)
(check-equal? (takes-after-dad 'gender) 'male)

;Getting the first parents personality
(check-equal? (takes-after-dad 'personality) 'drunk)
;multiple inheritance is depth first, so should get the homo-sapien personality 
;before fathers
(check-equal? (takes-after-mom 'personality) 'curious)

(check-equal? (object-depth mother) 2)
(check-equal? (object-depth takes-after-mom) 3)
; *maximum* depth from root
(check-equal? (object-depth mule-child) 4)

(define original (make-object [foo 42]))
(define copy (object-copy original))
(! original 'lol "lmao")
(check-equal? (copy 'lol) null)
(check-equal? (copy 'foo) 42)
  
;Checking you can't modify immutable hash
(define const (make-immutable-object [x 42]))
(check-exn exn:fail? (λ() (! const 'x 0)))

#|
Following "JavaScript and Object Oriented Programming (OOP)" tutorial
http://www.javascriptkit.com/javatutors/oopjs.shtml

This is just to see I can do what the one mainstream prototype language does

Often, the tutorial instructs the user to call the "alert" procedure to check
state - in my case I merely return the string and unit test against it.

Apparently this tutorial is not highly regarded among JS programmers.
|#

;; 1. Tutorial introduction (basic ways of creating an object)

(def-object person)
(! person 'name "Tim Scarfe")
(! person 'height "6ft")
(! person 'run
   (method ()
     (! self 'state "running")
     (! self 'speed "4ms^-1")))

(def-object tim-object
  [property1 "hello"]
  [property2 "MmmMMm"]
  [property3 '("mmm" 2 3 6 "kkk")]
  [method1 (method() (printf "Method has been called ~e" [self 'property1]))])

(check-equal? (list-ref [tim-object 'property3] 2)
              3)

(def-object circle [x 0] [y 0] [radius 2]) ;another example

;nesting is no problem.
(def-object rectangle
  [upper-left (make-object [x 2] [y 2])]
  [lower-right (make-object [x 4] [y 4])])

(check-equal? ([rectangle 'upper-left] 'x)
              2)

;; 2. Object Constructor and prototyping

(def-object cat 
  [talk (method () (string-append [self 'name] " says meeow!" ))])

(define (make-cat name) 
  (make-object #:parents (cat) [name name]))

(define cat1 (make-cat "felix"))
(check-equal? (@ cat1 'talk) "felix says meeow!")

(define cat2 (make-cat "ginger"))
(check-equal? (@ cat2 'talk) "ginger says meeow!")

(! cat 'change-name
   (method (name) [! self 'name name]))

(define first-cat (make-cat "pursur"))
(@ first-cat 'change-name "Bill")
(check-equal? (@ first-cat 'talk)
              "Bill says meeow!")

;; 3. Subclasses and Superclasses

(define (super-test self) "super-test")
(define (sub-test self) "sub-test")

(def-object super-class 
  [super-test super-test])

(def-object sub-class
  #:parents (super-class)
  [sub-test sub-test]) ;attach method sub-test

(def-object new-class #:parents (sub-class))
  
(check-equal? (@ new-class 'sub-test)
              "sub-test")
(check-equal? (@ new-class 'super-test)
              "super-test")

;;; 4. Associative arrays, looping, and JScript.NET
; This section is irrelevant. It's trivial to loop through a table with
; object-keys
) ;module end
