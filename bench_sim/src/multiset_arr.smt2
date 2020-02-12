(declare-sort Elem)

(declare-fun in () Elem)
(declare-fun out () Elem)
(declare-fun outb () Int)
(declare-fun s  () (Array Elem Int))
(declare-fun s1 () (Array Elem Int))

; init

(assert
  (forall ((a Elem)) (= (select s a) 0)))

; num of elements

(assert
  (= outb (select s in)))

; insert

(assert
  (= s1 (store s in (+ 1 (select s in)))))

; remove

(assert
  (= s1 (store s in 0)))