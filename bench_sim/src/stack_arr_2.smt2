(declare-sort Elem)

(declare-fun in () Elem)
(declare-fun out () Elem)
(declare-fun n () Int)
(declare-fun n1 () Int)
(declare-fun A () (Array Int Elem))
(declare-fun A1 () (Array Int Elem))

; isempty

(assert (= n 5))

; push

(assert
  (and
  (= A1 (store A n in))
  (= n1 (+ n 2))))

; pop

(assert
  (and
    (> n 5)
    (= n1 (- n 2))
    (= A1 A)
    (= out (select A n1))))

