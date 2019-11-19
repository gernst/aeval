(declare-sort Elem)

(declare-fun in () Elem)
(declare-fun out () Elem)
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun m1 () Int)
(declare-fun n1 () Int)
(declare-fun A () (Array Int Elem))
(declare-fun A1 () (Array Int Elem))

; isempty

(assert (= n (+ m 1)))

; enqueue

(assert
  (and
    (= A1 (store A n in))
    (= n1 (+ n 2))
    (= m1 m)))

; dequeue

(assert
  (and
    (< (+ m 1) n)
    (= m1 (+ m 1))
    (= n1 n)
    (= A1 A)
    (= out (select A m))))
