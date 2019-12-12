(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun allbutlast (Lst) Lst)
(assert (forall ((x Elem)) (= (allbutlast (cons x nil)) nil)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (allbutlast (cons x (cons y xs))) (cons x (allbutlast (cons y xs))))))

(declare-fun last (Lst) Elem)
(assert (forall ((x Elem)) (= (last (cons x nil)) x)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (last (cons x (cons y xs))) (last (cons y xs)))))

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun in () Elem)
(declare-fun out () Elem)

; isempty

(assert (= xs nil))

; enqueue

(assert (= xs1 (cons in xs)))

; dequeue

(assert
  (and
    (distinct xs nil)
    (= xs1 (allbutlast xs))
    (= out (last xs))))
