(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun in () Elem)
(declare-fun in2 () Elem)
(declare-fun out () Elem)
(declare-fun out2 () Elem)

; isempty

(assert (= xs nil))

; push

(assert (= xs1 (cons in (cons in2 xs))))

; pop

(assert (= xs (cons out (cons out2 xs1))))
