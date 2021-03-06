; K = 0
; Transition relation
(define-fun T ((%init Bool) ($mode$0 Int) ($desiredSpeed$0 Real) ($OK$0 Bool) ($mode$1 Int) ($desiredSpeed$1 Real) ($OK$1 Bool)) Bool (= $OK$1 (or (not (or (= $mode$1 1) (= $mode$1 3))) (= $desiredSpeed$1 (/ 0 10)))))
; Universally quantified variables
(declare-fun %init () Bool)
(declare-fun $mode$~1 () Int)
(declare-fun $desiredSpeed$~1 () Real)
(declare-fun $OK$~1 () Bool)
(declare-fun $mode$0 () Int)
(declare-fun $desiredSpeed$0 () Real)
(declare-fun $OK$0 () Bool)
(assert (T %init $mode$~1 $desiredSpeed$~1 $OK$~1 $mode$0 $desiredSpeed$0 $OK$0))
