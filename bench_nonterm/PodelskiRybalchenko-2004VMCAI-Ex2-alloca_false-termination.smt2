(declare-rel inv (Int ))
(declare-var j Int)
(declare-var j1 Int)

(declare-rel fail ())

(rule (inv j))

(rule (=> 
    (and 
        (inv j )
        (> j 0)
        (= j1 (+ (* 2 j) 10))
    )
    (inv j1 )
  )
)

(rule (=> (and (inv j ) (> j 0)) fail))

(query fail :print-certificate true)