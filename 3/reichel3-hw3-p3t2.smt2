(assert (forall ((x Real))
  (exists ((y Real))
    (and (> (* 2.0 y) (* 3.0 x)) (< (* 4.0 y) (+ (* 8.0 x) 10.0))))))

(apply qe)
