(declare-fun u2 () Real)
(declare-fun l2 () Real)
(declare-fun u1 () Real)
(declare-fun l1 () Real)
(declare-fun z () Real)
(assert
  (=> (and (< l1 z) (< z u1) (< l2 z) (< z u2))
      (exists ((w Real))
        (and (< l1 w) (< w u1) (< l2 w) (< w u2) (distinct w z)))))
(apply qe)
