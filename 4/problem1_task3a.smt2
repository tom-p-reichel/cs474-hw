(declare-fun sp2 () Real)
(declare-fun sp22 () Real)
(declare-fun sp12 () Real)
(declare-fun sp1 () Real)
(declare-fun sp21 () Real)
(declare-fun sp11 () Real)
(declare-fun rp22 () Real)
(declare-fun rp2 () Real)
(declare-fun rp12 () Real)
(declare-fun rp1 () Real)
(declare-fun rp21 () Real)
(declare-fun rp11 () Real)
(assert (let ((a!1 (exists ((r1 Real) (r2 Real) (s1 Real) (s2 Real))
             (let ((a!1 (+ (* (+ (* r1 rp11) (* r2 rp21)) s1)
                           (* (+ (* r1 rp12) (* r2 rp22)) s2)))
                   (a!2 (+ (* (+ (* rp1 rp11) (* rp2 rp21)) s1)
                           (* (+ (* rp1 rp12) (* rp2 rp22)) s2)))
                   (a!4 (+ (* (+ (* r1 sp11) (* r2 sp21)) s1)
                           (* (+ (* r1 sp12) (* r2 sp22)) s2)))
                   (a!5 (+ (* (+ (* r1 sp11) (* r2 sp21)) sp1)
                           (* (+ (* r1 sp12) (* r2 sp22)) sp2))))
             (let ((a!3 (=> (and (= (+ rp1 rp2) 1.0)
                                 (>= rp1 0.0)
                                 (<= rp1 1.0)
                                 (>= rp2 0.0)
                                 (<= rp2 1.0))
                            (>= a!1 a!2)))
                   (a!6 (=> (and (= (+ sp1 sp2) 1.0)
                                 (>= sp1 0.0)
                                 (<= sp1 1.0)
                                 (>= sp2 0.0)
                                 (<= sp2 1.0))
                            (>= a!4 a!5))))
               (and (= (+ r1 r2) 1.0)
                    (>= r1 0.0)
                    (<= r1 1.0)
                    (>= r2 0.0)
                    (<= r2 1.0)
                    (= (+ s1 s2) 1.0)
                    (>= s1 0.0)
                    (<= s1 1.0)
                    (>= s2 0.0)
                    (<= s2 1.0)
                    a!3
                    a!6))))))
  (not a!1)))

(check-sat)