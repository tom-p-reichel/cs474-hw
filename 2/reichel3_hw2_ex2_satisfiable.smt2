(declare-fun q () Bool)
(declare-fun r () Bool)
(declare-fun p () Bool)
(assert (and (or (not r) q)
     (or r (not p))
     (or r (not q) p)
     (or q (not q) p)
     (or (not r) q)))
; this is the original formula,
; so it should be satisfiable
(check-sat)
