module Tests/regression_test1
open lcm_skeleton

//All tests concerning the interplay of eo and po
pred t1[] {all e : Event | all e' : Event | e -> e' in ^eo and e in (po+~po).Event and e' in (po+~po).Event implies e->e' in ^po}
pred t2[] {acyclic[eo+po]}


check {t1 && t2}
