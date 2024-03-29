module Tests/regression_test_spectrev2
open lcm_skeleton as lcm

// Spectre v2
//NOTE: Jump performance optimization has to be commented out in lcm_skeleton
//NOTE: There are two additional efrx loops that are not shown in the paper that would be ruled out in most consistency predicates.
pred t1[] {#Event = 5 and #CacheFlush = 1 and #Jump=1 and #Read = 3 and #Write = 0}
pred t2[] {#Address = 2 and #XState=3}
pred t3[] {#po=2 and #tfo=4}
pred t4[] {#addr = 1 and #erfx = 2 and #ecox = 1 and #efrx > 0 and #rf_init =2}
pred t5[] {
some disj a0, a1 : Address | some disj s0, s1, s2 : XState | some cf : CacheFlush | some disj r1, r2, r3 : Read | some j : Jump  |
  (cf.address = a1) and (cf.xstate_access.xstate = s1) and (j.xstate_access.xstate = s2) and (r1.address = a0) and (r1.xstate_access.xstate = s0)
  and (r2.address = a1) and (r2.xstate_access.xstate = s1) and (r3.address = a1) and (r3.xstate_access.xstate = s1) and
  (cf->j in po) and (cf->j in tfo) and (j->r1 in tfo) and (r1->r2 in tfo) and (r2->r3 in tfo) and (j->r3 in po) and
  (r1->r2 in addr) and (cf ->r2 in erfx)  and (cf->r2 in ecox) and (cf->r2 in efrx) and (r2->r3 in erfx) and
  (cf->r2 in rf_init) and (cf->r3 in rf_init)  
}

fact{t1 && t2 && t3 && t4 && t5}

// Check if we can model the attack
run{} for 5

// Check if our model captures the leakage
//check {not {some e1:Event| some e2:Event| leakage[e1,e2]}} for 5

// Check if the leakage is caused by an intervening access or lacking extra architectural communication or both
//check {not {some e1:Event| some e2:Event| not {e1 != e2 and e1->e2 in com_arch and same_xstate[e1,e2] => (com_comx_consistent[e1,e2])}}} for 5
//check {not {some e1:Event| some e2:Event| not {e1 != e2 and e1->e2 in com_arch and same_xstate[e1,e2] => (not intervening_access[e1,e2])}}} for 5

// Identify what is leaked
//check {not {some candidate_source: Event | some sink:Event | xstate_leakage[candidate_source,sink]}} for 5
//check {not {some candidate_source: Event | some sink:Event | data_leakage[candidate_source,sink]}} for 5
