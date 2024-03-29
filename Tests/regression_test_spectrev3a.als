module Tests/regression_test_meltdown
open lcm_skeleton as lcm

// Spectre v3a
pred t1[] {#Event = 4 and #CacheFlush = 1 and #Read = 3 and #REG = 1}
pred t2[] {#Address = 2 and #XState=2}
pred t3[] {#po=1 and #tfo=3}
pred t4[] {#addr = 1 and #erfx = 2 and #ecox = 1 and #efrx > 0 and #rf_init =2 and #rf=0 and #co=0 and #fr=0}
pred t5[] {
some disj a1, a2 : Address | some disj s1, R : XState |
some cf : CacheFlush | some r1, r2 : Read | some reg : REG  |
  (cf.address = a1) and (cf.xstate_access.xstate = s1) and (r1.address = a1) and (r1.xstate_access.xstate = s1)
  and (r2.address = a1) and (r2.xstate_access.xstate = s1) and (reg.address = a2) and (reg.xstate_access.xstate = R)
  and (cf->reg in tfo) and (cf->r2 in po) and (reg->r1 in tfo) and (r1->r2 in tfo)
  and (reg->r1 in addr) and (cf ->r1 in erfx)  and (cf->r1 in ecox) and (cf->r1 in efrx) and (r1->r2 in erfx)
  and (cf->r1 in rf_init) and (cf->r2 in rf_init)  
}

fact{t1 && t2 && t3 && t4 && t5}

// Check if we can model the attack
//run{} for 4

// Check if our model captures the leakage
//check {not {some e:Event| some e1:Event| leakage[e,e1]}} for 4

// Check if the leakage is caused by an intervening access or lacking extra architectural communication or both
//check {not {some e1:Event| some e2:Event| not {e1 != e2 and e1->e2 in com_arch and same_xstate[e1,e2] => (com_comx_consistent[e1,e2])}}} for 5
//check {not {some e1:Event| some e2:Event| not {e1 != e2 and e1->e2 in com_arch and same_xstate[e1,e2] => (not intervening_access[e1,e2])}}} for 4

// Identify what is leaked
//check {not {some candidate_source: Event | some sink:Event | xstate_leakage[candidate_source,sink]}} for 5
//check {not {some candidate_source: Event | some sink:Event | data_leakage[candidate_source,sink]}} for 5
