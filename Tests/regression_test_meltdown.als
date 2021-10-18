module Tests/regression_test_meltdown
open lcm_perturbed as lcm

// Spectre v3 (Meltdown)
//NOTE: There are two additional efrx loops that are not shown in the paper that would be ruled out in most consistency predicates.
pred t1[] {#Event = 4 and #CacheFlush = 1 and #Read = 3 and #Write = 0}
pred t2[] {#Address = 2 and #XState=2}
pred t3[] {#po=1 and #tfo=3}
pred t4[] {#addr = 1 and #erfx = 2 and #ecox = 1 /*and #efrx = 1*/ and #rf_init =2 and #rf=0 and #co=0 and #fr=0}
pred t5[] {
some disj a0, a1 : Address | some s0, s1 : XState |
some cf : CacheFlush | some r1, r2, r3 : Read  |
  (cf.address = a1) and (cf.xstate_access.xstate = s1) and (r1.address = a0) and (r1.xstate_access.xstate = s0)
  and (r2.address = a1) and (r2.xstate_access.xstate = s1) and (r3.address = a1) and (r3.xstate_access.xstate = s1)
  and (cf->r1 in tfo) and (cf->r3 in po) and (r1->r2 in tfo) and (r2->r3 in tfo)
  and (r1->r2 in addr) and (cf ->r2 in erfx)  and (cf->r2 in ecox) and (cf->r2 in efrx) and (r2->r3 in erfx)
  and (cf->r2 in rf_init) and (cf->r3 in rf_init)
}

fact{t1 && t2 && t3 && t4 && t5}

// Check if we can model the attack
//run{} for 4

// Check if our model captures the leakage
check {not {all e: Event | leakage_different[RE->e]}} for 4

// Check if the leakage is caused by an intervening access or lacking extra architectural communication or both
//check {not {some e:Event| some e':Event| not {e != e' and e->e' in com_arch and same_xstate[e,e'] => (com_comx_consistent[e,e'])}}} for 5
//check {not {some e:Event| some e':Event| not {e != e' and e->e' in com_arch and same_xstate[e,e'] => (not intervening_access[e,e'])}}} for 4

// Identify what is leaked
//check {not {some candidate_source: Event | some sink:Event | xstate_leakage[candidate_source,sink]}} for 4
//check {not {some candidate_source: Event | some sink:Event | data_leakage[candidate_source,sink]}} for 4
