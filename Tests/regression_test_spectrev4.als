module Tests/regression_test_spectrev4
open lcm_skeleton as lcm

// Spectre v1
//NOTE: There are two additional efrx loops that is not shown in the paper that would be ruled out in most consistency predicates.
pred t1[] {#Event = 5 and #CacheFlush = 1 and #Read = 3 and #Write = 1}
pred t2[] {#Address = 2 and #XState=2}
pred t3[] {#po=2 and #eo=4}
pred t4[] {#addr = 1 and #erfx = 2 and #ecox = 1 /*and #efrx = 2*/ and #rf_init =2  and #rf=0 and #co=0 and #fr=0}
pred t5[] {
some disj a0, a1 : Address | some s0, s1 : XState |
some cf : CacheFlush | some r1, r2, r3 : Read | some w : Event  |
  w != cf and w != r1 and w != r2 and w != r3
  and (cf.address = a1) and (cf.xstate_access.xstate = s1) and (w.address = a0) and (w.xstate_access.xstate = s0) and (r1.address = a0) and (r1.xstate_access.xstate = s0)
  and (r2.address = a1) and (r2.xstate_access.xstate = s1) and (r3.address = a1) and (r3.xstate_access.xstate = s1)
  and (cf->w in po) and (cf->w in eo) and (w->r1 in eo) and (r1->r2 in eo) and (r2->r3 in eo) and (w->r3 in po)
  and (r1->r2 in addr) and (cf ->r2 in erfx)  and (cf->r2 in ecox) and (cf->r2 in efrx) and (r2->r3 in erfx) and (r1->w in efrx)
  and (cf->r2 in rf_init) and (cf->r3 in rf_init)  
}

fact{t1 && t2 && t3 && t4 && t5}

// Check if we can model the attack
//run{} for 5

// Check if our model captures the leakage
check {not {some e:Event| some e':Event| not no_leakage[e,e']}} for 5

// Check if the leakage is caused by an intervening access or lacking extra architectural communication or both
//check {not {some e:Event| some e':Event| not {e != e' and e->e' in com_arch and same_xstate[e,e'] => (e->e' in ecomx)}}} for 5
//check {not {some e:Event| some e':Event| not {e != e' and e->e' in com_arch and same_xstate[e,e'] => (not intervening_access[e,e'])}}} for 5

// Identify what is leaked
//check {not {some candidate_source: Event | some sink:Event | xstate_leakage[candidate_source,sink]}} for 5
//check {not {some candidate_source: Event | some sink:Event | data_leakage[candidate_source,sink]}} for 5
