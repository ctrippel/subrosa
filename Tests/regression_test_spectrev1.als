module Tests/regression_test_spectrev1
open lcm_skeleton as lcm

// Spectre v1
//NOTE: There are two additional efrx loops that are not shown in the paper that would be ruled out in most consistency predicates.
pred t1[] {#Event = 5 and #CacheFlush = 1 and #Branch=1 and #Read = 3 and #Write = 0 and #REG=0}
pred t2[] {#Address = 2 and #XState=3}
pred t3[] {#po=2 and #tfo=4}
pred t4[] {#addr = 1 and #erfx = 2 and #ecox = 1 /*and #efrx = 1*/ and #rf_init =2 and #rf=0 and #co=0 and #fr=0}
pred t5[] {
some disj a0, a1 : Address | some disj s0, s1, s2 : XState | 
some cf : CacheFlush | some disj r1, r2, r3 : Read | some br : Branch |
  (cf.address = a1) and (cf.xstate_access.xstate = s1) and (br.xstate_access.xstate = s2) and (r1.address = a0) 
  and (r1.xstate_access.xstate = s0) and (r2.address = a1) and (r2.xstate_access.xstate = s1) and (r3.address = a1)
  and (r3.xstate_access.xstate = s1)
  and (cf->br in po) and (cf->br in tfo) and (br->r1 in tfo) and (r1->r2 in tfo) and (r2->r3 in tfo) and (br->r3 in po)
  and (r1->r2 in addr) and (cf ->r2 in erfx)  and (cf->r2 in ecox) and (cf->r2 in efrx) and (r2->r3 in erfx)
  and (cf->r2 in rf_init) and (cf->r3 in rf_init)  
  //and a0.privilege_domain = VictimControlled and a1.privilege_domain = AttackerControlled
}

fact{t1 && t2 && t3 && t4 && t5}

// Check if we can model the attack
//run{} for 5

// Check if our model captures the leakage
//check {not {some e:Event| some e':Event| leakage[e,e']}} for 5

// Check if the leakage is caused by an intervening access or lacking extra architectural communication or both
//check {not {some e:Event| some e':Event| not {e != e' and e->e' in com_arch and same_xstate[e,e'] => (not com_comx_inconsistent[e,e'])}}} for 5
//check {not {some e:Event| some e':Event| not {e != e' and e->e' in com_arch and same_xstate[e,e'] => (not intervening_access[e,e'])}}} for 5

// Identify what is leaked
//check {not {some candidate_source: Event | some sink:Event | xstate_leakage[candidate_source,sink]}} for 5
//check {not {some candidate_source: Event | some sink:Event | data_leakage[candidate_source,sink]}} for 5

//Identify what is leaked considering Privilege Domains
//check {not {some candidate_source: Event | some sink:Event | xstate_leakage[candidate_source,sink]
// 	     and not leakage_is_benign[candidate_source,sink]}} for 5
//check {not {some candidate_source: Event | some sink:Event | data_leakage[candidate_source,sink] 
//            and not leakage_is_benign[candidate_source,sink]}} for 5


