module Tests/regression_test_meltdown
open lcm_skeleton as lcm

// Spectre v3 (Meltdown)
//NOTE: There are two additional efrx loops that is not shown in the paper that would be ruled out in most consistency predicates.
pred t1[] {#Event = 4 and #CacheFlush = 1 and #Read = 3 and #Write = 0}
pred t2[] {#Address = 2 and #XState=2}
pred t3[] {#po=1 and #eo=3}
pred t4[] {#addr = 1 and #erfx = 2 and #ecox = 1 /*and #efrx = 1*/ and #rf_init =2 and #rf=0 and #co=0 and #fr=0}
pred t5[] {
some a0 : Address| some a1 : Address | some s0 : XState | some s1 : XState |
some cf : CacheFlush | some r1 : Read | some r2 : Read | some r3 : Read  |
  a0 != a1 and s0 != s1 and r1 != r2 and r1 != r3 and r2 != r3 and
  (cf.address = a1) and (cf.xstate_access.xstate = s1) and (r1.address = a0) and (r1.xstate_access.xstate = s0)
  and (r2.address = a1) and (r2.xstate_access.xstate = s1) and (r3.address = a1) and (r3.xstate_access.xstate = s1) and
  (cf->r1 in eo) and (cf->r3 in po) and (r1->r2 in eo) and (r2->r3 in eo) and
  (r1->r2 in addr) and (cf ->r2 in erfx)  and (cf->r2 in ecox) and (cf->r2 in efrx) and (r2->r3 in erfx) and
  (cf->r2 in rf_init) and (cf->r3 in rf_init)  
}

// Check if we can model the attack
run{t1 && t2 && t3 && t4 && t5} for 4

// Check if our model captures the leakage
//fact{t1 && t2 && t3 && t4 && t5}
//check {all e:Event| all e':Event| no_leakage[e,e']}
