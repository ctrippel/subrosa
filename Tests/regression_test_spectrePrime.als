module Tests/regression_test_spectrePrime
open lcm_skeleton as lcm

// Spectre v1
//NOTE: There are two additional efrx loops that is not shown in the paper that would be ruled out in most consistency predicates.
pred t1[] {#Event = 5 and #Branch = 1 and #Read = 3 and #Write = 1}
pred t2[] {#Address = 2 and #XState=3}
pred t3[] {#po=1 and #eo=3}
pred t4[] {#addr = 1 and #erfx = 2 and #ecox = 3 /*and #efrx = 3*/ and #rf_init =1  and #rf=0 and #co=0 and #fr=0}
pred t5[] {
some a0 : Address| some a1 : Address | some s0 : XState | some s1 : XState | some s2: XState | 
some r1 : Read | some r2 : Read | some r3 : Read | some w : Write  | some br : Branch | 
  a0 != a1 and s0 != s1 and s1 != s2 and s0 != s2 and r1 != r2 and r1 != r3 and r2 != r3 and
  (br.xstate_access.xstate = s2) and (w.address = a1) and (w.xstate_access.xstate = s1) and (r1.address = a0) and (r1.xstate_access.xstate = s0)
  and (r2.address = a1) and (r2.xstate_access.xstate = s1) and (r3.address = a1) and (r3.xstate_access.xstate = s1) and
  (br->r1 in eo) and (r1->w in eo) and (r2->r3 in eo) and (r2->r3 in po) and
  (r1->w in addr) and (r2 ->w in erfx)  and (w->r3 in erfx) and (r2->w in ecox) and (w->r3 in ecox) and (r2->r3 in ecox) and
  (r2->w in efrx) and (w->r3 in efrx) and (r2->r3 in efrx) and
  (r2->r3 in rf_init)
}

// Check if we can model the attack
//run{t1 && t2 && t3 && t4 && t5} for 5

// Check if our model captures the leakage
fact{t1 && t2 && t3 && t4 && t5}
check {not {some e:Event| some e':Event| not no_leakage[e,e']}} for 5

// Check if the leakage is caused by an intervening access or lacking extra architectural communication or both
//check {not {some e:Event| some e':Event| not {e != e' and e->e' in com_arch and same_xstate[e,e'] => (e->e' in ecomx)}}} for 5
//check {not {some e:Event| some e':Event| not {e != e' and e->e' in com_arch and same_xstate[e,e'] => (not intervening_access[e,e'])}}} for 5
