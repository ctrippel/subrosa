module mitigation
open lcm_perturbed as lcm

//Even though we have not defined what Fences do the following works because we assert that they do not use xstate which is a prerequisite for leakage in our definition

//Move to skeleton
fact {all f:Fences}

// A simple but naive strategy to prevent all leackage is to insert a fence after each instruction
pred simple_mitigation {
 all e : Event | {all e' : Event | e->e' in tfo implies (e = Fence or e' = Fence or {some e'' : Event | e'' = Fence and e->e'' in tfo and e''->e in tfo})}
}

//It is also possible to put fences in between data control transmissions.
pred simple_mitigation2 {
 all sink: Event | s_sink[sink] implies {all e' : Event |  e'->sink in dep implies }
}

// This should not work since the mitigation strategy prevents all lleakage
run mitigation {
  simple_mitigation &&   #data_leak > 0
} for 6
