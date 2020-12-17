module x86_lcm_skeleton
open lcm_skeleton

// we have to have these conflict sets for extra-architectural state
// rather than specifying the elements of the micro-architecture, 
// we just specify the instrutions that can communicate

// specify XState buckets
sig cache extends XState { }

// define how micro-ops can interact with xstate
fact { all r: Read | 
	r.xstate in cache and
	r.xstate in cache => r.xstate_event_type in XRead + XRMW
}

fact { all w: Write |
	w.xstate in cache and // + mm and
	w.xstate in cache => w.xstate_event_type in XRead + XRMW // and
	// w.xstate in mm => w.xstate_event_type in XWrite
}

// TODO: move to x86_lcm file and define there since these are arechitecture-specific
// sig mfence extends Fence { }
// sig lfence extends Fence { }

// conditional branches
// sig Branch extends XSEvent { 
//	branch: set Event
// }

// fact branch_relation { all b: Branch | all e: Event | execution_order[b, e] and not program_order[b, e] and (no e': Event | program_order[b, e'] and execution_order[e', e]) <=> b->e in branch }

fact write_allocate { all w: Write | w.xstate_event_type = XRead <=> not event_commits[w] }

fact read_hits {
	all w: XStateWriters |						// Writes or RMWs to xstate
		no r: Read |								// Read of xstate
			r in XStateRMW and				// that is a RMW
			same_address[w, r] and
			w->r in rfx and
			eo_tc[w, r]
}

// define speculation primitives (Microsoft terminology); we allow an unbounded speculation window
pred exception_deferral[e: Event] { all e': MemoryEvent | same_address[e', e] => not event_commits[e'] }
// pred memory_access_mispred[e: Event] { some e' : e.frx | eo_tc[e', e] }

fact squash_memory_access_mispred { all e: MemoryEvent | memory_access_mispred[e] => not event_commits[e] }
fact squash_dep { all e: MemoryEvent | e in squashed_events.dep => e in squashed_events }

pred speculation_primitives { 
	all e: squashed_events |
		exception_deferral[e] or
		// memory_access_mispred[e] or
		e in squashed_events.dep
}

// define the MCM
fun po_loc : MemoryEvent->MemoryEvent { ^po & address.~address }		
fun rfe: Write->Read { rf - (^po + ^~po) }		
fun rfi: Write->Read { rf - rfe}
fun fence : MemoryEvent->MemoryEvent { (MemoryEvent <: *po :> mfence).(mfence <: *po :> MemoryEvent) }
fun ppo : MemoryEvent->MemoryEvent { ^po - Write->Read }
pred location_sc { acyclic[com + po_loc] }	
// pred atomicity   { no (fr.co) & rmw }
pred mca { acyclic[rfe + co + fr + ppo + fence] } 
//pred tso_mm { location_sc and atomicity and mca }
pred mca { acyclic[rfe + co + fr + ppo] } 
pred tso_mm { location_sc and mca }


// define the LCM
fun eo_loc : MemoryEvent->MemoryEvent { ^eo & address.~address }		// same address accesses in eo
// fun fence_lfence : XStateEvent->XStateEvent { (XStateEvent <: *eo :> lfence).(lfence <: *eo :> XStateEvent) }
// fun store_bypass : XStateEvent->XStateEvent { frx - (( (Read & XStateRead) <: frx ) & (address.~address)) } 
//pred mcax { acyclic[cox + rfx + store_bypass + eo] }
//pred mcaxc { acyclic[coxc + rfxc + frxc + store_bypass + eo] }
pred mcax { acyclic[cox + rfx + eo] }
pred mcaxc { acyclic[coxc + rfxc + frxc + eo] }
//pred x86_lcm { xstate_actions and conflict_sets and speculation_primitives and spec_fence and mcax }
pred x86_lcm { speculation_primitives and mcax and mcaxc }
pred mcm_lcm { tso_mm and x86_lcm } 

//pred lfence_fix { ( all e : eo.Event | e not in lfence <=> (some l : lfence | e->l in eo )) and (no lfence & (Event - Event.eo)) and (no lfence & (Event - eo.Event)) }

run ilamcm { mcm_lcm and disclosure_primitive } for 5 //  and some e: Event | memory_access_mispred[e] } for 5




//fact { all r: Read | 
//	~(r.xstate_actions).XStateAccessType = cache + mm and 
//	r.state_actions.cache = XRead + XRMW and
//	r.state_actions.mm = XRead
//}

// fact { all w: Write |
//	~(w.xstate_actions).XStateAccessType = cache + mm and
//	w.state_actions.cache = XRead + XRMW and
//	w.state_acations.cache = XRMW
//} 

//pred write_xstate_actions { all w: Write | w in StateReaders } 	// Writes can only be RMWs or Reads
//pred read_xstate_actions { all r:  Read | r in StateReaders }		// Reads can be RMWs or Reads
//pred jump_xstate_actions { all j: Jump | j in StateRMW }
//pred branch_xstate_actions { all b: Branch | b in StateRMW }


// define rfx conflict sets
// relates micro-ops that write xstate to micro-ops that read xstate
//pred rfx_conflict_sets { rfx in
//	Read->Read +
//	Read->Write +
//	Write->Read +
//	Write->Write +
//	Jump->Jump //+
//	//Branch->Branch
//}

//pred cox_conflict_sets { cox in
//	Read->Read +
//	Read->Write +
//	Write->Read +
//	Write->Write +
//	Jump->Jump //+
//	//Branch->Branch
//}



//fact write_in_reads {
//	all s: StateWriters |
//		all w: Write |
//			s->w in rfx and
//			same_address[s, w] and
//			execution_order[s, w] and
//			not program_order[s, w]
//			=> w in StateRead
//}

// add something where you can't have exception deferral ->dep with other po intervening 





// and some (frx & ~eo) } for 3


// should this be same_state instead of same_address? probably need to do testing to figure this ut

//pred indirect_branch_mispred[e: Event] { some j: Jump | execution_order[j, e] and not program_order[j, e] and (no e': Event | program_order[j, e'] and execution_order[e', e]) }
//pred conditional_branch_mispred[e: Event] { some b: Branch | execution_order[b, e] and not program_order[b, e] and (no e': Event | program_order[b, e'] and execution_order[e', e]) }

//and some dep }//lfence_fix} // some (frx & ~eo) and  //and #rfx=2 #po=1 and #eo=2 #Read=2 and #Write=1 and #StateRead=1 and some (Read & StateRMW & (Event - Event.eo)) and some (po & Read->Write)} //lfence_fix} //and #eo=2} //and #(Read & StateRMW)=2} //and no Jump and no CacheFlush } // and lfence_fix }
 //and no ((comx + ~comx) & fence_lfence)}
// (fence_lfence & comx) in ^po }
//fact { all s: StateRMW | all s': Read | s->s' in po and (s'.address = s.address) => s->s' in rfx }
//fact { all e : Jump | e in StateRMWs }
//fact { all e: CacheFlush | e in StateReads }	
//fact { all e: CacheFlush | e in StateRMWs => (some e': StateEvent | e'->e in rfx) }
//fact { all e: CacheFlush | all e': StateEvent | (e in StateRMWs and e->e' in rfx) => e' in StateRMWs }
//fact { no e, e' : StateRead | e in  }
//fact cache_hits { no cox & (eo & ({ Write } <: address.~address :> { Read })) }
// cache misses?

//pred x86_lcm { {comx + (dep - (dep & ^po)) } not in fence_lfence and  locationx_sc }


//fact { no (Event - Event.eo) & Fence }
//fact { no (Event - eo.Event) & Fence }
//fact { no disj e, e': Event | e->e' in eo and e in lfence and e' in lfence }
//pred lfence_fix { all disj e, e': Event | e not in lfence and e' not in lfence and execution_order[e, e'] => (one l: lfence | execution_order[e, l] and execution_order[l, e']) }

//rfx conflict sets
	//Read->CacheFlush +
	//Write->CacheFlush +
	//CacheFlush->Read +
	//CacheFlush->Write +
	//CacheFlush->CacheFlush +

//cox conflict sets
	//Read->CacheFlush +
	//Write->CacheFlush +
	//CacheFlush->Read +
	//CacheFlush->Write +
	//CacheFlush->CacheFlush +
