module lcm_skeleton

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  Specifying Leakage Containment Models Axiomatically (Programs + Candidate Executions)
//  This file contains basic memory model sets and relations and suggestions to extend MCMs to produce LCM

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 1: Specify relevant sets (e.g., Address, Event, Read, Write, Fence) and relations (address, po, addr, rf, co)

sig Address {													// set of physical address objects representing shared memory locations
  //privilege_domain: one PrivilegeDomain			// OPTIONAL, uncomment to use
																	// there is no leakage between members of the same privilige domain
}

sig XState { }												// extra-architectural state locations

abstract sig Event {	   								    // set of instruction objects representing assembly language program instructions
  po: lone Event,											// set of tuples of the form (Event, Event) which map each instruction object in Event 
																	// to the instruction sequencing of committed instructions
  tfo: lone Event,											// set of tuples of the form (Event, Event) which map each instruction object in Event 
																	// to the sequence of instructions in which they began execution
  xstate_access: lone XSAccess						// extra-architectural state accesses
}

abstract sig XSEventType { }						// extra-architectural state types
one sig XRead extends XSEventType {}			// xstate access can behave as "read"
one sig XWrite extends XSEventType { }		// and/or "write"

sig XSAccess{
  xstate: one XState,										// set of tuples of the form (XStateAccess, XState) which map each XStateAccess to the one
																	// XState element that it accesses.
  xstate_event_type: some XSEventType,			// set of tuples of the form (XStateAccess, XSEventType) which map each XStateAccess to the 
																	// behavior it shows when accessing the xstate specified through xstate_access.
  rfx: set XSAccess,											// rf lifted to Events
  cox: set XSAccess											// co lifted to Events
}

fun xrmw : XSAccess->XSAccess {					// In case that a XSAccess has both type XRead and XWrite it is an XRMW
  xstate_event_type.XRead ->xstate_event_type.XWrite
  & iden
}

abstract sig MemoryEvent extends Event{		// set of instruction objects representing assembly language program instructions which access architectural state
  address: one Address,									// set of tuples of the form (Event, Address) which map each MemoryEvent to the one Address that it accesses
  rf_init : set MemoryEvent								// memory accesses might read from the initial state of the memory
}

sig Read extends MemoryEvent {					// Read is a subset of MemoryEvents that is disjoint from Write and CacheFlush
  addr : set MemoryEvent,								// address dependency relation, relates a Read to a po-subsequent MemoryEvent when the value accessed by that event syntactically depends on the value returned by the Read
  data : set MemoryEvent,								// data dependency relation, relates a Read to a Write whose value depends on the value read
  control : set MemoryEvent,							// control dependency relation, relates a Read to instructions following a conditional branch whose condition involved the value read
  fr: set Write													// from-reads relation
}

sig Write extends MemoryEvent {					// Write is a subset of MemoryEvents that is disjoint from Read
  rf: set Read,												// reads-from relation, relates each Write to all same-address Reads it sources
  co: set Write												// coherence-order relation, relates all Writes to all Writes that follow it in coherence order 
}

// Additional Events

sig Branch extends Event {}							// Branches are Events that access xstate
fact branch_has_xstate {all b : Branch | one {b.xstate_access}}

sig Jump extends Event {}							// Jumps are Events that access xstate
fact branch_has_xstate {all j : Jump | one {j.xstate_access}}

abstract sig Fence extends Event { }			// Fences are Events that do not access xstate
fact fence_has_no_xstate {Fence.xstate_access = none}

sig CacheFlush extends MemoryEvent { }		// CacheFlushes are special Memory Events
fact cf_has_xstate {all c : CacheFlush | one {c.xstate_access}}

sig REG extends Read {}								// REG operations are special reads that access xstate but don't share a memory location or xstate with other instructions
fact reg_has_xstate{all r : REG | one {r.xstate_access}}
fact reg_no_shared_xstate {all r : REG | all e : Event | disj[e,r] implies disj[e.xstate_access.xstate,r.xstate_access.xstate]}
fact reg_no_shared_memory {all r : REG | all e : Event | disj[e,r] implies disj[e.address,r.address]}
fact reg_no_rf_init {all r : REG | all e : Event | disj[rf_init.r,e] and disj[r.rf_init,e]}


/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 2: Constrain memory consitency model relation

//po
fact po_acyclic { acyclic[po] }							// po is acyclic
fact po_prior { all e : Event | lone e.~po }		// all events are related to 0 or 1 events by po
// If there are several instructions related by po in a thread there is exactly one sequence connecting all them by po
fact po_connect { all e1, e2 : Event |  (e1->e2 in ^tfo and e1 in Event.~po and e2 in Event.po) implies (e1->e2 in ^po+^~po)}

//com
fun com : MemoryEvent->MemoryEvent { rf + fr + co }	// com edges are all rf, fr and co edges
fact com_in_same_addr { com in address.~address }		// com edges only relate same address instructions

//coherence-order
fact co_transitive { transitive[co] }																				// co is transitive
fact co_total { all a : Address | total[co, a.~address & (committed_events & Write)] }		// co is total
fact co_commited {all e : Event | event_commits[e.co] and event_commits[co.e]}			// co relates commited events only

//reads-from
fact lone_source_write { rf.~rf in iden }	// each read has a single source over rf

//reads-from-init
// we conservatively assume that a sequential order is enforced here
fact rf_init_in_tfo {rf_init in ^tfo}	// rf_init follows transient fetch order 
fact rf_init_in_same_addr {rf_init in address.~address}	// rf_init edges only relate same address instructions
fact rf_init_in_same_thread {same_thread[rf_init.Event,Event.rf_init]}	// rf_init edges only relate instructions in the same thread
fact rf_init_initialize {{all e: Event | e in rf_init.Event implies first_initialization_access[e]} and 
                                 {all e: Event | e in Event.rf_init implies initialization_access[e]}}	// rf_init edges relate an first_initialisation_access to an initialisation_access
fact rf_init_domain {(MemoryEvent.rf_init+rf_init.MemoryEvent) in (Read+CacheFlush)}	// rf_init edges relate only non-write instructions
// if there is an initialization access in the same thread as a distinct first initialization access it they have to be related by rf_init
fact rf_init_total  {all e1 : (Read+CacheFlush) | {some e2:Event | disj[e1,e2] and same_address[e1,e2] and initialization_access[e2]} and initialization_access[e1] implies e1 in (rf_init.Event+Event.rf_init)}
//com_arch edges 
fun com_arch : MemoryEvent->MemoryEvent { rf_init + com }	// com_arch edges are all rf_init and com edges

//constrain fr edges
// from-reads (fr) relates each Read to all co-sucessors of Write that it read from it including Reads that read from the initial state
// Some events have to be necessarily connected by fr. This includes all Reads and all co-sucessors of Write that read from it and
// all Reads that read from initial state if they are necessarily committed.
fact fr_min {~rf.co + (((Event.po + po.Event) & Read)-((Event.po + po.Event) & Write).rf) <: address.~address :> ((Event.po + po.Event) & Write) in fr} 
// all other events can be connected by fr but do not have to. This includes Reads that read from initial state as well. However, 
// if an event is not committed there is no fr edge incident to it. 
fact fr_max {fr in ~rf.co + (Read-Write.rf) <: address.~address :> Write}	
// If a Read has an outgoing fr edge it is committed and thus has to be connected to all subsequent Writes and not only to some
fact fr_connect {all e : Read | all w : Write | (same_thread[e,w] and event_commits[e] and same_address[e,w]) implies e->w in fr}

//dependencies
fact data_domain {Event.data in Write}
fact control_branch {#control > 0 implies {some b : Branch  |  control.Event->b in ^tfo and b->Event.control in ^tfo}}
fun dep : Read->MemoryEvent { addr + control + data}
fact dep_in_tfo { dep in ^tfo }

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 3: Constrain leakage containment model relations

//xstate_access
fact xstate_access_inj {xstate_access.~xstate_access in iden}	// Each XSAccess can only be related to one instruction

//tfo
fact tfo_acyclic { acyclic[tfo] }						// tfo is acyclic
fact tfo_prior { all e : Event | lone e.~tfo }		// all events are related to 0 or 1 events by tfo

//comx
fun comx : XSAccess -> XSAccess { rfx + frx + cox }	// comx edges are all rfx, frx and cox edges
fact comx_in_same_xstate { comx in xstate.~xstate }	// comx edges can only relate instructions with the same xstate

//lifting comx functions to event level
fun erfx : Event->Event {(xstate_access.rfx).~xstate_access}		// rfx on Events
fun ecox : Event->Event {(xstate_access.cox).~xstate_access}		// cox on Events
fun efrx : Event->Event {(xstate_access.frx).~xstate_access}		// frx on Events
fun ecomx: Event->Event {(xstate_access.comx).~xstate_access}	// comx on Events

//helper functions
fun XSRead : XSAccess { xstate_event_type.XRead }
fun XSWrite : XSAccess { xstate_event_type.XWrite }
fun XSRMW : XSAccess { xstate_event_type.XRead & xstate_event_type.XWrite}
fun XSReaders : XSAccess { XSRead+ XSRMW }
fun XSWriters : XSAccess { XSWrite + XSRMW }

//lifting helper functions to event level
fun eXSRead : Event { xstate_access.xstate_event_type.XRead }
fun eXSWrite : Event { xstate_access.xstate_event_type.XWrite }
fun eXSRMW : Event { xstate_access.xstate_event_type.XRead & xstate_access.xstate_event_type.XWrite}
fun eXSReaders : Event { eXSRead+ eXSRMW }
fun eXSWriters : Event { eXSWrite + eXSRMW }

//constrain events
fact constrain_write {Write in eXSRead + eXSRMW}						// Writes are always either reads or read modify write
fact constrain_cacheFlush {CacheFlush in eXSRead + eXSRMW}		// CacheFlushs are always either reads or read modify write
fact constrain_read {Read in eXSRead + eXSRMW}						// Reads are always either reads or read modify write
fact constrain_branch {Branch in eXSRead + eXSRMW}					// Branch are always either reads or read modify write

//rfx
fact constrain_rfx { rfx in XSWriters->XSReaders } 						// rfx edges relates instruction that write to xstate to instructions that read from it 
fact lone_source_writex { rfx.~rfx in iden }									// each instruction has at most a single source over rfx

//cox
fact cox_transitive { transitive[cox] }											// cox edges are transitive
fact cox_total { all s: XState | total[cox, s.~xstate & XSWriters] }	// cox is total 
fact constrain_cox { cox in XSWriters->XSWriters }						// cox related instructions that write to xstate to instructions that write to it 
fact cox_acyclic { acyclic[cox] }													// cox is acyclic

//frx
// in contrast to fr edges, frx edges can be uniquely given by a function that comprises:
fun frx : XSAccess->XSAccess {
  ~rfx.cox																					// all edges between events that read xstate that another event e has written to to all 
																								// predecessor that wrote to xstate before e
  +
  ((XSReaders - (XSWriters.rfx)) <: (xstate.~xstate) :> XSWriters)  // and all events that read from the initial state of the xstate element they access
}

// If an instruction acts as a XRMW, i.e. both as a XRead and a XWrite, the XRead should happen before the XWrite, i.e. they should not be reordered. 
// This means that the XRead has to read either from initial state or from another XWrite that happens before the XWrite that is part of the XRMW. 
// Thus, there is a frx edge between the XRead and the XWrite.
fact xrmw_sc {xrmw in frx}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 4: Specify relevant interactions between MCM and LCM sets and relations

//relate po and tfo
fact po_in_tfo { po in ^tfo }	// po is a subset of ^tfo

// A speculation primitive (SP) is an event that starts a speculative execution
fun speculation_primitive : Event {Event.po & tfo.Event - po.Event}

//MemoryEvents that modify the same address should modify the same xstate
fact same_addr_in_same_xstate { address.~address in xstate_access.(xstate.~xstate).~xstate_access }		// same address events are also same state events

// committed events are events that are either related by po with other events or have an incoming or outgoing rf or fr edge
// TODO: why are co edges not included
// Note that this definition does not work for one special cases (only one thread with a single instruction in it), these cases 
// can be ommitted safely though.
fun committed_events : Event { po.Event + Event.po + Event.(rf+fr+~rf+~fr) }
// speculative/transient events are events that are not committed.
fun transient_events : Event { Event - committed_events }

// assert that all commited event are connected by po if connected by tfo
fact commits_connect {all disj e1,e2: Event | (e1 in committed_events and e2 in committed_events and e1->e2 in ^(tfo+~tfo))
	 implies (e1->e2 in ^(po+~po))}

//constrain com
fact com_in_committed {com in committed_events <:Event->Event:> committed_events}	// com relates committed events only

// initialization access
// an initialization access acts on memory to which no write has happened before in transient fetch order
pred initialization_access[e1 : Event]
  {e1 in MemoryEvent and {all e2 : Write | (disj[e1,e2] and event_commits[e2]) implies not(tfo_tc[e2,e1] and same_address[e1,e2])}}
// it is the first access if there is no other initialization access that happens earlier in tfo order
pred first_initialization_access[e1 : Event] 
  { initialization_access[e1] and 
  {all e2 : Event | disj[e1,e2] and e1.address = e2.address and initialization_access[e1] and same_thread[e1,e2] implies tfo_tc[e1,e2]}}


/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 5: Leakage

// =Leakage=

// An intervening access writes to the same xstate location as the two instructions related by a com_arch edge
pred intervening_access[e1 : Event, e2 : Event]{
  e1->e2 in com_arch and 
 {some e3:Event| disj[e3,e1] and disj[e3,e2] 
  and e1->e3 not in  ^com_arch and e3->e1 in ecomx 
  and e3 in eXSWriters}
}

// Whenever there is no corresponding comx edge for its respective com counterpart, the architectural communication is inconsistent with the extra-architecural communication
pred com_comx_consistent[e1 : Event, e2 : Event]{
  (e1->e2 in rf implies e1->e2 in erfx)
  and (e1->e2 in co implies e1->e2 in ecox)
  and (e1->e2 in fr implies e1->e2 in efrx)
  and (e1->e2 in rf_init implies e1->e2 in erfx)
}

// leakage can only occur between two disjoint events if there is an intervening access or a com edge that is inconsistent with the respective comx counterpart
pred leakage[e1 : Event, e2 : Event] {disj[e1,e2]  and (not com_comx_consistent[e1,e2] or intervening_access[e1,e2])}
pred leakage {some e1, e2 : Event | leakage[e1,e2]}
fun leak : Event -> set Event {{e1,e2 : Event| leakage[e1,e2]}}

// =Sink and Source instructions=
pred is_sink [e1: Event] {some e2 : Event | leakage[e1,e2]}			// the sink is the instruction where information is leaked to
fact sink_is_committed {all e : Event | is_sink[e] implies event_commits[e] }	// the sink instruction has to be a committed argument

// A candidate source is always defined with respect to the sink(s) it leaks too. Any instruction related to the sink by comx is a candidate of a source for leakage. 
pred is_candidate_source [e:Event,sink:Event]{disj[e,sink] and is_sink[sink] and sink->e in ^~ecomx}

// =Privilege Domains=
// OPTIONAL, uncomment to use. Also uncomment in Event, xstate_leakage and data_leakage
// Privilige domains allow users to declare that certain leakage is benign, e.g. from an attacker controlled instruction to another attacker controlled instruction

/*abstract sig PrivilegeDomain{}	// a set of privilege domains
one sig AttackerControlled extends PrivilegeDomain{}	// to showcase the usage two domains are defined here, one is attacker controlled, the other one is victim controlled
one sig VictimControlled extends PrivilegeDomain{}		// one could assert here that all instructions accessing the same memory address are in the same domain, etc.
// leakage is only malicious if two instructions are not in the same privilege domain
pred leakage_is_benign[e:Event,sink:Event] {e.address.privilege_domain=sink.address.privilege_domain}*/

// =Identify what leaks=

// Leakage exists between a sink and its candidate sources
pred xstate_leakage[source:Event,sink:Event] {is_sink[sink] and is_candidate_source[source,sink] /*and not leakage_is_benign*/}

// Data leakage occurs because of addr dependencies
pred data_leakage [e:Event,sink:Event]{is_sink[sink] and sink->e in ~^erfx.~addr /*and not leakage_is_benign*/}
fun data_leak : Event -> set Event {{e,sink : Event| data_leakage[e,sink]}}

// Some leakage is due to speculative execution
pred speculative_leakage{speculation_primitive in leak.Event}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 6: Consistency and Confidentialiy predicate
// =TSO consistency predicate=

fun po_loc : MemoryEvent->MemoryEvent { ^po & address.~address }		// connects all same address events in program order
fun tfo_loc : MemoryEvent->MemoryEvent { ^po & address.~address }		// connects all same address events in transient fetch order
fun rfi : MemoryEvent->MemoryEvent{{e1, e2 : MemoryEvent | e1->e2 in rf and same_thread[e1,e2]}}
fun rfxi : MemoryEvent->MemoryEvent{{e1, e2 : MemoryEvent | e1->e2 in erfx and same_thread[e1,e2]}}
fun rfe: MemoryEvent->MemoryEvent { rf - rfi}
fun rfxe: MemoryEvent->MemoryEvent { erfx - rfxi}
fun ppo: MemoryEvent->MemoryEvent {^po & (Write->Write + Read->Write + Read->Read)}
fun ptfo: MemoryEvent->MemoryEvent {^tfo & (Write->Write + Read->Write + Read->Read)}
//fun mfence: Event->Event {{e1,e2:Event| all f: Fence| e1->f in ^tfo and f->e2 in ^tfo}} //TODO

pred sc_per_loc {acyclic[rf + co + fr + po_loc]}
//We don't allow atomic rmw instructions. Thus, rmw_actomicity is not considered here.
pred causality {acyclic[rfe + co + fr + ppo]} //+ mfence]}
pred consistency_predicate {sc_per_loc and causality}

pred sc_per_loc_x {acyclic[rfx + cox + tfo_loc] and acyclic[rfx + cox + frx]}
pred causality_x {acyclic[rfxe + cox + frx + ptfo]}
pred confidentiality_predicate {sc_per_loc_x and causality_x}

fact tso {consistency_predicate and confidentiality_predicate}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 7: Performance optimizations and Options

// Events that do not access architectural state nor extra-architectural state are ommitted since they are not interesting to our analysis
pred event_simplify {Event in xstate_access.XSAccess + MemoryEvent}
// XSAccess that are not connected to any Event are ommitted
pred xsaccess_simplify {XSAccess in Event.xstate_access}
// Data and control edges do not contribute to leakage in any way.
pred delete_dep {no data and no control}

// Performance optimization. If behavior is wanted to delete here.
fact{event_simplify and xsaccess_simplify and delete_dep}

// Turn off or on different speculation primitives
//fact {#(speculation_primitive & Branch) = 0}
//fact {#(speculation_primitive & Write) = 0}
//fact {#(speculation_primitive & CacheFlush) = 0}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 8: Run Alloy

//E.g., find models that feature leakage
run{
   #leak > 0
}

//E.g., find models that feature leakage between two Reads
run{
  some e1 : Read | some e2 : Read | leakage[e1,e2]
}

//E.g., find models that feature data_leakage
run{
   #data_leak > 0
}


//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Alloy shortcuts=
pred transitive[rel: (Event+XSAccess)->(Event+XSAccess)]        { rel.rel in rel }
pred irreflexive[rel: (Event+XSAccess)->(Event+XSAccess)]       { no iden & rel }
pred acyclic[rel: (Event+XSAccess)->(Event+XSAccess)]           { irreflexive[^rel] }
pred total[rel: (Event+XSAccess)->(Event+XSAccess), bag: (Event+XSAccess)] {
  // all unique event are part of the relation and the relation is acyclic
  all disj e1, e2: bag | e1->e2 in rel + ~rel
  acyclic[rel]
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =LCM shortcuts=
// program and transient fetch order
pred po_tc[e1 : Event, e2 : Event] { e1->e2 in ^po }	// e1 happens before e2 in program order
pred tfo_tc[e1: Event, e2: Event] { e1->e2 in ^tfo }	// e1 happens before e2 in transient fetch order
pred same_address[e1 : Event, e2 : Event] { e1.address = e2.address }	// both events access the same adress
pred same_xstate[e1 : Event, e2 : Event] {e1.xstate_access.xstate = e2.xstate_access.xstate}	// both events access the same xstate
pred same_thread[e1 : Event, e2 : Event] { e1->e2 in (iden + ^tfo + ^~tfo)}	// both events are in the same thread
pred event_commits[e1: Event] { e1 in committed_events }	// the event commits
pred event_transients[e1: Event] { e1 in transient_events }	// the event does not commit
