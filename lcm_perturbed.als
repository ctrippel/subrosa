module lcm_skeleton

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  Specifying Leakage Containment Models Axiomatically (Programs + Candidate Executions)
//  This file contains basic memory model sets and relations and suggestions to extend MCMs to produce LCM


////////////////////////////////////////////////////////////////////////////////
// SECTION 0: Pertubations

// =Perturbations=
abstract sig PTag {}

one sig RE extends PTag {} // Remove Event
one sig RR extends PTag {} // Remove Relation
one sig RD extends PTag {} // Remove Dependency (RMW)

fun no_p : PTag->univ { // no_p - constant for no perturbation
  (PTag->univ) - (PTag->univ)
}


/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 1: Specify relevant sets (e.g., Address, Event, Read, Write, Fence) and relations (address, po, addr, rf, co)

sig Address {													// set of physical address objects representing shared memory locations
  //privilege_domain: one PrivilegeDomain			// OPTIONAL, uncomment to use
																	// there is no leakage between members of the same privilige domain
}

sig XState { }												// extra-architectural state locations

abstract sig Event {										// set of instruction objects representing assembly language program instructions
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
fact po_connect { all e : Event | all e':Event |  (e->e' in ^tfo and e in Event.~po and e' in Event.po) implies (e->e' in ^po+^~po)}

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
fact rf_init_initialize {first_initialization_access[Event.rf_init] and initialization_access[rf_init.Event]}	// rf_init edges relate an first_initialisation_access to an initialisation_access
fact rf_init_domain {(MemoryEvent.rf_init+rf_init.MemoryEvent) in (Read+CacheFlush)}	// rf_init edges relate only non-write instructions
// if there is an initialization access in the same thread as a distinct first initialization access it they have to be related by rf_init
fact rf_init_total	{all e : (Read+CacheFlush) | 
						{some e':Event | disj[e,e'] and same_address[e,e'] and initialization_access[e']} and initialization_access[e] => e in (rf_init.Event+Event.rf_init)}

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

//dependencies (for now just consists of addr)
fun dep : Read->MemoryEvent { addr }
fact dep_in_tfo { dep in ^tfo }

//Performance optimizations
// Events that do not access architectural state nor extra-architectural state are ommitted since they are not interesting to our analysis
fact event_simplify {Event in xstate_access.XSAccess + MemoryEvent}
// XSAccess that are not connected to any Event are ommitted
fact xsaccess_simplify {XSAccess in Event.xstate_access}


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
fact constrain_frx { frx in XSReaders->XSWriters }

// If an instruction acts as a XRMW, i.e. both as a XRead and a XWrite, the XRead should happen before the XWrite, i.e. they should not be reordered. 
// This means that the XRead has to read either from initial state or from another XWrite that happens before the XWrite that is part of the XRMW. 
// Thus, there is a frx edge between the XRead and the XWrite.
fact xrmw_sc {xrmw in frx}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 4: Specify relevant interactions between MCM and LCM sets and relations

//relate po and tfo
fact po_in_tfo { po in ^tfo }	// po is a subset of ^tfo

//MemoryEvents that modify the same address should modify the same xstate
fact same_addr_in_same_xstate { address.~address in xstate_access.(xstate.~xstate).~xstate_access }		// same address events are also same state events

// committed events are events that are either related by po with other events or have an incoming or outgoing rf or fr edge
// Note that this definition does not work for one special cases (only one thread with a single instruction in it), these cases 
// can be ommitted safely though.
fun committed_events : Event { po.Event + Event.po + Event.(rf+fr+~rf+~fr) }
// speculative/transient events are events that are not committed.
fun transient_events : Event { Event - committed_events }

// assert that all commited event are connected by po if connected by tfo
fact commits_connect {all disj e,e': Event | (e in committed_events and e' in committed_events and e->e' in ^(tfo+~tfo))
	 implies (e->e' in ^(po+~po))}

//constrain com
fact com_in_committed {com in committed_events <:Event->Event:> committed_events}	// com relates committed events only

// initialization access
// an initialization access acts on memory to which no write has happened before in transient fetch order
pred initialization_access[e : Event]
  {e in MemoryEvent and {all e' : Write | (disj[e,e'] and event_commits[e']) implies not(tfo_tc[e',e] and same_address[e,e'])}}
// it is the first acces if there is no other initialization access that happens earlier in tfo order
pred first_initialization_access[e : Event] 
  { initialization_access[e] and 
  {all e' : Event | disj[e,e'] and e.address = e'.address  and initialization_access[e'] and same_thread[e,e'] => tfo_tc[e,e']}}


/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 5: Leakage

// =Leakage=

// An intervening access writes to the same xstate location as the two instructions related by a com_arch edge
pred intervening_access[e : Event, e' : Event]{
  e->e' in com_arch and 
 {some e'':Event| disj[e'',e] and disj[e'',e'] 
  and e->e'' not in  ^com_arch and e''->e' in ecomx 
  and e'' in eXSWriters}
}

// Whenever there is no corresponding comx edge for its respective com counterpart, the architectural communication is inconsistent with the extra-architecural communication
pred com_comx_consistent[e : Event, e' : Event]{
  (e->e' in rf implies e->e' in erfx)
  and (e->e' in co implies e->e' in ecox)
  and (e->e' in fr implies e->e' in efrx)
  and (e->e' in rf_init implies e->e' in erfx)
}

// leakage can only occur between two disjoint events if there is an intervening access or a com edge that is inconsistent with the respective comx counterpart
pred leakage[e : Event, e' : Event] {disj[e,e']  and (not com_comx_consistent[e,e'] or intervening_access[e,e'])}
pred leakage {some e, e' : Event | leakage[e,e']}
fun leak : Event -> set Event {{e,e' : Event| leakage[e,e']}}

// =Sink and Source instructions=

pred is_sink [e: Event] {some e':Event | leakage[e',e]}	// the sink is the instruction where information is leaked to
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
pred data_leakage [e:Event,sink:Event]{is_sink[sink] and sink->e in ^~ecomx.~addr /*and not leakage_is_benign*/}
fun data_leak : Event -> set Event {{e,sink : Event| data_leakage[e,sink]}}


/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 6: Pertubations
// =Model of memory, under perturbation=

//TODO: delete speculation primitive, all speculative executed instructions should be deleted
//TODO: only delete instructions that are not included in leakage
//TODO: use same way Dan Lustig's paper did with rf edges
//QUESTION: still to clarify is the state of the initial state and if it changes anything if we don't assume it to be 0 and 0 to be a "special" value anymore

//TODO: When do instructions change from xrmw to Read or Write?  -> Answer for now they don't 
//TODO: If speculative should always rf_init as well. 


//TODO: Silent store
//TODO: Add consistency predicate. TSO
//TODO: Check if Spectre v4 could be the result of deleting one element getting a new frx edge


//po and tfo
fun po_p[p: PTag->univ] : Event->Event {(Event-p[RE])  <: po :> (Event-p[RE]) + (po.(p[RE]) -> p[RE].po)}
fun tfo_p[p: PTag->univ] : Event->Event {(Event-p[RE])  <: tfo :> (Event-p[RE]) + (tfo.(p[RE]) -> p[RE].tfo)}


//com edges
// Accoring to our minimalisation criterion we won't try to delete instructions that are involved in a leakage relation. There should be no new leakage that is 
// introduced by deleting an instruction. 
// Therefore, we decide to use the same overapproximation as prior work when it comes to pertubations on rf edges. We delete all rf edges were one of the 
// endpoints is deleted completley. This works because we assume that if a Write that sources a Read is deleted that then the Read reads from initial state 
// instead. This is always possible since the intial state could have been the value that was written by the deleted Write. If the Read is deleted then there is 
// no rf edge by definition.
fun rf_p[p: PTag->univ] : Write->Read { (Write - p[RE]) <: rf :> (Read - p[RE])}
// For co edges the transitive structure allows the removal of an instruction with ease.
// In prior work ^co was used here because the authors did not insert that co is transitive.
fun co_p[p: PTag->univ] : Write->Write { (Write - p[RE]) <: co :> (Write - p[RE])}
// If any endpoint of an fr edge is deleted the fr edge is also deleted. However, there might be cases where it is reintroduced and other fr edges could be added.
// If a Write with an incoming fr edge to a Read is deleted, the Read now reads from initial state and fr edges are added from the Read to any Write in the program
// that is commited.  
// If a Read with an outgoing fr edge is deleted no new fr edges are introduced.
// If a Write that is the middle point of a ~rf.co path between the two endpoints is deleted, the deleted fr edges has to be reintroduced, because the Read will now read
// from the initial state.
fun fr_p[p: PTag->univ] : Read->Write {(Read - p[RE]) <: fr :> (Write - p[RE])
                                                               + (p[RE].rf) <: address.~address :> ((Write - p[RE]) & committed_events)
}
fun fr_original_p[p: PTag->univ] : Read->Write {(Read - p[RE]) <: fr :> (Write - p[RE])}
fun com_p[p: PTag->univ] : MemoryEvent->MemoryEvent { rf_p[p] + fr_p[p] + co_p[p] }
fun com_arch_p[p: PTag->univ] : MemoryEvent->MemoryEvent { rf_init_p[p] + com_p[p] }

// For rf_init edges there are two cases. If the first initialisation access is deleted
// the second initialisation_access becomes the first and all rf_init edges have to 
// be changed. Otherwise, the rf_init edge can just be deleted.
// However, if a rf edge is deleted but not the Read it will also read from initial state. 
// Thus, it becomes an initialisation access and might even be the first initialization access.
fun rf_init_p[p: PTag->univ] : MemoryEvent->MemoryEvent { 
  {{first_initialization_access_in_set_p [Event-p[RE],p]} <:Event->Event:> {Event.rf_init} - iden}
}

pred initialization_access_p[e : Event,p: PTag->univ]
  {disj[e,p[RE]] and e in MemoryEvent and 
  {all e' : (Write-p[RE]) | (disj[e,e'] and event_commits_p[e',p]) implies not(tfo_tc_p[e',e,p] and same_address[e,e'])}}

//TODO: either use => or implies everywhere

fun first_initialization_access_in_set_p [events : set Event,p: PTag->univ] : Event{
{e : Event |  initialization_access_p[e,p] and 
{all e' : events | (disj[e,e'] and e.address = e'.address  and initialization_access_p[e',p] and same_thread_p[e,e',p]  => tfo_tc_p[e,e',p])}}
}

pred event_commits_p[e: Event,p: PTag->univ] { e in committed_events }	// the event commits
fun committed_events_p[p: PTag->univ] : Event { po_p[p].Event + Event.(po_p[p]) + Event.(rf_p[p]+fr_p[p]+~(rf_p[p])+~(fr_p[p])) }

//comx edges 
fun erfx_p[p: PTag->univ] : Event->Event {(Event-p[RE]) <:(xstate_access.rfx).~xstate_access:> (Event-p[RE])}
fun ecox_p[p: PTag->univ] : Event->Event {(Event-p[RE]) <:(xstate_access.cox).~xstate_access:> (Event-p[RE])}
fun efrx_p[p: PTag->univ] : Event->Event {(Event-p[RE]) <:(xstate_access.frx).~xstate_access:> (Event-p[RE])
+  (p[RE].erfx) <: (xstate_access.frx).~xstate_access :> (eXSWriters_p[p])
}
fun ecomx_p[p: PTag->univ] : Event->Event {erfx_p[p] + ecox_p[p] + efrx_p[p]}	

fun eXSWriters_p[p: PTag->univ] : Event { eXSWrite + eXSRMW - p[RE]} // TODO the set of Writers might change when an event is delted? Or not?





// An intervening access writes to the same xstate location as the two instructions related by a com_arch edge
pred intervening_access_same[e : Event, e' : Event, p: PTag->univ]{
  e->e' in com_arch implies 
 {some e'' : Event | disj[e'',e] and disj[e'',e'] 
  and ((e''->e' in erfx implies e''->e' in erfx_p[p])
    or (e''->e' in ecox implies e''->e' in ecox_p[p])
    or (e''->e' in efrx implies e''->e' in efrx_p[p]))
  and (e'' in eXSWriters implies e'' in eXSWriters_p[p])
  and (e->e'' not in  ^com_arch implies  e->e'' not in  ^(com_arch_p[p]))
 }
and 
(e->e' in rf implies e->e' in rf_p[p])
and 
(e->e' in co implies e->e' in co_p[p])
and 
(e->e' in fr implies e->e' in fr_p[p])
and 
(e->e' in rf_init implies e->e' in rf_init_p[p])
}

// Whenever there is no corresponding comx edge for its respective com counterpart, the architectural communication is inconsistent with the extra-architecural communication
pred com_comx_consistent_same[e : Event, e' : Event, p: PTag->univ]{
  ((e->e' in rf and e->e' not in erfx) implies (e->e' in rf_p[p] and e->e' not in erfx_p[p]))
  and ((e->e' in co and e->e' not in ecox) implies (e->e' in co_p[p] and e->e' not in ecox_p[p]))
  and ((e->e' in fr and e->e' not in efrx) implies (e->e' in fr_original_p[p] and e->e' not in efrx_p[p]))
  and ((e->e' in rf_init and e->e' not in erfx) implies (e->e' in rf_init_p[p] and e->e' not in erfx_p[p]))
}

// leakage can only occur between two disjoint events if there is an intervening access or a com edge that is inconsistent with the respective comx counterpart
pred leakage_different[p: PTag->univ] 
{all e,e' : Event | leakage[e,e']  implies (not com_comx_consistent_same[e,e',p] or not intervening_access_same[e,e',p])}

//TODO: Check what this does if there is intervening access and com_comx_inconsistency.

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 6: Run Alloy

let interesting_not_axiom{
  leakage

  // All events must be relevant and minimal
  // Minimal: Every relaxation removes all original leakage from the program
  all e: Event | leakage_different[RE->e]
}

run leakage1 {
  interesting_not_axiom[] and #Event > 3 and #leak=1
} for 4


//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Alloy shortcuts=
pred transitive[rel: (Event+XSAccess)->(Event+XSAccess)]        { rel.rel in rel }
pred irreflexive[rel: (Event+XSAccess)->(Event+XSAccess)]       { no iden & rel }
pred acyclic[rel: (Event+XSAccess)->(Event+XSAccess)]           { irreflexive[^rel] }
pred total[rel: (Event+XSAccess)->(Event+XSAccess), bag: (Event+XSAccess)] {
  // all unique event are part of the relation and the relation is acyclic
  all disj e, e': bag | e->e' in rel + ~rel
  acyclic[rel]
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =LCM shortcuts=
// program and transient fetch order
pred po_tc[e : Event, e' : Event] { e->e' in ^po }	// e happens before e' in program order
pred tfo_tc[e: Event, e': Event] { e->e' in ^tfo }	// e happens before e' in transient fetch order
pred same_address[e : Event, e' : Event] { e.address = e'.address }	// both events access the same adress
pred same_xstate[e : Event, e' : Event] {e.xstate_access.xstate = e'.xstate_access.xstate}	// both events access the same xstate
pred same_thread[e : Event, e' : Event] { e->e' in (iden + ^tfo + ^~tfo)}	// both events are in the same thread
pred event_commits[e: Event] { e in committed_events }	// the event commits
pred event_transients[e: Event] { e in transient_events }	// the event does not commit

// under pertubation
// Note: with the current definition of po_p and tfo_p this is actually not needed.
pred po_tc_p[e : Event, e' : Event, p: PTag->univ] { e->e' in ^(po_p[p]) }	// e happens before e' in program order
pred tfo_tc_p[e: Event, e': Event, p: PTag->univ] { e->e' in ^(tfo_p[p]) }	// e happens before e' in transient fetch order
pred same_thread_p[e : Event, e' : Event, p: PTag->univ] { e->e' in (iden + ^(tfo_p[p]) + ^~(tfo_p[p]))}	// both events are in the same thread

// There are three cases why an fr edge might exist
// 1. fr edge outgoing from an event that reads from initial state 
// 2. fr edge between two events that are connected both by rf and co
// 3. fr edge because there is a ~rf.co path that uses an event distinct from start and end events of the fr edge
// In case 1 and 2, deleting an endpoint of an fr edge causes deleting the fr edge itself
// In case 3, the edge is additionally deleted if the event in the middle is deleted.
