module lcm_skeleton

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  Specifying Leakage Containment Models Axiomatically (Programs + Candidate Executions)
//  This file contains basic memory model sets and relations and suggestions to extend MCMs to produce LCM

/////////////////////////////////////////////////////////////////////////////////////////////////////////////

// SECTION 1: Specify relevant sets (e.g., Address, Event, Read, Write, Fence) and relations (address, po, addr, rf, co)

sig Address { }							// set of physical address objects representing shared memory locations
sig XState { }							// extra-architectural state locations

sig Event {							// set of instruction objects representing assembly language program instructions
  po: lone Event,						// set of tuples of the form (Event, Event) which map each instruction object in Event 
									// to the instruction sequencing of committed instructions
  eo: lone Event,						// set of tuples of the form (Event, Event) which map each instruction object in Event 
									// to the sequence of instructions in which they began execution
  xstate_access: lone XSAccess				// extra-architectural state accesses
									// TODO: will be changed to set later
}

abstract sig XSEventType { }				// extra-architectural state types
one sig XRead extends XSEventType {}		// xstate access can behave as "read" and/or "write"
one sig XWrite extends XSEventType { }

sig XSAccess{
  xstate: one XState,						// set of tuples of the form (XStateAccess, XState) which map each XStateAccess to the one
									// XState element that it accesses.
  xstate_event_type: some XSEventType,		// set of tuples of the form (XStateAccess, XSEventType) which map each XStateAccess to the 
									// behavior it shows when accessing the xstate specified through xstate_access.
  rfx: set XSAccess,						// rf lifted to Events
  cox: set XSAccess						// co lifted to Events
}

fun xrmw : XSAccess->XSAccess {			// In case that a XSAccess has both type XRead and XWrite it is an XRMW
  xstate_event_type.XWrite ->xstate_event_type.XRead
  & iden
}

abstract sig MemoryEvent extends Event{		// set of instruction objects representing assembly language program instructions which access architectural state
  address: one Address,					// set of tuples of the form (Event, Address) which map each MemoryEvent to the one Address that it accesses
  rf_init : set MemoryEvent					// memory accesses might read from the initial state of the memory
}

sig Read extends MemoryEvent {			// Read is a subset of MemoryEvents that is disjoint from Write and CacheFlush
  addr : set MemoryEvent,					// address dependency relation, relates a Read to a po-subsequent MemoryEvent when the value accessed by that event syntactically depends on the value returned by the Read
  fr: set Write							// from-reads relation
  // TODO: add data, crtrl later
  // data : set Write,
  // ctrl : set MemoryEvent
}

sig Write extends MemoryEvent {			// Write is a subset of MemoryEvents that is disjoint from Read
  rf: set Read,							// reads-from relation, relates each Write to all same-address Reads it sources
  co: set Write							// coherence-order relation, relates all Writes to all Writes that follow it in coherence order 
}

sig CacheFlush extends MemoryEvent { }		// CacheFlush is a subset of Memory Event

//abstract sig Fence extends Event { }			// Fence is a subset of Event, since it does not have xstate intractions with other instructions

//abstract sig Jump extends Event {}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 2: Constrain memory consitency model relation

//po
fact po_acyclic { acyclic[po] }				// po is acyclic
fact po_prior { all e : Event | lone e.~po }		// all events are related to 0 or 1 events by po
fact po_connect { all e : Event | all e':Event |  (e->e' in ^eo and e in Event.~po and e' in Event.po) implies (e->e' in ^po+^~po)} // If there are several instructions related by po in a thread there is exactly one sequence connecting all them by po

//com
fun com : MemoryEvent->MemoryEvent { rf + fr + co }
fact com_in_same_addr { com in address.~address }

//coherence-order
fact co_transitive { transitive[co] }											// co is transitive
fact co_total { all a : Address | total[co, a.~address & (committed_events & Write)] }		// co is total
fact co_commited {all e : Event | event_commits[e.co] and event_commits[co.e]}			// co relates commited events only

//reads-from
fact lone_source_write { rf.~rf in iden }										// each read has a single source over rf

//reads-from-init
fact rf_init_in_eo {rf_init in ^eo} //Would be enough to assert irreflexivity, same_thread and first_initialization access
fact rf_init_in_same_addr {rf_init in address.~address}
fact rf_init_in_same_thread {same_thread[rf_init.Event,Event.rf_init]}
fact rf_init_initialize {initialization_access[Event.rf_init] and initialization_access[rf_init.Event]}
fact rf_init_domain {(MemoryEvent.rf_init+rf_init.MemoryEvent) in (Read+CacheFlush)}
fact rf_init_total {all e : (Read+CacheFlush) | {some e':Event | e != e' and same_address[e,e'] and initialization_access[e']} and initialization_access[e] => e in (rf_init.Event+Event.rf_init)}

fun com_arch : MemoryEvent->MemoryEvent { rf_init + com }


//from-reads relates each Read to all co-sucessors of Write that it read from it including Reads that read from the initial state
fact fr_min {~rf.co + (((Event.po + po.Event) & Read)-((Event.po + po.Event) & Write).rf) <: address.~address :> ((Event.po + po.Event) & Write) in fr} 
// some events have to be necessarily connected by fr. This includes all Reads and all co-sucessors of Write that read from it and
// all Reads that read from initial state if they are necessarily committed.
fact fr_max {fr in ~rf.co + (Read-Write.rf) <: address.~address :> Write}	
// other events can be connected by fr but do not have to. This includes Reads that read from initial state as well. However, 
// if an event is not committed there is no fr edge incident to it. 
fact fr_connect {all e : Read | event_commits[e] implies e <: address.~address :> Write in fr}
// If a Read has an outgoing fr edge it is committed and thus has to be connected to all subsequent Writes and not only to some

// dependencies (for now just consists of addr)
//fun dep : Read->MemoryEvent { addr }
//fact dep_in_eo { dep in ^eo }

// Performance optimizations
// Events that do not access architectural state nor extra-architectural state are ommitted since they are not interesting to our analysis
fact event_simplify {Event in xstate_access.XSAccess + MemoryEvent}
// XSAccess that are not connected to any Event are ommitted
fact xsaccess_simplify {XSAccess in Event.xstate_access}
//fact no_trailing_fence { all f : Fence | f in Event.po and f in po.Event 


/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 3: Constrain leakage containment model relations

//xstate_access
fact xstate_access_inj {xstate_access.~xstate_access in iden}
fact xstate_access_surj {XSAccess in Event.xstate_access}

//eo
fact eo_acyclic { acyclic[eo] }							// eo is acyclic
fact eo_prior { all e : Event | lone e.~eo }					// all events are related to 0 or 1 events by eo

//comx
fun comx : XSAccess -> XSAccess { rfx + frx + cox }
fact comx_in_same_xstate { comx in xstate.~xstate }			//NOTE: this will change once we allow set of xstate

// helper functions
fun XSRead : XSAccess { xstate_event_type.XRead }
fun XSWrite : XSAccess { xstate_event_type.XWrite }
fun XSRMW : XSAccess { xstate_event_type.XRead & xstate_event_type.XWrite}
fun XSReaders : XSAccess { XSRead+ XSRMW }
fun XSWriters : XSAccess { XSWrite + XSRMW }

fun erfx : Event->Event {(xstate_access.rfx).~xstate_access}		//rfx on Event level
fun ecox : Event->Event {(xstate_access.cox).~xstate_access}		//cox on Event level
fun efrx : Event->Event {(xstate_access.frx).~xstate_access}		//frx on Event level

fun eXSRead : Event { xstate_access.xstate_event_type.XRead }
fun eXSWrite : Event { xstate_access.xstate_event_type.XWrite }
fun eXSRMW : Event { xstate_access.xstate_event_type.XRead & xstate_access.xstate_event_type.XWrite}
fun eXSReaders : Event { eXSRead+ eXSRMW }
fun eXSWriters : Event { eXSWrite + eXSRMW }

//constrain events
fact constrain_write {Write in eXSRMW}			// Writes are always read modify write
fact constrain_cacheFlush {CacheFlush in eXSRMW}	// CacheFlushs are always read modify write
fact constrain_read {Read in eXSRead + eXSRMW}		// Reads are always either reads or read modify write

//rfx
fact constrain_rfx { rfx in XSWriters->XSReaders } 
fact rfx_acyclic { acyclic[rfx] }								// rfx is acyclic TODO: see note on atomicity, this should be part of the consistency predicate
fact lone_source_writex { rfx.~rfx in iden }

// cox
fact cox_transitive { transitive[cox] }
fact cox_total { all s: XState | total[cox, s.~xstate & XSWriters] }//TODO: Add again
fact constrain_cox { cox in XSWriters->XSWriters }			
//fact cox_acyclic { acyclic[cox] }							// cox is acyclic TODO: see above, however this might be different

fun frx : XSAccess->XSAccess {
  ~rfx.cox
  +
  ((XSReaders - (XSWriters.rfx)) <: (xstate.~xstate) :> XSWriters)
  //-iden 
}
fact constrain_frx { frx in XSReaders->XSWriters }

//fact frx_acyclic {  acyclic[frx] } //TODO: see above

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 4: Specify relevant interactions between MCM and LCM sets and relations

// relate po and eo
fact po_in_eo { po in ^eo }                                                              // po is a subset of ^eo

// TODO: constrain com to relate committed events only
fact com_in_committed { all e, e' : Event | e->e' in com => event_commits[e] and event_commits[e'] }

// TODO: MemoryEvents that modify the same address should modify the same xstate; however, aspects of this will
// change if we permit xstate to be a set
//fact same_addr_in_same_xstate { address.~address in xstate.~xstate } // same address events are also same state events

// TODO: relate com and comx
// fact co_in_cox { co in cox} /./Only true if not considering sets of xstate
// fact fr_in_frx { fr in frx }


// TODO:  "transient_events" used to be "squashed_events", so we'll have to do a find-replace in the x86_lcm file

// =Committed and Transient Events=

fun committed_events : Event { po.Event + Event.po + Event.(rf+fr+~rf+~fr) }	// Committed events are events that 
	// are either related by po with other events or have an incoming or outgoing com edge
	// Note that this definition does not work for a few special cases (e.g. only one thread with a single instruction in it),
	// these cases can be ommitted safely though.

fact {all e: Event| all e':Event | (e!=e' and e in committed_events and e' in committed_events and e->e' in ^(eo+~eo))
	 implies (e->e' in ^(po+~po))}
//TODO: exchange by fact not using all
// committed_events <:Event.Event:> committed_events


fun transient_events : Event { Event - committed_events }						// Speculative/transient events are events that are not committed.
pred event_commits[e: Event] { e in committed_events }
pred event_transients[e: Event] { e in transient_events }

//pred intervening_access[e : Event, e' : Event] {some e'':Event| e->e'' not in  ^(com+rf_init) 
//									    and e''->e' in comx and e'' in XSWriters and e''.xstate = e.xstate}//TEMP, might need improvement

//pred no_leakage[e : Event, e' : Event] {e->e' in (com+rf_init) => (e->e' in ^comx and not intervening_access[e,e'])}
//add that e'' has same xstate


//fun same_thread [rel: Event->Event] : Event->Event {
 // rel & ( iden + ^eo + ~^eo )
//}
/*TODO: fun coix[] : MemoryEvent->MemoryEvent { same_thread[cox] }
fun coex[] : MemoryEvent->MemoryEvent { cox - coix }
fun frix[] : MemoryEvent->MemoryEvent { same_thread[frx] }
fun frex[] : MemoryEvent->MemoryEvent { frx - frix }
pred rmw_atomicity{frex.coex & (xstate_event_type.XRead & xstate_event_type.XWrite)}*/
/*pred xstate_state_atomicity{}*/
	// See NOTE above, also see paper https://dl.acm.org/doi/pdf/10.1145/3037697.3037723

//check{not some e:Event|#po.e>1}
//check {not(some e : Event | e->e in ^frx)}
//check {all e:Event| all e':Event| no_leakage[e,e']}

run{} for 5


//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Alloy shortcuts=
fun optional[f: univ->univ] : univ->univ  { iden + f }
pred transitive[rel: (Event+XSAccess)->(Event+XSAccess)]        { rel.rel in rel }
pred irreflexive[rel: (Event+XSAccess)->(Event+XSAccess)]       { no iden & rel }
pred acyclic[rel: (Event+XSAccess)->(Event+XSAccess)]           { irreflexive[^rel] }
pred total[rel: (Event+XSAccess)->(Event+XSAccess), bag: (Event+XSAccess)] {
  // all unique event are part of the relation and the relation is acyclic
  all disj e, e': bag | e->e' in rel + ~rel
  acyclic[rel]
}


fun thread[t: Event] : Event->Event {
  { t + t.(^po + ^~po) } <: iden
}
fun ext [ r: Event -> Event ] : Event -> Event { r - (^po + ^~po) }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =LCM shortcuts=
pred same_address[e : Event, e' : Event] { e.address = e'.address }
pred po_tc[e : Event, e' : Event] { e->e' in ^po }
// TODO: add in this helper function for eo transitive closure and predicate for same_thread when we add in eo
// pred eo_tc[e: Event, e': Event] { e->e' in ^eo }

//If and only if events are connected over po or eo they are part of the same thread
pred same_thread[e : Event, e' : Event] { e->e' in (iden + ^(po + eo) + ~^(eo+po)) }


// initialization access
// there has been no write to that location yet. What does that mean? 
// There have been no Write to the same address occured earlier, use po?
pred initialization_access[e : Event] {all e' : Write | e!= e' implies not(e'->e in ^eo and same_address[e,e'])}

//first initialization access
pred first_initialization_access[e : Event] { initialization_access[e] and {all e' : Event | (e!=e' and initialization_access[e'] and same_thread[e,e']) => e->e' in ^eo}}
//read passage in paper again, it says there something about this being okay for most applications
