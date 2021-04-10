module lcm_skeleton

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  Specifying Leakage Containment Models Axiomatically (Programs + Candidate Executions)
//  This file contains basic memory model sets and relations and suggestions to extend MCMs to produce LCM

/////////////////////////////////////////////////////////////////////////////////////////////////////////////

// SECTION 1: Specify relevant sets (e.g., Address, Event, Read, Write, Fence) and relations (address, po, addr, rf, co)
sig Address {                                                   // set of physical address objects representing shared memory locations
  //privilege_domain: one PrivilegeDomain           // OPTIONAL, uncomment to use
								       // there is no leakage between members of the same privilige domain
}

sig XState { }                                                  // extra-architectural state locations

sig Event {							// set of instruction objects representing assembly language program instructions
  po: lone Event,						// set of tuples of the form (Event, Event) which map each instruction object in Event 
									// to the instruction sequencing of committed instructions
  tfo: lone Event,						// set of tuples of the form (Event, Event) which map each instruction object in Event 
									// to the sequence of instructions in which they began execution
  xstate_access: lone XSAccess				// extra-architectural state accesses
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

abstract sig MemoryEvent extends Event{	// set of instruction objects representing assembly language program instructions which access architectural state
  address: one Address,					// set of tuples of the form (Event, Address) which map each MemoryEvent to the one Address that it accesses
  rf_init : set MemoryEvent					// memory accesses might read from the initial state of the memory
}

sig Read extends MemoryEvent {			// Read is a subset of MemoryEvents that is disjoint from Write and CacheFlush
  addr : set MemoryEvent,					// address dependency relation, relates a Read to a po-subsequent MemoryEvent when the value accessed by that event syntactically depends on the value returned by the Read
  fr: set Write							// from-reads relation
}

sig Write extends MemoryEvent {			// Write is a subset of MemoryEvents that is disjoint from Read
  rf: set Read,							// reads-from relation, relates each Write to all same-address Reads it sources
  co: set Write							// coherence-order relation, relates all Writes to all Writes that follow it in coherence order 
}


// Additional Events

sig Branch extends Event {}							      // Branches are Events that access xstate
fact branch_has_xstate {all b : Branch | one {b.xstate_access}}    //TODO: delete?

sig Jump extends Event {}							      // Jumps are Events that access xstate
fact branch_has_xstate {all j : Jump | one {j.xstate_access}}	      //TODO: delete?

abstract sig Fence extends Event { }					      // Fences are Events that do not access xstate
fact fence_has_no_xstate {Fence.xstate_access = none}    	      //TODO: delete?

sig CacheFlush extends MemoryEvent { }	                              // CacheFlushes are special Memory Events
fact cf_is_xread{all c : CacheFlush | XRead in c.xstate_access.xstate_event_type } // that access xstate as a XRead or XRMW


sig REG extends Read {}                                                              // REG operations are special reads that access xstate
fact reg_has_xstate{all r : REG | some {r.xstate_access}}
fact reg_no_shared_xstate {all r : REG | all e : Event | disj[e,r] implies disj[e.xstate_access.xstate,r.xstate_access.xstate]}
fact reg_no_shared_memory {all r : REG | all e : Event | disj[e,r] implies disj[e.address,r.address]}
fact reg_no_rf_init {all r : REG | all e : Event | disj[rf_init.r,e] and disj[r.rf_init,e]}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 2: Constrain memory consitency model relation

//po
fact po_acyclic { acyclic[po] }					// po is acyclic
fact po_prior { all e : Event | lone e.~po }		// all events are related to 0 or 1 events by po
fact po_connect { all e : Event | all e':Event |  (e->e' in ^tfo and e in Event.~po and e' in Event.po) implies (e->e' in ^po+^~po)} // If there are several instructions related by po in a thread there is exactly one sequence connecting all them by po

//com
fun com : MemoryEvent->MemoryEvent { rf + fr + co }
fact com_in_same_addr { com in address.~address }

//coherence-order
fact co_transitive { transitive[co] }										          	// co is transitive
fact co_total { all a : Address | total[co, a.~address & (committed_events & Write)] }		// co is total
fact co_commited {all e : Event | event_commits[e.co] and event_commits[co.e]}			// co relates commited events only

//reads-from
fact lone_source_write { rf.~rf in iden }										// each read has a single source over rf

//reads-from-init
fact rf_init_in_tfo {rf_init in ^tfo}
fact rf_init_in_same_addr {rf_init in address.~address}
fact rf_init_in_same_thread {same_thread[rf_init.Event,Event.rf_init]}
fact rf_init_initialize {initialization_access[Event.rf_init] and initialization_access[rf_init.Event]}
fact rf_init_domain {(MemoryEvent.rf_init+rf_init.MemoryEvent) in (Read+CacheFlush)}
fact rf_init_total {all e : (Read+CacheFlush) | {some e':Event | disj[e,e'] and same_address[e,e'] and initialization_access[e']} and initialization_access[e] => e in (rf_init.Event+Event.rf_init)}

//com_arch edges 
fun com_arch : MemoryEvent->MemoryEvent { rf_init + com }

//constrain fr edges
// from-reads relates each Read to all co-sucessors of Write that it read from it including Reads that read from the initial state
fact fr_min {~rf.co + (((Event.po + po.Event) & Read)-((Event.po + po.Event) & Write).rf) <: address.~address :> ((Event.po + po.Event) & Write) in fr} 
// some events have to be necessarily connected by fr. This includes all Reads and all co-sucessors of Write that read from it and
// all Reads that read from initial state if they are necessarily committed.
fact fr_max {fr in ~rf.co + (Read-Write.rf) <: address.~address :> Write}	
// other events can be connected by fr but do not have to. This includes Reads that read from initial state as well. However, 
// if an event is not committed there is no fr edge incident to it. 
fact fr_connect {all e : Read | all w : Write | (same_thread[e,w] and event_commits[e]) implies e <: address.~address :> w in fr} //TODO: find better expression
// If a Read has an outgoing fr edge it is committed and thus has to be connected to all subsequent Writes and not only to some

// dependencies (for now just consists of addr)
fun dep : Read->MemoryEvent { addr }
fact dep_in_tfo { dep in ^tfo }

// Performance optimizations
// Events that do not access architectural state nor extra-architectural state are ommitted since they are not interesting to our analysis
fact event_simplify {Event in xstate_access.XSAccess + MemoryEvent}
// XSAccess that are not connected to any Event are ommitted
fact xsaccess_simplify {XSAccess in Event.xstate_access}


/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 3: Constrain leakage containment model relations

//xstate_access
fact xstate_access_inj {xstate_access.~xstate_access in iden}
fact xstate_access_surj {XSAccess in Event.xstate_access}

//tfo
fact tfo_acyclic { acyclic[tfo] }							// tfo is acyclic
fact tfo_prior { all e : Event | lone e.~tfo }				// all events are related to 0 or 1 events by tfo

//comx
fun comx : XSAccess -> XSAccess { rfx + frx + cox }
fact comx_in_same_xstate { comx in xstate.~xstate }

// helper functions
fun XSRead : XSAccess { xstate_event_type.XRead }
fun XSWrite : XSAccess { xstate_event_type.XWrite }
fun XSRMW : XSAccess { xstate_event_type.XRead & xstate_event_type.XWrite}
fun XSReaders : XSAccess { XSRead+ XSRMW }
fun XSWriters : XSAccess { XSWrite + XSRMW }

// lifting comx functions to event level
fun erfx : Event->Event {(xstate_access.rfx).~xstate_access}		//rfx on Event level
fun ecox : Event->Event {(xstate_access.cox).~xstate_access}	//cox on Event level
fun efrx : Event->Event {(xstate_access.frx).~xstate_access}		//frx on Event level
fun ecomx: Event->Event {(xstate_access.comx).~xstate_access}	//comx on Event level

// lifting helper functions to event level
fun eXSRead : Event { xstate_access.xstate_event_type.XRead }
fun eXSWrite : Event { xstate_access.xstate_event_type.XWrite }
fun eXSRMW : Event { xstate_access.xstate_event_type.XRead & xstate_access.xstate_event_type.XWrite}
fun eXSReaders : Event { eXSRead+ eXSRMW }
fun eXSWriters : Event { eXSWrite + eXSRMW }

//constrain events
//TODO: it would be enough to assert Write in eXSRead to assert that Write always reads from xstate first.
fact constrain_write {Write in eXSRead + eXSRMW}				// Writes are always either reads or read modify write
fact constrain_cacheFlush {CacheFlush in eXSRead + eXSRMW}	// CacheFlushs are always either reads or read modify write
fact constrain_read {Read in eXSRead + eXSRMW}				// Reads are always either reads or read modify write
fact constrain_read {Branch in eXSRead + eXSRMW}			// Branch are always either reads or read modify write
fact constrain_read {Fence not in eXSRead + eXSRMW}			// Fences do not access xstate

//rfx
fact constrain_rfx { rfx in XSWriters->XSReaders } 
fact lone_source_writex { rfx.~rfx in iden }

// cox
fact cox_transitive { transitive[cox] }
fact cox_total { all s: XState | total[cox, s.~xstate & XSWriters] }
fact constrain_cox { cox in XSWriters->XSWriters }			
fact cox_acyclic { acyclic[cox] }							// cox is acyclic TODO: see above, however this might be different

//frx
//TODO: we might need a lemma that asserts that there is either frx or rfx
fun frx : XSAccess->XSAccess {
  ~rfx.cox
  +
  ((XSReaders - (XSWriters.rfx)) <: (xstate.~xstate) :> XSWriters)
}
fact constrain_frx { frx in XSReaders->XSWriters }

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 4: Specify relevant interactions between MCM and LCM sets and relations

// relate po and tfo
fact po_in_tfo { po in ^tfo }                                                              // po is a subset of ^tfo

// constrain com to relate committed events only
fact com_in_committed { all e, e' : Event | e->e' in com => event_commits[e] and event_commits[e'] }

// MemoryEvents that modify the same address should modify the same xstate; however, aspects of this will
// change if we permit xstate to be a set
fact same_addr_in_same_xstate { address.~address in xstate_access.(xstate.~xstate).~xstate_access } // same address events are also same state events


// =Committed and Transient Events=

// Committed events are events that are either related by po with other events or have an incoming or outgoing rf or fr edge
// Note that this definition does not work for one special cases (only one thread with a single instruction in it),
// these cases can be ommitted safely though.
fun committed_events : Event { po.Event + Event.po + Event.(rf+fr+~rf+~fr) }
fun transient_events : Event { Event - committed_events }						// Speculative/transient events are events that are not committed.
pred event_commits[e: Event] { e in committed_events }
pred event_transients[e: Event] { e in transient_events }

// Assert that all commited event are connected by po if connected by tfo
fact commits_connect {all disj e,e': Event | (e in committed_events and e' in committed_events and e->e' in ^(tfo+~tfo))
	 implies (e->e' in ^(po+~po))}



/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 5: Leakage

// =Leakage=

pred intervening_access[e : Event, e' : Event]{
  e->e' in com_arch and 
 {some e'':Event| disj[e'',e] and disj[e'',e'] 
  and e->e'' not in  ^com_arch and e''->e' in ecomx 
  and e'' in eXSWriters}
}

pred com_comx_consistent[e : Event, e' : Event]{
  (e->e' in rf implies e->e' in erfx)
  and (e->e' in co implies e->e' in ecox)
  and (e->e' in fr implies e->e' in efrx)
  and (e->e' in rf_init implies e->e' in erfx)
}

pred leakage[e : Event, e' : Event] {disj[e,e']  and (not com_comx_consistent[e,e'] or intervening_access[e,e'])}
pred leakage {some e, e' : Event | leakage[e,e']}









// =Define what leaks=

pred is_sink [e: Event] {some e':Event | leakage[e',e]}

//one sig Sink{}
//fun Sinks : Event->Sink {Event->Sink}
//fact {all e: Event | e in Sinks.Sink => sink[e]}

//pred candidate_source [e:Event]{some s:Event | e!=s and sink[s] and e->s in ^~ecomx} Think about situations where e is candidate_source
//for two sinks. Can this be possible?

pred candidate_source [e:Event,sink:Event]{is_sink[sink] and sink->e in ^~ecomx}

pred xstate_leakage[source:Event,sink:Event] {candidate_source[source,sink] /*and not leakage_is_benign*/}
//fun xstate_leakage:Event->Event{ {all e,e': Event | xstate_leakage[e,e']} => Event.po else po.Event}

pred data_leakage [e:Event,sink:Event]{is_sink[sink] and sink->e in ^~ecomx.~addr}


//TODO: Reflexivity

// =Privilege Domains=
// OPTIONAL, uncomment to use

//abstract sig PrivilegeDomain{}
//one sig AttackerControlled extends PrivilegeDomain{}
//one sig VictimControlled extends PrivilegeDomain{}
//pred leakage_is_benign[e:Event,sink:Event] {e.address.privilege_domain=sink.address.privilege_domain}


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
// TODO: add in this helper function for tfo transitive closure and predicate for same_thread when we add in tfo
// pred tfo_tc[e: Event, e': Event] { e->e' in ^tfo }
pred same_xstate[e : Event, e' : Event] {e.xstate_access.xstate = e'.xstate_access.xstate}

//If and only if events are connected over po or tfo they are part of the same thread
//TODO: tfo should be enough, is there a po in ~tfo?
pred same_thread[e : Event, e' : Event] { e->e' in (iden + ^(po + tfo) + ~^(tfo+po)) }


// initialization access
// there has been no write to that location yet. What does that mean? 
// There have been no Write to the same address occured earlier, use po?
pred initialization_access[e : Event] {all e' : Write | disj[e,e'] implies not(e'->e in ^tfo and same_address[e,e'])}

//first initialization access
pred first_initialization_access[e : Event] { initialization_access[e] and {all e' : Event | (disj[e,e'] and initialization_access[e'] and same_thread[e,e']) => e->e' in ^tfo}}

