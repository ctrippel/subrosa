module lcm_skeleton

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  Specifying Leakage Containment Models Axiomatically (Programs + Candidate Executions)
//  This file contains basic memory model sets and relations and suggestions to extend MCMs to produce LCM

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 1: Specify relevant sets (e.g., Address, Event, Read, Write, Fence) and relations (address, po, addr, rf, co, 
sig Address { }								// set of physical address objects representing shared memory locations

abstract sig Event {						// set of instruction objects representing assembly language program instructions
	po: lone Event,							// set of tuples of the form (Event, Event) which map each instruction object in Event 
													// to the instruction sequencing of committed instructions
}

// TODO: when we add XSEvents, they will operate on elements of XState, similar to how MemoryEvents operate on elements of Address
// abstract sig XState { }					// extra-architectural state locations

// TODO: when we add XSEvents, they will operate behaves as either a "read", "write", or "rmw" with resepct to the xstate that they access
// abstract sig XSEventType { }	
// one sig XRead extends XSEventType { }
// one sig XWrite extends XSEventType { }
// one sig XRMW extends XSEventType { } // could implement with relations

// TODO: add XSEvents as a type of Event. For all instructions that can communicate with other instructions
// via xstate, the will extend from XSEvent (see diagram I sent)
// abstract sig XSEvent extends Event {
// 	xstate: one XState,													// set of tuples of the form (XSEvent, XState) which map each XSEvent to the one
																						// XState element that it accesses. As an extension, we could use "set" instead of "one"
																						// to denote a vetor of XState elements
// 	xstate_event_type: one XSEventType,							// Each instruction can only behave as one type of xstate access during its excution,
																						// which there may be multiple options for the "type" as will be specified on an ISA-by-ISA
																						// basis, for example in x86_lcm
// 	rfx: set XSEvent,														// rf lifted to XSEvents
// 	cox: set XSEvent														// cox lifted to XSEvents
// }

abstract sig MemoryEvent extends Event {  // extends XSEvent {	// TODO : MemoryEvents should be a subset of StateEvents
																						// "abstract" means that MemoryEvent will only contain objects from sigs
																						// that extend it
	address: one Address 													// set of tuples of the form (Event, Address) which map each MemoryEvent
																						// to the one Address that it accesses 
}

sig Read extends MemoryEvent {							// Read is a subset of MemoryEvents that is disjoint from Write
	addr : set MemoryEvent									// address dependency relation -- let's just worry about these for now
																			// and add in data, crtrl later
	// data : set Write,
	// ctrl : set MemoryEvent
}

sig Write extends MemoryEvent {							// Write is a subset of MemoryEvents that is disjoint from Read
	rf: set Read,														// reas-from relation
 	co: set Write														// 
}

// TODO: We will want to add this instruction also to enable modeling of some basic flush+reload style attacks
// sig CacheFlush extends MemoryEvent { }

// Fence currently exends Event, which means we are not modeling it as having xstate intractions with other instructions
// This is fine for now -- we can talk about why
abstract sig Fence extends Event { }					 

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 2: Constrain memory consitency model relations
//po
fact po_acyclic { acyclic[po] }							// po is acyclic												
fact po_prior { all e: Event | lone e.~po }			// all events are related to 0 or more events by po		

//com
fun com : MemoryEvent->MemoryEvent { rf + fr + co }
fact com_in_same_addr { com in address.~address }

//writes
fact co_transitive { transitive[co] }
fact co_total { all a: Address | total[co, a.~address & Write] }		// TODO: we want co to only refer to committed events, so we should use the line below instead once we add eo	
// fact co_total { all a: Address | total[co, a.~address & (committed_events & Write)] }

//reads
fact lone_source_write { rf.~rf in iden }						
fun fr : Read->Write {							
  ~rf.co																							
  +
  // also include reads that read from the initial state
  ((Read - (Write.rf)) <: address.~address :> Write)		// TODO: we want fr to only refer to committed events, so we should use the line below instead once we add eo
  // ((committed_events & Read) - ((committed_events & Write).rf) <: address.~address :> (committed_events & Write))		
}

fact no_trailing_fence { all f : Fence | f in Event.po and f in po.Event }			// This is just a performance optimization

// dependencies (for now just consists of addr) 
fun dep : Read->MemoryEvent { addr }
fact dep_in_po { dep in ^po }					// TODO: dependencies can involve instructions that don't commit, so we shuld use the line below instead once we add eo
// fact dep_in_eo { dep in ^eo }	


/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 3: Constrain leakage containment model relations 

// TODO: constrain eo, similar to how po is constrainted above
// fact eo_acyclic { acyclic[eo] }																	// eo is acyclic	
// fact eo_prior { all e: Event | lone e.~eo }													// all events are related to 0 or more events by eo

// TODO: constrain comx similar to how we constrained com above
// fun comx : XSEvent->XSEvent { rfx + frx + cox }
// fact comx_in_same_xstate { comx in xstate.~xstate }

// TODO: more constraints for comx that are distict from com
// helper functions
// fun XSRead : XSEvent { xstate_event_type.XRead }
// fun XSWrite : XSEvent { xstate_event_type.XWrite }
// fun XSRMW : XSEvent { xstate_event_type.XRMW }
// fun XSReaders : XSEvent { xstate_event_type.XRead + xstate_event_type.XRMW }
// fun XSWriters : XSEvent { xstate_event_type.XWrite + xstate_event_type.XRMW }
// fact constrain_cox { cox in XSWriters->XSWriters }
// fact constrain_rfx { rfx in XSWriters->XSReaders }
// fact constrain_frx { frx in XSReaders->XSWriters }

// TODO: constrain xstate writes similar to how we constrained memory writes above
// fact cox_transitive { transitive[cox] }	
// fact cox_total { all s: XState | total[cox, s.~xstate & XSWriters] }

// TODO: constrain xstate reads similar to how we constrained memory reads above, excpet we need to handle the spcial case of RMWs being modeled as a single instruction instead of two
// fact lone_source_writex { rfx.~rfx in iden }		
// fun frx : XSEvent->XSEvent {							
// 	(
// 		~rfx.cox																							
//   		+
//   		// also include reads that read from the initial xstate
//   		((XSReaders - (XSWriters.rfx)) <: (xstate.~xstate) :> XSWriters)
// 	) - iden // need to do this for RMWs
// }


/////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SECTION 4: Specify relevant interactions between MCM and LCM sets and relations

// TODO: relate po and eo
// fact po_in_eo { po in ^eo }								// po is a subset of ^eo

// TODO: constrain com to relate committed evenets only
// fact com_in_committed { all e, e': Event | e->e' in com => event_commits[e] and event_commits[e'] } 

// TODO: MemoryEvents that modify the same address should modify the same xstate; however, aspects of this will
// change if we permit xstate to be a set
// fact same_addr_in_same_xstate { address.~address in xstate.~xstate }	// same address events are also same state events

// TODO: relate com and comx
// fact co_in_cox { co in cox}
// fact fr_in_frx { fr in frx }


// TODO: helper functions for reasoning about transient vs. non-transient events
// Also, "transient_events" used to be "squashed_events", so we'll have to do a find-replace in the x86_lcm file
// fun committed_events : Event { po.Event + Event.po }			// TODO: take care of the case where there is only one instruciton on a thread
																							// as long as it's not illegal (e.g., rogues access/meltdown case) it's conisdered to have committed
// fun transient_events : Event { Event - committed_events }
// pred event_commits[e: Event] { e in committed_events }	
													

run { }


//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// =Alloy shortcuts=
fun optional[f: univ->univ] : univ->univ  { iden + f }
pred transitive[rel: Event->Event]        { rel.rel in rel }	
pred irreflexive[rel: Event->Event]       { no iden & rel }	
pred acyclic[rel: Event->Event]           { irreflexive[^rel] }	 
pred total[rel: Event->Event, bag: Event] {
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
pred same_address[e: Event, e': Event] { e.address = e'.address }
pred po_tc[e: Event, e': Event] { e->e' in ^po }
// TODO: add in this helper function for eo transitive closure and predicate for same_thread when we add in eo
// pred eo_tc[e: Event, e': Event] { e->e' in ^eo }
pred same_thread[e: Event, e': Event] { e->e' in {^po + ~^po} } // TODO: need to use line below when we add eo
//pred same_thread[e: Event, e': Event] { e->e' in {^eo + ~^eo} }

