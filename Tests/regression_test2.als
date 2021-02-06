module Tests/regression_test2
open lcm_skeleton

// Test committed_events 
pred t1[] {all e: Event | e in Event.po+po.Event implies event_commits[e]}
pred t2[] {all e: Event | e in Event.(rf+fr)+(rf+fr).Event implies event_commits[e]}
pred t3[] {all e: Event | all e': Event | event_commits[e] and e->e' in ^(po+~po) implies event_commits[e']}


check {t1 && t2 && t3}
