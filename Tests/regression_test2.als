module Tests/regression_test3
open lcm_skeleton

// Spectre v1
pred t1[] {#Event = 5 and #CacheFlush = 1 and #Read=3 and #Write=0}
pred t2[] {all e: Event | e in Event.(rf+fr)+(rf+fr).Event implies event_commits[e]}
pred t3[] {all e: Event | all e': Event | event_commits[e] and e->e' in ^(po+~po) implies event_commits[e']}


check {t1 && t2 && t3}
