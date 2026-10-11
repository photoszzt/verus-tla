----------------------------- MODULE Mutex -----------------------------
\* Exact two-thread finite instance of src/mutex_example.rs.
VARIABLES lock, pc
vars == <<lock, pc>>

Threads == {"A", "B"}
Stages == {"Waiting", "Holding", "Terminated"}

Init ==
  /\ lock = FALSE
  /\ pc = [t \in Threads |-> "Waiting"]

Acquire(t) ==
  /\ ~lock
  /\ pc[t] = "Waiting"
  /\ lock' = TRUE
  /\ pc' = [pc EXCEPT ![t] = "Holding"]

Release(t) ==
  /\ pc[t] = "Holding"
  /\ lock' = FALSE
  /\ pc' = [pc EXCEPT ![t] = "Terminated"]

Next == \E t \in Threads : Acquire(t) \/ Release(t)
BaseSpec == Init /\ [][Next]_vars
Fair == \A t \in Threads : WF_vars(Acquire(t)) /\ WF_vars(Release(t))
Spec == BaseSpec /\ Fair
UnfairSpec == BaseSpec

TypeOK == lock \in BOOLEAN /\ pc \in [Threads -> Stages]
Mutex == ~\E a, b \in Threads : a # b /\ pc[a] = "Holding" /\ pc[b] = "Holding"
LockConsistent == lock = (\E t \in Threads : pc[t] = "Holding")
Done == \A t \in Threads : pc[t] = "Terminated"
EventuallyDone == <>Done
StarvationFreedom == \A t \in Threads : (pc[t] = "Waiting") ~> (pc[t] = "Terminated")

=======================================================================
