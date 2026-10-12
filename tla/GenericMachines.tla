---------------------- MODULE GenericMachines ----------------------
\* Value-level Action and StateMachine formulation from src/action.rs
\* and src/state_machine.rs. Constants are instantiated by applications.
CONSTANTS States, Inputs, Steps, ActionIds, ActionInputs, MessageOps, Outputs,
          InitStates, DeclaredActions, StepToAction, StepInput,
          EnabledTriples, Transition, Deliver, NetworkInitStates
TP == INSTANCE TemporalPredicates WITH States <- States

VARIABLE state
vars == <<state>>

ActionPre(a, i, s) == <<a, i, s>> \in EnabledTriples
ActionForward(a, i, s, t) ==
  /\ ActionPre(a, i, s)
  /\ t = Transition[<<a, i, s>>][1]

ActionPreStates(a, i) == {s \in States : ActionPre(a, i, s)}
ActionForwardRelation(a, i) ==
  {pair \in States \X States : ActionForward(a, i, pair[1], pair[2])}

\* This is Action::weak_fairness, whose premise uses the precondition.
\* Native WF_vars on an action is a separate, intentional specialization.
ActionWeakFairness(a, i) ==
  TP!LeadsTo(TP!Always(TP!LiftState(ActionPreStates(a, i))),
             TP!LiftAction(ActionForwardRelation(a, i)))

ActionResult(a, i, s) ==
  IF ActionPre(a, i, s)
  THEN LET pair == Transition[<<a, i, s>>]
       IN [kind |-> "Enabled", state |-> pair[1], output |-> pair[2]]
  ELSE [kind |-> "Disabled"]

MappedPre(step, input, s) ==
  ActionPre(StepToAction[step], StepInput[<<step, input>>], s)

\* Verus next_result selects one enabled step with choose. Its actions
\* field is not consulted, even when the chosen action is absent there.
StepResult(input, s) ==
  IF \E step \in Steps : MappedPre(step, input, s)
  THEN LET chosen == CHOOSE step \in Steps : MappedPre(step, input, s)
       IN ActionResult(StepToAction[chosen], StepInput[<<chosen, input>>], s)
  ELSE [kind |-> "Disabled"]

NextActionResult(a, i, s) == ActionResult(a, i, s)
NetworkResult(messageOps, s) == ActionResult(Deliver, messageOps, s)

Init == state \in InitStates
StepAction(step, input) ==
  /\ MappedPre(step, input, state)
  /\ state' = Transition[<<StepToAction[step], StepInput[<<step, input>>], state>>][1]
Next == \E step \in Steps : \E input \in Inputs : StepAction(step, input)
Spec == Init /\ [][Next]_vars

NetworkInit == state \in NetworkInitStates
NetworkNext == \E input \in MessageOps : ActionForward(Deliver, input, state, state')
NetworkSpec == NetworkInit /\ [][NetworkNext]_vars

====================================================================
