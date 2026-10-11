------------------------- MODULE GenericMachineModel -------------------------
\* Finite witness for the generic StateMachine result and Next relation.
\* Both steps are enabled, although DeclaredActions is empty.
VARIABLE state

States == {0, 1, 2}
Inputs == {"go"}
Steps == {"left", "right"}
ActionIds == {"L", "R"}
ActionInputs == {"unit"}
MessageOps == {"unit"}
Outputs == {"ok"}
InitStates == {0}
NetworkInitStates == {0}
DeclaredActions == {}
StepToAction == [step \in Steps |-> IF step = "left" THEN "L" ELSE "R"]
StepInput == [pair \in Steps \X Inputs |-> "unit"]
EnabledTriples == {<<"L", "unit", 0>>, <<"R", "unit", 0>>}
Transition == [triple \in EnabledTriples |->
  IF triple[1] = "L" THEN <<1, "ok">> ELSE <<2, "ok">>]
Deliver == "L"

Machine == INSTANCE GenericMachines WITH
  States <- States, Inputs <- Inputs, Steps <- Steps,
  ActionIds <- ActionIds, ActionInputs <- ActionInputs,
  MessageOps <- MessageOps, Outputs <- Outputs,
  InitStates <- InitStates, NetworkInitStates <- NetworkInitStates,
  DeclaredActions <- DeclaredActions, StepToAction <- StepToAction,
  StepInput <- StepInput, EnabledTriples <- EnabledTriples,
  Transition <- Transition, Deliver <- Deliver, state <- state

Spec == Machine!Spec
TypeOK == state \in States
ResultWellFormed ==
  /\ Machine!StepResult("go", 0).kind = "Enabled"
  /\ Machine!StepResult("go", 0).state \in {1, 2}
  /\ Machine!NetworkResult("unit", 0).state = 1
ASSUME ResultWellFormed

==========================================================================
