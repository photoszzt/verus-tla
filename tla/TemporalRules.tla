--------------------------- MODULE TemporalRules ---------------------------
\* Native propositional temporal laws corresponding to public rules.rs laws.
\* Each variable is an unconstrained state proposition; PTL checks the
\* temporal shape for every behavior of these propositions.
EXTENDS TLAPS

VARIABLES p, q, r, s

THEOREM LeadsToSelf == p ~> p
  BY PTL

THEOREM LeadsToTrans == ((p ~> q) /\ (q ~> r)) => (p ~> r)
  BY PTL

THEOREM AlwaysImpliesToLeadsTo == [](p => q) => (p ~> q)
  BY PTL

THEOREM AlwaysDouble == [][]p <=> []p
  BY PTL

THEOREM AlwaysAnd == [](p /\ q) <=> ([]p /\ []q)
  BY PTL

THEOREM AlwaysEntailsCurrent == []p => p
  BY PTL

THEOREM AlwaysPIsStable == []p => [][]p
  BY PTL

THEOREM LeadsToIsStable == (p ~> q) => [](p ~> q)
  BY PTL

THEOREM LeadsToEliminateAlways == (p ~> []q) => (p ~> q)
  BY PTL

THEOREM TrueLeadsToEventuallyAlways == (TRUE ~> []p) <=> <>[]p
  BY PTL

THEOREM FalseLeadsToAnything == FALSE ~> p
  BY PTL

THEOREM EventuallyTrue == <>TRUE
  BY PTL

THEOREM LeadsToWeakenPremise == (p ~> q) => ((p /\ r) ~> q)
  BY PTL

THEOREM OrLeadsTo == ((p ~> r) /\ (q ~> r)) => ((p \/ q) ~> r)
  BY PTL

THEOREM LeadsToFramedByOr == (p ~> q) => ((p \/ r) ~> (q \/ r))
  BY PTL

THEOREM LeadsToShortcut ==
  ((p ~> (q \/ s)) /\ (q ~> (r \/ s))) => (p ~> (r \/ s))
  BY PTL

THEOREM AlwaysImpliedEventually == p => <>p
  BY PTL

THEOREM AlwaysMonotonic == [](p => q) => ([]p => []q)
  BY PTL

THEOREM AlwaysWeaken == ([](p => q) /\ []p) => []q
  BY PTL

THEOREM LeadsToApply == (p /\ (p ~> q)) => <>q
  BY PTL

THEOREM LeadsToWeaken ==
  ((p ~> q) /\ [](r => p) /\ [](q => s)) => (r ~> s)
  BY PTL

THEOREM LeadsToByBorrowingInv ==
  (((p /\ r) ~> q) /\ []r) => (p ~> q)
  BY PTL

THEOREM VacuousLeadsTo ==
  ([]r /\ [](p /\ r => FALSE)) => (p ~> q)
  BY PTL

THEOREM StableAnd ==
  ((p => []p) /\ (q => []q)) => ((p /\ q) => [](p /\ q))
  BY PTL

THEOREM NativeInvariantInduction ==
  (p /\ [](p => p')) => []p
  BY PTL

THEOREM NativeLeadsToStable ==
  ((p ~> q) /\ [](q => q')) => (p ~> []q)
  BY PTL

==========================================================================
