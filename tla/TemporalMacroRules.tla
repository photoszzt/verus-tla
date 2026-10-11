-------------------------- MODULE TemporalMacroRules --------------------------
\* Finite macro argument lists are represented by their set of predicates.
\* Conjunction is insensitive to order and duplicate arguments.
EXTENDS TemporalSetRules, TLAPS

Conjoin(C) == {ex \in Executions : \A P \in C : ex \in P}
Disjoin(C) == {ex \in Executions : \E P \in C : ex \in P}
MergedAction(A, C) ==
  {pair \in States \X States :
    pair \in A /\ \A I \in C : pair[1] \in I}

THEOREM ConjoinType ==
  \A C : Conjoin(C) \subseteq Executions
  BY DEF Conjoin

THEOREM ConjoinPair ==
  \A P, Q \in SUBSET Executions : Conjoin({P, Q}) = And(P, Q)
  BY SMT DEF Conjoin, And

THEOREM ConjoinAdd ==
  \A C \in SUBSET (SUBSET Executions) :
  \A P \in SUBSET Executions :
    Conjoin(C \cup {P}) = And(Conjoin(C), P)
  BY SMT DEF Conjoin, And

THEOREM AlwaysConjoinAt ==
  \A C \in SUBSET (SUBSET Executions) :
  \A ex \in Executions :
    (ex \in Always(Conjoin(C)) <=>
     \A P \in C : ex \in Always(P))
  BY SMT, SuffixType DEF Always, Conjoin

THEOREM ConjoinAlwaysImageAt ==
  \A C \in SUBSET (SUBSET Executions) :
  \A ex \in Executions :
    (ex \in Conjoin({Always(P) : P \in C}) <=>
     \A P \in C : ex \in Always(P))
  BY SMT DEF Conjoin

THEOREM AlwaysConjoin ==
  \A C \in SUBSET (SUBSET Executions) :
    Always(Conjoin(C)) = Conjoin({Always(P) : P \in C})
  BY SMT, AlwaysConjoinAt, ConjoinAlwaysImageAt,
    SetExtensionality DEF Always, Conjoin

THEOREM EntailsConjoin ==
  \A S \in SUBSET Executions :
  \A C \in SUBSET (SUBSET Executions) :
    (\A P \in C : Entails(S, P)) => Entails(S, Conjoin(C))
  BY SMT DEF Entails, Conjoin

THEOREM EntailsAlwaysConjoin ==
  \A S \in SUBSET Executions :
  \A C \in SUBSET (SUBSET Executions) :
    (\A P \in C : Entails(S, Always(P))) =>
      Entails(S, Always(Conjoin(C)))
  BY SMT, AlwaysConjoin DEF Entails, Conjoin, Always

THEOREM AlwaysUnpackConjoin ==
  \A S, Inv \in SUBSET Executions :
  \A C \in SUBSET (SUBSET Executions) :
    (Entails(S, Always(Inv)) /\
     (\A P \in C : Entails(Inv, P))) =>
      (\A P \in C : Entails(S, Always(P)))
  BY SMT DEF Entails, Always

THEOREM StableConjoin ==
  \A C \in SUBSET (SUBSET Executions) :
    (\A P \in C : Valid(Stable(P))) => Valid(Stable(Conjoin(C)))
  BY SMT, SuffixType DEF Valid, Stable, Implies, Always, Conjoin

THEOREM InvariantConjoin ==
  \A S, Partial, Inv \in SUBSET Executions :
  \A C \in SUBSET (SUBSET Executions) :
    ((\A P \in C : Entails(S, Always(P))) /\
     Entails(Conjoin(C), Partial) /\
     Entails(Partial, Inv)) =>
      Entails(S, Always(Inv))
  BY SMT, EntailsAlwaysConjoin DEF Entails, Always, Conjoin

THEOREM StableAlwaysConjoin ==
  \A C \in SUBSET (SUBSET Executions) :
    Valid(Stable(Conjoin({Always(P) : P \in C})))
  BY SMT, AlwaysConjoin, AlwaysPIsStable, ConjoinType
    DEF Valid, Stable

THEOREM CombineWithNext ==
  \A Next \in SUBSET Executions :
  \A C \in SUBSET (SUBSET Executions) :
    Conjoin(C \cup {Next}) = And(Next, Conjoin(C))
  BY SMT DEF Conjoin, And

THEOREM CombineSpecEntails ==
  \A S, Partial \in SUBSET Executions :
  \A C \in SUBSET (SUBSET Executions) :
    ((\A P \in C : Entails(S, P)) /\
     Entails(Conjoin(C), Partial)) => Entails(S, Partial)
  BY SMT, EntailsConjoin DEF Entails

THEOREM CombineSpecEntailsAlways ==
  \A S, Partial \in SUBSET Executions :
  \A C \in SUBSET (SUBSET Executions) :
    ((\A P \in C : Entails(S, Always(P))) /\
     Entails(Conjoin(C), Partial)) =>
      Entails(S, Always(Partial))
  BY SMT, EntailsAlwaysConjoin DEF Entails, Always, Conjoin

THEOREM DisjoinPair ==
  \A P, Q \in SUBSET Executions : Disjoin({P, Q}) = Or(P, Q)
  BY SMT DEF Disjoin, Or

THEOREM DisjoinAdd ==
  \A C \in SUBSET (SUBSET Executions) :
  \A P \in SUBSET Executions :
    Disjoin(C \cup {P}) = Or(Disjoin(C), P)
  BY SMT DEF Disjoin, Or

THEOREM OrLeadsToFamily ==
  \A S, Q \in SUBSET Executions :
  \A C \in SUBSET (SUBSET Executions) :
    (\A P \in C : Entails(S, LeadsTo(P, Q))) =>
      Entails(S, LeadsTo(Disjoin(C), Q))
  BY SMT, SuffixType
    DEF Entails, LeadsTo, Always, Implies, Eventually, Disjoin

THEOREM OrLeadsToNamedResult ==
  \A S, Q, Result \in SUBSET Executions :
  \A C \in SUBSET (SUBSET Executions) :
    ((\A P \in C : Entails(S, LeadsTo(P, Q))) /\
     Result = Disjoin(C)) => Entails(S, LeadsTo(Result, Q))
  BY SMT, OrLeadsToFamily

THEOREM MergedActionAt ==
  \A A \in SUBSET (States \X States) :
  \A C \in SUBSET (SUBSET States) :
  \A s, t \in States :
    (<<s, t>> \in MergedAction(A, C) <=>
     (<<s, t>> \in A /\ \A I \in C : s \in I))
  BY SMT DEF MergedAction

THEOREM HeadsType ==
  \A ex \in Executions :
    Head(ex) \in States /\ HeadNext(ex) \in States
  BY SMT DEF Executions, Head, HeadNext

THEOREM LiftStateImageAt ==
  \A C \in SUBSET (SUBSET States) :
  \A ex \in Executions :
    (ex \in Conjoin({LiftState(I) : I \in C}) <=>
     \A I \in C : Head(ex) \in I)
  BY SMT DEF Conjoin, LiftState

THEOREM LiftMergedActionAt ==
  \A A \in SUBSET (States \X States) :
  \A C \in SUBSET (SUBSET States) :
  \A ex \in Executions :
    (ex \in LiftAction(MergedAction(A, C)) <=>
     ex \in And(LiftAction(A),
       Conjoin({LiftState(I) : I \in C})))
  BY SMT, MergedActionAt, HeadsType, LiftStateImageAt
    DEF LiftAction, LiftState, Conjoin, And

THEOREM LiftMergedAction ==
  \A A \in SUBSET (States \X States) :
  \A C \in SUBSET (SUBSET States) :
    LiftAction(MergedAction(A, C)) =
      And(LiftAction(A), Conjoin({LiftState(I) : I \in C}))
  BY SMT, LiftMergedActionAt, SetExtensionality
    DEF LiftAction, LiftState, Conjoin, And

===========================================================================
