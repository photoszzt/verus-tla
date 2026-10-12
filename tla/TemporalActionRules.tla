------------------------- MODULE TemporalActionRules -------------------------
\* Exact action-preservation laws for the behavior-set interpretation.
EXTENDS TemporalSetRules, TLAPS

IdentityAction == {<<s, s>> : s \in States}
StutteringClosure(A) == A \cup IdentityAction
LiftFamily(D, F) == [a \in D |-> LiftState(F[a])]
PersistentFamily(D, F) == [a \in D |-> Always(LiftState(F[a]))]

THEOREM NatInductionChecked ==
  ASSUME NEW P(_), P(0), \A n \in Nat : P(n) => P(n + 1)
  PROVE \A n \in Nat : P(n)
  BY IsaM("(intro natInduct, auto)")

THEOREM NextToStableAt ==
  ASSUME NEW A \in SUBSET (States \X States),
         NEW I \in SUBSET States,
         NEW ex \in Executions,
         \A s, t \in States :
           (<<s, t>> \in A /\ s \in I) => t \in I,
         ex \in Always(LiftAction(A)),
         ex \in LiftState(I)
  PROVE \A n \in Nat : Suffix(ex, n) \in LiftState(I)
PROOF
  <1>1. DEFINE P(n) == Suffix(ex, n) \in LiftState(I)
  <1>2. P(0)
    BY SMT, SuffixZero DEF P
  <1>3. ASSUME NEW n \in Nat, P(n)
        PROVE P(n + 1)
  PROOF
    <2>1. Suffix(ex, n) \in LiftAction(A)
      BY SMT, SuffixType DEF Always
    <2>2. Head(Suffix(ex, n)) \in I
      BY SMT, <1>3, SuffixType DEF P, LiftState
    <2>3. HeadNext(Suffix(ex, n)) \in I
      BY SMT, <2>1, <2>2, SuffixType DEF LiftAction
    <2>4. HeadNext(Suffix(ex, n)) = Head(Suffix(ex, n + 1))
      BY SMT DEF Suffix, Head, HeadNext
    <2>5. QED BY SMT, <2>3, <2>4, SuffixType DEF P, LiftState
  <1>4. \A n \in Nat : P(n) => P(n + 1)
    BY SMT, <1>3
  <1>5. HIDE DEF P
  <1>6. \A n \in Nat : P(n)
    BY ONLY <1>2, <1>4, NatInductionChecked, Isa
  <1>7. QED BY <1>6 DEF P

THEOREM NextToStable ==
  ASSUME NEW A \in SUBSET (States \X States),
         NEW I \in SUBSET States,
         \A s, t \in States :
           (<<s, t>> \in A /\ s \in I) => t \in I
  PROVE Entails(Always(LiftAction(A)), Stable(LiftState(I)))
  BY SMT, NextToStableAt DEF Entails, Stable, Implies, Always

THEOREM InitInvariant ==
  ASSUME NEW A \in SUBSET (States \X States),
         NEW InitStates \in SUBSET States,
         NEW I \in SUBSET States,
         NEW S \in SUBSET Executions,
         InitStates \subseteq I,
         \A s, t \in States :
           (<<s, t>> \in A /\ s \in I) => t \in I,
         Entails(S, LiftState(InitStates)),
         Entails(S, Always(LiftAction(A)))
  PROVE Entails(S, Always(LiftState(I)))
PROOF
  <1>1. LiftState(InitStates) \subseteq LiftState(I)
    BY SMT DEF LiftState
  <1>2. Entails(S, LiftState(I))
    BY SMT, <1>1 DEF Entails
  <1>3. Entails(Always(LiftAction(A)), Stable(LiftState(I)))
    BY NextToStable
  <1>4. Entails(S, Stable(LiftState(I)))
    BY SMT, <1>3 DEF Entails
  <1>5. QED BY SMT, <1>2, <1>4 DEF Entails, Stable, Implies

THEOREM StutteringClosurePreserves ==
  \A A \in SUBSET (States \X States) :
  \A I \in SUBSET States :
    (\A s, t \in States : (<<s, t>> \in A /\ s \in I) => t \in I) =>
      (\A s, t \in States :
        (<<s, t>> \in StutteringClosure(A) /\ s \in I) => t \in I)
  BY SMT DEF StutteringClosure, IdentityAction

THEOREM NextToStableStuttering ==
  ASSUME NEW A \in SUBSET (States \X States),
         NEW I \in SUBSET States,
         \A s, t \in States :
           (<<s, t>> \in A /\ s \in I) => t \in I
  PROVE Entails(Always(LiftAction(StutteringClosure(A))),
                  Stable(LiftState(I)))
  BY SMT, StutteringClosurePreserves, NextToStable
    DEF StutteringClosure, IdentityAction

THEOREM InitInvariantStuttering ==
  ASSUME NEW A \in SUBSET (States \X States),
         NEW InitStates \in SUBSET States,
         NEW I \in SUBSET States,
         NEW S \in SUBSET Executions,
         InitStates \subseteq I,
         \A s, t \in States :
           (<<s, t>> \in A /\ s \in I) => t \in I,
         Entails(S, LiftState(InitStates)),
         Entails(S, Always(LiftAction(StutteringClosure(A))))
  PROVE Entails(S, Always(LiftState(I)))
  BY SMT, StutteringClosurePreserves, InitInvariant
    DEF StutteringClosure, IdentityAction

THEOREM TemporalPreservationAt ==
  ASSUME NEW Q \in SUBSET Executions,
         NEW N \in SUBSET Executions,
         NEW ex \in Executions,
         ex \in Always(Implies(And(Q, N), Later(Q))),
         ex \in Always(N),
         ex \in Q
  PROVE ex \in Always(Q)
PROOF
  <1>1. DEFINE P(n) == Suffix(ex, n) \in Q
  <1>2. P(0) BY SMT, SuffixZero DEF P
  <1>3. ASSUME NEW n \in Nat, P(n)
        PROVE P(n + 1)
  PROOF
    <2>1. Suffix(ex, n) \in Implies(And(Q, N), Later(Q))
      BY SMT DEF Always
    <2>2. Suffix(ex, n) \in N
      BY SMT DEF Always
    <2>3. Suffix(ex, n) \in And(Q, N)
      BY SMT, <1>3, <2>2 DEF P, And
    <2>4. Suffix(ex, n) \in Later(Q)
      BY SMT, <2>1, <2>3, SuffixType DEF Implies
    <2>5. QED BY SMT, <2>4, SuffixAssoc DEF P, Later
  <1>4. \A n \in Nat : P(n) => P(n + 1)
    BY SMT, <1>3
  <1>5. HIDE DEF P
  <1>6. \A n \in Nat : P(n)
    BY ONLY <1>2, <1>4, NatInductionChecked, Isa
  <1>7. QED BY <1>6 DEF Always, P

THEOREM TemporalPreservationGlobal ==
  ASSUME NEW S \in SUBSET Executions,
         NEW Q \in SUBSET Executions,
         NEW N \in SUBSET Executions,
         Entails(S, Always(Implies(And(Q, N), Later(Q)))),
         Entails(S, Always(N))
  PROVE Entails(S, Always(Stable(Q)))
PROOF
  <1>1. ASSUME NEW ex \in S
        PROVE ex \in Always(Stable(Q))
  PROOF
    <2>1. ex \in Executions /\
          ex \in Always(Implies(And(Q, N), Later(Q))) /\
          ex \in Always(N)
      BY SMT DEF Entails
    <2>2. \A i \in Nat : Suffix(ex, i) \in Stable(Q)
    PROOF
      <3>1. ASSUME NEW i \in Nat
            PROVE Suffix(ex, i) \in Stable(Q)
      PROOF
        <4>1. Suffix(ex, i) \in Executions /\
              Suffix(ex, i) \in Always(Implies(And(Q, N), Later(Q))) /\
              Suffix(ex, i) \in Always(N)
          BY SMT, <2>1, SuffixType, AlwaysSuffix
        <4>2. Suffix(ex, i) \in Q =>
              Suffix(ex, i) \in Always(Q)
          BY SMT, <4>1, TemporalPreservationAt
        <4>3. QED BY SMT, <4>1, <4>2 DEF Stable, Implies
      <3>2. QED BY <3>1
    <2>3. QED BY SMT, <2>1, <2>2 DEF Always
  <1>2. QED BY SMT, <1>1 DEF Entails

THEOREM LeadsToStable ==
  \A S, P, Q, N \in SUBSET Executions :
    (Entails(S, Always(Implies(And(Q, N), Later(Q)))) /\
     Entails(S, Always(N)) /\
     Entails(S, LeadsTo(P, Q))) =>
       Entails(S, LeadsTo(P, Always(Q)))
  BY SMT, TemporalPreservationGlobal, LeadsToWeaken, AlwaysType
    DEF Entails, Stable, Implies, Always

THEOREM ActionPreservesExistsAt ==
  ASSUME NEW A \in SUBSET (States \X States),
         NEW D,
         NEW F \in [D -> SUBSET States],
         NEW ex \in Executions,
         \A a \in D : \A s, t \in States :
           (<<s, t>> \in A /\ s \in F[a]) => t \in F[a],
         ex \in Always(LiftAction(A)),
         ex \in Exists(D, LiftFamily(D, F))
  PROVE ex \in Exists(D, PersistentFamily(D, F))
PROOF
  <1>1. \E a \in D : ex \in LiftState(F[a])
    BY SMT DEF Exists, LiftFamily
  <1>2. ASSUME NEW a \in D, ex \in LiftState(F[a])
        PROVE ex \in Exists(D, PersistentFamily(D, F))
  PROOF
    <2>1. F[a] \in SUBSET States /\
          (\A s, t \in States :
            (<<s, t>> \in A /\ s \in F[a]) => t \in F[a])
      BY SMT
    <2>2. \A n \in Nat : Suffix(ex, n) \in LiftState(F[a])
      BY SMT, NextToStableAt, <1>2, <2>1
    <2>3. ex \in Always(LiftState(F[a]))
      BY SMT, <2>2 DEF Always
    <2>4. QED BY SMT, <2>3 DEF Exists, PersistentFamily
  <1>3. QED BY SMT, <1>1, <1>2

THEOREM EntailsExistsStable ==
  ASSUME NEW A \in SUBSET (States \X States),
         NEW D,
         NEW F \in [D -> SUBSET States],
         NEW S \in SUBSET Executions,
         \A a \in D : \A s, t \in States :
           (<<s, t>> \in A /\ s \in F[a]) => t \in F[a],
         Entails(S, Exists(D, LiftFamily(D, F))),
         Entails(S, Always(LiftAction(A)))
  PROVE Entails(S, Exists(D, PersistentFamily(D, F)))
  BY SMT, ActionPreservesExistsAt DEF Entails

THEOREM LeadsToExistsStable ==
  ASSUME NEW A \in SUBSET (States \X States),
         NEW D,
         NEW F \in [D -> SUBSET States],
         NEW S \in SUBSET Executions,
         NEW P \in SUBSET Executions,
         \A a \in D : \A s, t \in States :
           (<<s, t>> \in A /\ s \in F[a]) => t \in F[a],
         Entails(S, Always(LiftAction(A))),
         Entails(S, LeadsTo(P, Exists(D, LiftFamily(D, F))))
  PROVE Entails(S, LeadsTo(P, Exists(D, PersistentFamily(D, F))))
PROOF
  <1>1. DEFINE Q == Exists(D, LiftFamily(D, F))
  <1>2. DEFINE R == Exists(D, PersistentFamily(D, F))
  <1>3. Q \in SUBSET Executions /\ R \in SUBSET Executions
    BY SMT DEF Q, R, Exists, LiftFamily, PersistentFamily, Always
  <1>4. Entails(S, Always(Implies(Q, R)))
  PROOF
    <2>1. ASSUME NEW ex \in S
          PROVE ex \in Always(Implies(Q, R))
    PROOF
      <3>1. ex \in Executions /\ ex \in Always(LiftAction(A))
        BY SMT DEF Entails
      <3>2. \A i \in Nat : Suffix(ex, i) \in Implies(Q, R)
      PROOF
        <4>1. ASSUME NEW i \in Nat
              PROVE Suffix(ex, i) \in Implies(Q, R)
        PROOF
          <5>1. Suffix(ex, i) \in Executions /\
                Suffix(ex, i) \in Always(LiftAction(A))
            BY SMT, <3>1, SuffixType, AlwaysSuffix
          <5>2. Suffix(ex, i) \in Q => Suffix(ex, i) \in R
            BY SMT, <5>1, ActionPreservesExistsAt DEF Q, R
          <5>3. QED BY SMT, <5>1, <5>2 DEF Implies
        <4>2. QED BY <4>1
      <3>3. QED BY SMT, <3>1, <3>2 DEF Always
    <2>2. QED BY SMT, <2>1 DEF Entails
  <1>5. Entails(S, Always(Implies(P, P)))
    BY SMT, SuffixType DEF Entails, Always, Implies
  <1>6. QED BY SMT, <1>3, <1>4, <1>5, LeadsToWeaken
    DEF Q, R
===========================================================================
