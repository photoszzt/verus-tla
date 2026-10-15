-------------------------- MODULE TemporalRankRules --------------------------
\* Leads-to induction over natural ranks and finite ascending chains.
EXTENDS TemporalMacroChainRules, TLAPS

THEOREM RankStepOne ==
  ASSUME NEW S \in SUBSET Executions,
         NEW F \in [Nat -> SUBSET Executions],
         \A n \in Nat \ {0} :
           Entails(S, LeadsTo(F[n], F[n - 1]))
  PROVE \A n \in Nat : Entails(S, LeadsTo(F[n], F[0]))
PROOF
  <1>1. DEFINE P(n) == Entails(S, LeadsTo(F[n], F[0]))
  <1>2. P(0)
    BY SMT, SpecLeadsToReflexive DEF P
  <1>3. ASSUME NEW n \in Nat, P(n)
        PROVE P(n + 1)
    BY SMT, SpecLeadsToTrans, <1>3 DEF P
  <1>4. \A n \in Nat : P(n) => P(n + 1)
    BY SMT, <1>3
  <1>5. HIDE DEF P
  <1>6. \A n \in Nat : P(n)
    BY ONLY <1>2, <1>4, NatInductionChecked, Isa
  <1>7. QED BY <1>6 DEF P

THEOREM BoundedRankStepOne ==
  ASSUME NEW Max \in Nat,
         NEW S \in SUBSET Executions,
         NEW F \in [0 .. Max -> SUBSET Executions],
         \A n \in 1 .. Max :
           Entails(S, LeadsTo(F[n], F[n - 1]))
  PROVE \A n \in 0 .. Max : Entails(S, LeadsTo(F[n], F[0]))
PROOF
  <1>1. DEFINE P(n) ==
    n <= Max => Entails(S, LeadsTo(F[n], F[0]))
  <1>2. P(0)
    BY SMT, SpecLeadsToReflexive DEF P
  <1>3. ASSUME NEW n \in Nat, P(n)
        PROVE P(n + 1)
  PROOF
    <2>1. ASSUME n + 1 <= Max
          PROVE Entails(S, LeadsTo(F[n + 1], F[0]))
    PROOF
      <3>1. n \in 0 .. Max /\ n + 1 \in 1 .. Max
        BY SMT, <2>1
      <3>2. Entails(S, LeadsTo(F[n], F[0])) /\
            Entails(S, LeadsTo(F[n + 1], F[n]))
        BY SMT, <1>3, <3>1 DEF P
      <3>3. QED BY SMT, <3>1, <3>2, SpecLeadsToTrans
    <2>2. QED BY SMT, <2>1 DEF P
  <1>4. \A n \in Nat : P(n) => P(n + 1)
    BY SMT, <1>3
  <1>5. HIDE DEF P
  <1>6. \A n \in Nat : P(n)
    BY ONLY <1>2, <1>4, NatInductionChecked, Isa
  <1>7. QED BY SMT, <1>6 DEF P

THEOREM AscendingChainToEnd ==
  ASSUME NEW Max \in Nat,
         NEW S \in SUBSET Executions,
         NEW F \in [0 .. Max -> SUBSET Executions],
         \A i \in 0 .. (Max - 1) :
           Entails(S, LeadsTo(F[i], F[i + 1]))
  PROVE \A n \in 0 .. Max :
    Entails(S, LeadsTo(F[n], F[Max]))
PROOF
  <1>1. DEFINE P(j) ==
    j <= Max =>
      (\A i \in 0 .. j : Entails(S, LeadsTo(F[i], F[j])))
  <1>2. P(0)
    BY SMT, SpecLeadsToReflexive DEF P
  <1>3. ASSUME NEW j \in Nat, P(j)
        PROVE P(j + 1)
  PROOF
    <2>1. ASSUME j + 1 <= Max
          PROVE \A i \in 0 .. (j + 1) :
            Entails(S, LeadsTo(F[i], F[j + 1]))
    PROOF
      <3>1. ASSUME NEW i \in 0 .. (j + 1)
            PROVE Entails(S, LeadsTo(F[i], F[j + 1]))
      PROOF
        <4>1. CASE i = j + 1
          BY SMT, <4>1, <2>1, SpecLeadsToReflexive
        <4>2. CASE i # j + 1
        PROOF
          <5>1. i \in 0 .. j /\ j \in 0 .. (Max - 1)
            BY SMT, <3>1, <4>2, <2>1
          <5>2. Entails(S, LeadsTo(F[i], F[j])) /\
                Entails(S, LeadsTo(F[j], F[j + 1]))
            BY SMT, <1>3, <5>1 DEF P
          <5>3. QED BY SMT, <5>1, <5>2, SpecLeadsToTrans
        <4>3. QED BY <4>1, <4>2
      <3>2. QED BY <3>1
    <2>2. QED BY SMT, <2>1 DEF P
  <1>4. \A j \in Nat : P(j) => P(j + 1)
    BY SMT, <1>3
  <1>5. HIDE DEF P
  <1>6. \A j \in Nat : P(j)
    BY ONLY <1>2, <1>4, NatInductionChecked, Isa
  <1>7. QED BY SMT, <1>6 DEF P

THEOREM LeadsToGreaterUntil ==
  ASSUME NEW Max \in Nat,
         NEW S \in SUBSET Executions,
         NEW P \in SUBSET Executions,
         NEW F \in [0 .. Max -> SUBSET Executions],
         Entails(P, Exists(0 .. Max, F)),
         \A i \in 0 .. (Max - 1) :
           Entails(S, LeadsTo(F[i], F[i + 1]))
  PROVE Entails(S, LeadsTo(P, F[Max]))
PROOF
  <1>1. \A n \in 0 .. Max :
    Entails(S, LeadsTo(F[n], F[Max]))
    BY AscendingChainToEnd
  <1>2. Entails(S, LeadsTo(Exists(0 .. Max, F), F[Max]))
    BY SMT, <1>1, LeadsToExistsIntro
  <1>3. Entails(S, Always(Implies(P, Exists(0 .. Max, F))))
    BY SMT, SuffixType DEF Entails, Always, Implies
  <1>4. Entails(S, Always(Implies(F[Max], F[Max])))
    BY SMT, SuffixType DEF Entails, Always, Implies
  <1>5. Exists(0 .. Max, F) \in SUBSET Executions /\
        F[Max] \in SUBSET Executions
    BY SMT DEF Exists
  <1>6. QED BY SMT, <1>2, <1>3, <1>4, <1>5, LeadsToWeaken
===========================================================================
