---------------------- MODULE TemporalMacroChainRules ----------------------
\* Finite proof-script macro expansions, with their source minimum arities.
EXTENDS TemporalFoldRules, TLAPS

THEOREM SpecLeadsToReflexive ==
  \A S, P \in SUBSET Executions : Entails(S, LeadsTo(P, P))
  BY SMT, LeadsToSelf DEF Entails, Valid

THEOREM SpecLeadsToTrans ==
  \A S, P, Q, R \in SUBSET Executions :
    (Entails(S, LeadsTo(P, Q)) /\ Entails(S, LeadsTo(Q, R))) =>
      Entails(S, LeadsTo(P, R))
  BY SMT, LeadsToTrans, LeadsToType DEF Entails, And

THEOREM EntailsFiniteChain ==
  ASSUME NEW Ps \in Seq(SUBSET Executions),
         Len(Ps) >= 3,
         \A i \in 1 .. (Len(Ps) - 1) : Entails(Ps[i], Ps[i + 1])
  PROVE Entails(Ps[1], Ps[Len(Ps)])
PROOF
  <1>1. DEFINE P(n) ==
    (1 <= n /\ n <= Len(Ps)) => Entails(Ps[1], Ps[n])
  <1>2. P(0) BY SMT DEF P
  <1>3. ASSUME NEW n \in Nat, P(n)
        PROVE P(n + 1)
  PROOF
    <2>1. ASSUME 1 <= n + 1 /\ n + 1 <= Len(Ps)
          PROVE Entails(Ps[1], Ps[n + 1])
    PROOF
      <3>1. CASE n = 0
        BY SMT, EntailsReflexive, <2>1, <3>1
      <3>2. CASE n # 0
      PROOF
        <4>1. n \in 1 .. (Len(Ps) - 1)
          BY SMT, <2>1, <3>2
        <4>2. Entails(Ps[1], Ps[n]) /\ Entails(Ps[n], Ps[n + 1])
          BY SMT, <1>3, <4>1 DEF P
        <4>3. QED BY SMT, <4>1, <4>2, EntailsTrans
      <3>3. QED BY <3>1, <3>2
    <2>2. QED BY SMT, <2>1 DEF P
  <1>4. \A n \in Nat : P(n) => P(n + 1)
    BY SMT, <1>3
  <1>5. HIDE DEF P
  <1>6. \A n \in Nat : P(n)
    BY ONLY <1>2, <1>4, NatInductionChecked, Isa
  <1>7. QED BY SMT, <1>6 DEF P

THEOREM LeadsToFiniteChain ==
  ASSUME NEW S \in SUBSET Executions,
         NEW Ps \in Seq(SUBSET Executions),
         Len(Ps) >= 3,
         \A i \in 1 .. (Len(Ps) - 1) :
           Entails(S, LeadsTo(Ps[i], Ps[i + 1]))
  PROVE Entails(S, LeadsTo(Ps[1], Ps[Len(Ps)]))
PROOF
  <1>1. DEFINE P(n) ==
    (1 <= n /\ n <= Len(Ps)) =>
      Entails(S, LeadsTo(Ps[1], Ps[n]))
  <1>2. P(0) BY SMT DEF P
  <1>3. ASSUME NEW n \in Nat, P(n)
        PROVE P(n + 1)
  PROOF
    <2>1. ASSUME 1 <= n + 1 /\ n + 1 <= Len(Ps)
          PROVE Entails(S, LeadsTo(Ps[1], Ps[n + 1]))
    PROOF
      <3>1. CASE n = 0
        BY SMT, SpecLeadsToReflexive, <2>1, <3>1
      <3>2. CASE n # 0
      PROOF
        <4>1. n \in 1 .. (Len(Ps) - 1)
          BY SMT, <2>1, <3>2
        <4>2. Entails(S, LeadsTo(Ps[1], Ps[n])) /\
              Entails(S, LeadsTo(Ps[n], Ps[n + 1]))
          BY SMT, <1>3, <4>1 DEF P
        <4>3. QED BY SMT, <4>1, <4>2, SpecLeadsToTrans
      <3>3. QED BY <3>1, <3>2
    <2>2. QED BY SMT, <2>1 DEF P
  <1>4. \A n \in Nat : P(n) => P(n + 1)
    BY SMT, <1>3
  <1>5. HIDE DEF P
  <1>6. \A n \in Nat : P(n)
    BY ONLY <1>2, <1>4, NatInductionChecked, Isa
  <1>7. QED BY SMT, <1>6 DEF P

THEOREM LeadsToAlwaysFiniteConjoin ==
  ASSUME NEW S \in SUBSET Executions,
         NEW Trigger \in SUBSET Executions,
         NEW Qs \in Seq(SUBSET Executions),
         Len(Qs) >= 2,
         \A i \in 1 .. Len(Qs) :
           Entails(S, LeadsTo(Trigger, Always(Qs[i])))
  PROVE Entails(S,
    LeadsTo(Trigger, Always(Conjoin(PrefixSet(Qs, Len(Qs))))))
PROOF
  <1>1. DEFINE P(n) ==
    (1 <= n /\ n <= Len(Qs)) =>
      Entails(S,
        LeadsTo(Trigger, Always(Conjoin(PrefixSet(Qs, n)))))
  <1>2. P(0) BY SMT DEF P
  <1>3. ASSUME NEW n \in Nat, P(n)
        PROVE P(n + 1)
  PROOF
    <2>1. ASSUME 1 <= n + 1 /\ n + 1 <= Len(Qs)
          PROVE Entails(S,
            LeadsTo(Trigger, Always(Conjoin(PrefixSet(Qs, n + 1)))))
    PROOF
      <3>1. CASE n = 0
      PROOF
        <4>1. n + 1 = 1 /\ 1 \in 1 .. Len(Qs)
          BY SMT, <3>1, <2>1
        <4>2. Qs[1] \in SUBSET Executions
          BY SMT, <4>1
        <4>3. PrefixSet(Qs, 1) = {Qs[1]}
          BY SMT DEF PrefixSet
        <4>4. Conjoin(PrefixSet(Qs, 1)) = Qs[1]
          BY SMT, <4>2, <4>3 DEF Conjoin
        <4>5. Entails(S, LeadsTo(Trigger, Always(Qs[1])))
          BY SMT, <4>1
        <4>6. QED BY SMT, <4>1, <4>4, <4>5
      <3>2. CASE n # 0
      PROOF
        <4>1. n \in 1 .. (Len(Qs) - 1) /\
              n + 1 \in 1 .. Len(Qs)
          BY SMT, <2>1, <3>2
        <4>2. Entails(S,
          LeadsTo(Trigger, Always(Conjoin(PrefixSet(Qs, n))))) /\
          Entails(S, LeadsTo(Trigger, Always(Qs[n + 1])))
          BY SMT, <1>3, <4>1 DEF P
        <4>3. PrefixSet(Qs, n + 1) =
              PrefixSet(Qs, n) \cup {Qs[n + 1]}
          BY SMT, PrefixSetAdd, <4>1
        <4>4. Qs[n + 1] \in SUBSET Executions /\
              PrefixSet(Qs, n) \in SUBSET (SUBSET Executions)
          BY SMT, <4>1 DEF PrefixSet
        <4>5. Conjoin(PrefixSet(Qs, n + 1)) =
              And(Conjoin(PrefixSet(Qs, n)), Qs[n + 1])
          BY SMT, ConjoinAdd, <4>3, <4>4
        <4>6. QED BY SMT, LeadsToAlwaysAnd, <4>2, <4>4, <4>5,
          ConjoinType
      <3>3. QED BY <3>1, <3>2
    <2>2. QED BY SMT, <2>1 DEF P
  <1>4. \A n \in Nat : P(n) => P(n + 1)
    BY SMT, <1>3
  <1>5. HIDE DEF P
  <1>6. \A n \in Nat : P(n)
    BY ONLY <1>2, <1>4, NatInductionChecked, Isa
  <1>7. QED BY SMT, <1>6 DEF P
===========================================================================
===========================================================================
