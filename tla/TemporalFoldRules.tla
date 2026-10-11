-------------------------- MODULE TemporalFoldRules --------------------------
\* A trace F records the successive results of an ordered macro .and fold.
EXTENDS TemporalMacroRules, Sequences, TLAPS

PrefixSet(Ps, n) == {Ps[i] : i \in 1 .. n}
AndTrace(Ps) ==
  [i \in 0 .. Len(Ps) |-> Conjoin(PrefixSet(Ps, i))]
OrTrace(Ps) ==
  [i \in 0 .. Len(Ps) |-> Disjoin(PrefixSet(Ps, i))]
ActionTrace(A, Is) ==
  [i \in 0 .. Len(Is) |-> MergedAction(A, PrefixSet(Is, i))]

THEOREM NatInductionChecked ==
  ASSUME NEW P(_), P(0), \A n \in Nat : P(n) => P(n + 1)
  PROVE \A n \in Nat : P(n)
  BY IsaM("(intro natInduct, auto)")

THEOREM PrefixSetAdd ==
  \A V : \A Ps \in Seq(V) :
  \A n \in 0 .. (Len(Ps) - 1) :
    PrefixSet(Ps, n + 1) = PrefixSet(Ps, n) \cup {Ps[n + 1]}
  BY SMT DEF PrefixSet

THEOREM SeqLenNat ==
  \A S : \A s \in Seq(S) : Len(s) \in Nat
  BY SMT

THEOREM AndTraceRecurrence ==
  ASSUME NEW Ps \in Seq(SUBSET Executions)
  PROVE
    /\ AndTrace(Ps) \in [0 .. Len(Ps) -> SUBSET Executions]
    /\ AndTrace(Ps)[0] = Executions
    /\ \A i \in 1 .. Len(Ps) :
         AndTrace(Ps)[i] = And(AndTrace(Ps)[i - 1], Ps[i])
PROOF
  <1>1. AndTrace(Ps) \in [0 .. Len(Ps) -> SUBSET Executions]
    BY SMT, ConjoinType DEF AndTrace, PrefixSet, Conjoin
  <1>2. AndTrace(Ps)[0] = Executions
  PROOF
    <2>1. Len(Ps) \in Nat /\ 0 \in 0 .. Len(Ps)
      BY SMT, SeqLenNat
    <2>2. PrefixSet(Ps, 0) = {}
      BY SMT DEF PrefixSet
    <2>3. AndTrace(Ps)[0] = Conjoin(PrefixSet(Ps, 0))
      BY SMT, <2>1 DEF AndTrace
    <2>4. QED BY <2>2, <2>3, ConjoinEmpty
  <1>3. \A i \in 1 .. Len(Ps) :
    AndTrace(Ps)[i] = And(AndTrace(Ps)[i - 1], Ps[i])
    BY SMT, ConjoinAdd, PrefixSetAdd
      DEF AndTrace, PrefixSet, Conjoin, And
  <1>4. QED BY <1>1, <1>2, <1>3

THEOREM OrTraceRecurrence ==
  ASSUME NEW Ps \in Seq(SUBSET Executions)
  PROVE
    /\ OrTrace(Ps) \in [0 .. Len(Ps) -> SUBSET Executions]
    /\ OrTrace(Ps)[0] = {}
    /\ \A i \in 1 .. Len(Ps) :
         OrTrace(Ps)[i] = Or(OrTrace(Ps)[i - 1], Ps[i])
  BY SMT, DisjoinAdd, PrefixSetAdd
    DEF OrTrace, PrefixSet, Disjoin, Or

THEOREM ActionTraceRecurrence ==
  ASSUME NEW A \in SUBSET (States \X States),
         NEW Is \in Seq(SUBSET States)
  PROVE
    /\ ActionTrace(A, Is) \in
         [0 .. Len(Is) -> SUBSET (States \X States)]
    /\ ActionTrace(A, Is)[0] = A
    /\ \A i \in 1 .. Len(Is) :
         ActionTrace(A, Is)[i] =
           {pair \in States \X States :
             pair \in ActionTrace(A, Is)[i - 1] /\ pair[1] \in Is[i]}
PROOF
  <1>1. ActionTrace(A, Is) \in
    [0 .. Len(Is) -> SUBSET (States \X States)]
    BY SMT DEF ActionTrace, PrefixSet, MergedAction
  <1>2. ActionTrace(A, Is)[0] = A
  PROOF
    <2>1. Len(Is) \in Nat /\ 0 \in 0 .. Len(Is)
      BY SMT, SeqLenNat
    <2>2. PrefixSet(Is, 0) = {}
      BY SMT DEF PrefixSet
    <2>3. ActionTrace(A, Is)[0] = MergedAction(A, PrefixSet(Is, 0))
      BY SMT, <2>1 DEF ActionTrace
    <2>4. QED BY <2>2, <2>3, MergedActionEmpty
  <1>3. \A i \in 1 .. Len(Is) :
    ActionTrace(A, Is)[i] =
      {pair \in States \X States :
        pair \in ActionTrace(A, Is)[i - 1] /\ pair[1] \in Is[i]}
    BY SMT, MergedActionAdd, PrefixSetAdd
      DEF ActionTrace, PrefixSet, MergedAction
  <1>4. QED BY <1>1, <1>2, <1>3

THEOREM FoldAndTraceCorrespondence ==
  ASSUME NEW Ps \in Seq(SUBSET Executions),
         NEW F \in [0 .. Len(Ps) -> SUBSET Executions],
         F[0] = Executions,
         \A i \in 1 .. Len(Ps) :
           F[i] = And(F[i - 1], Ps[i])
  PROVE \A n \in 0 .. Len(Ps) :
    F[n] = Conjoin(PrefixSet(Ps, n))
PROOF
  <1>1. DEFINE P(n) ==
    n \leq Len(Ps) => F[n] = Conjoin(PrefixSet(Ps, n))
  <1>2. P(0)
    BY SMT DEF P, PrefixSet, Conjoin
  <1>3. ASSUME NEW n \in Nat, P(n)
        PROVE P(n + 1)
  PROOF
    <2>1. ASSUME n + 1 \leq Len(Ps)
          PROVE F[n + 1] = Conjoin(PrefixSet(Ps, n + 1))
    PROOF
      <3>1. n \in 0 .. (Len(Ps) - 1) /\
            n + 1 \in 1 .. Len(Ps)
        BY SMT, <2>1
      <3>2. F[n] = Conjoin(PrefixSet(Ps, n))
        BY SMT, <1>3, <2>1 DEF P
      <3>3. F[n + 1] = And(F[n], Ps[n + 1])
        BY SMT, <3>1
      <3>4. PrefixSet(Ps, n + 1) =
            PrefixSet(Ps, n) \cup {Ps[n + 1]}
        BY SMT, PrefixSetAdd, <3>1
      <3>5. Ps[n + 1] \in SUBSET Executions /\
            PrefixSet(Ps, n) \in SUBSET (SUBSET Executions)
        BY SMT, <3>1 DEF PrefixSet
      <3>6. QED BY SMT, <3>2, <3>3, <3>4, <3>5,
        ConjoinAdd DEF And
    <2>2. QED BY SMT, <2>1 DEF P
  <1>4. \A n \in Nat : P(n) => P(n + 1)
    BY SMT, <1>3
  <1>5. HIDE DEF P
  <1>6. \A n \in Nat : P(n)
    BY ONLY <1>2, <1>4, NatInductionChecked, Isa
  <1>7. QED BY <1>6 DEF P
THEOREM FoldOrTraceCorrespondence ==
  ASSUME NEW Ps \in Seq(SUBSET Executions),
         NEW F \in [0 .. Len(Ps) -> SUBSET Executions],
         F[0] = {},
         \A i \in 1 .. Len(Ps) :
           F[i] = Or(F[i - 1], Ps[i])
  PROVE \A n \in 0 .. Len(Ps) :
    F[n] = Disjoin(PrefixSet(Ps, n))
PROOF
  <1>1. DEFINE P(n) ==
    n \leq Len(Ps) => F[n] = Disjoin(PrefixSet(Ps, n))
  <1>2. P(0)
    BY SMT DEF P, PrefixSet, Disjoin
  <1>3. ASSUME NEW n \in Nat, P(n)
        PROVE P(n + 1)
  PROOF
    <2>1. ASSUME n + 1 \leq Len(Ps)
          PROVE F[n + 1] = Disjoin(PrefixSet(Ps, n + 1))
    PROOF
      <3>1. n \in 0 .. (Len(Ps) - 1) /\
            n + 1 \in 1 .. Len(Ps)
        BY SMT, <2>1
      <3>2. F[n] = Disjoin(PrefixSet(Ps, n))
        BY SMT, <1>3, <2>1 DEF P
      <3>3. F[n + 1] = Or(F[n], Ps[n + 1])
        BY SMT, <3>1
      <3>4. PrefixSet(Ps, n + 1) =
            PrefixSet(Ps, n) \cup {Ps[n + 1]}
        BY SMT, PrefixSetAdd, <3>1
      <3>5. Ps[n + 1] \in SUBSET Executions /\
            PrefixSet(Ps, n) \in SUBSET (SUBSET Executions)
        BY SMT, <3>1 DEF PrefixSet
      <3>6. QED BY SMT, <3>2, <3>3, <3>4, <3>5,
        DisjoinAdd DEF Or
    <2>2. QED BY SMT, <2>1 DEF P
  <1>4. \A n \in Nat : P(n) => P(n + 1)
    BY SMT, <1>3
  <1>5. HIDE DEF P
  <1>6. \A n \in Nat : P(n)
    BY ONLY <1>2, <1>4, NatInductionChecked, Isa
  <1>7. QED BY <1>6 DEF P

THEOREM MergedActionTraceCorrespondence ==
  ASSUME NEW A \in SUBSET (States \X States),
         NEW Is \in Seq(SUBSET States),
         NEW F \in [0 .. Len(Is) -> SUBSET (States \X States)],
         F[0] = A,
         \A i \in 1 .. Len(Is) :
           F[i] = {pair \in States \X States :
             pair \in F[i - 1] /\ pair[1] \in Is[i]}
  PROVE \A n \in 0 .. Len(Is) :
    F[n] = MergedAction(A, PrefixSet(Is, n))
PROOF
  <1>1. DEFINE P(n) ==
    n \leq Len(Is) => F[n] = MergedAction(A, PrefixSet(Is, n))
  <1>2. P(0)
    BY SMT DEF P, PrefixSet, MergedAction
  <1>3. ASSUME NEW n \in Nat, P(n)
        PROVE P(n + 1)
  PROOF
    <2>1. ASSUME n + 1 \leq Len(Is)
          PROVE F[n + 1] = MergedAction(A, PrefixSet(Is, n + 1))
    PROOF
      <3>1. n \in 0 .. (Len(Is) - 1) /\
            n + 1 \in 1 .. Len(Is)
        BY SMT, <2>1
      <3>2. F[n] = MergedAction(A, PrefixSet(Is, n))
        BY SMT, <1>3, <2>1 DEF P
      <3>3. F[n + 1] = {pair \in States \X States :
              pair \in F[n] /\ pair[1] \in Is[n + 1]}
        BY SMT, <3>1
      <3>4. PrefixSet(Is, n + 1) =
            PrefixSet(Is, n) \cup {Is[n + 1]}
        BY SMT, PrefixSetAdd, <3>1
      <3>5. Is[n + 1] \in SUBSET States /\
            PrefixSet(Is, n) \in SUBSET (SUBSET States)
        BY SMT, <3>1 DEF PrefixSet
      <3>6. QED BY SMT, <3>2, <3>3, <3>4, <3>5,
        MergedActionAdd DEF MergedAction
    <2>2. QED BY SMT, <2>1 DEF P
  <1>4. \A n \in Nat : P(n) => P(n + 1)
    BY SMT, <1>3
  <1>5. HIDE DEF P
  <1>6. \A n \in Nat : P(n)
    BY ONLY <1>2, <1>4, NatInductionChecked, Isa
  <1>7. QED BY <1>6 DEF P

THEOREM AndFoldResult ==
  \A Ps \in Seq(SUBSET Executions) :
    AndTrace(Ps)[Len(Ps)] = Conjoin(PrefixSet(Ps, Len(Ps)))
  BY SMT, AndTraceRecurrence, FoldAndTraceCorrespondence, SeqLenNat

THEOREM OrFoldResult ==
  \A Ps \in Seq(SUBSET Executions) :
    OrTrace(Ps)[Len(Ps)] = Disjoin(PrefixSet(Ps, Len(Ps)))
  BY SMT, OrTraceRecurrence, FoldOrTraceCorrespondence, SeqLenNat

THEOREM MergedActionFoldResult ==
  \A A \in SUBSET (States \X States) :
  \A Is \in Seq(SUBSET States) :
    ActionTrace(A, Is)[Len(Is)] =
      MergedAction(A, PrefixSet(Is, Len(Is)))
  BY SMT, ActionTraceRecurrence, MergedActionTraceCorrespondence, SeqLenNat
===========================================================================
