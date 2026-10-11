-------------------------- MODULE TemporalSetRules --------------------------
\* Exact behavior-set laws for src/defs.rs and selected public rules.rs laws.
EXTENDS TemporalPredicates, TLAPS

THEOREM EntailsReflexive ==
  \A P \in SUBSET Executions : Entails(P, P)
  BY DEF Entails

THEOREM AndCommutative ==
  \A P, Q \in SUBSET Executions : And(P, Q) = And(Q, P)
  BY DEF And

THEOREM ImpliesApply ==
  \A S, P, Q \in SUBSET Executions :
    (Entails(S, Implies(P, Q)) /\ Entails(S, P)) => Entails(S, Q)
  BY DEF Entails, Implies

THEOREM EntailsTrans ==
  \A P, Q, R \in SUBSET Executions :
    (Entails(P, Q) /\ Entails(Q, R)) => Entails(P, R)
  BY DEF Entails

THEOREM EntailsAnd ==
  \A S, P, Q \in SUBSET Executions :
    Entails(S, And(P, Q)) <=> (Entails(S, P) /\ Entails(S, Q))
  BY DEF Entails, And

THEOREM EntailsImplies ==
  \A S, P, Q \in SUBSET Executions :
    Entails(And(S, P), Q) => Entails(S, Implies(P, Q))
  BY SMT DEF Entails, And, Implies

THEOREM VacuousImplies ==
  \A S, P, Q \in SUBSET Executions :
    Entails(S, Q) => Entails(S, Implies(P, Q))
  BY SMT DEF Entails, Implies

THEOREM TempPredEquality ==
  \A P, Q \in SUBSET Executions :
    (Entails(P, Q) /\ Entails(Q, P)) => P = Q
  BY SMT, SetExtensionality DEF Entails

THEOREM ExecutionEquality ==
  \A ex1, ex2 \in Executions :
    (\A i \in Nat : ex1[i] = ex2[i]) => ex1 = ex2
  BY SMT DEF Executions

THEOREM EntailsAndAcrossSpecs ==
  \A S1, S2, P, Q \in SUBSET Executions :
    (Entails(S1, P) /\ Entails(S2, Q)) => Entails(And(S1, S2), And(P, Q))
  BY SMT DEF Entails, And

THEOREM FalseEntailsAnything ==
  \A P \in SUBSET Executions : Entails(FalsePred, P)
  BY DEF Entails, FalsePred

THEOREM FalseImpliesAnything ==
  \A P \in SUBSET Executions : Valid(Implies(FalsePred, P))
  BY SMT DEF Valid, Implies, FalsePred

THEOREM SimplifyPredicate ==
  \A P, Q \in SUBSET Executions : Entails(P, Q) => P = And(P, Q)
  BY SMT DEF Entails, And

THEOREM SuffixZero ==
  \A ex \in Executions : Suffix(ex, 0) = ex
  BY SMT DEF Suffix, Executions

THEOREM SuffixType ==
  \A ex \in Executions : \A i \in Nat : Suffix(ex, i) \in Executions
  BY SMT DEF Suffix, Executions

THEOREM SuffixAssoc ==
  \A ex \in Executions : \A i, j \in Nat :
    Suffix(Suffix(ex, i), j) = Suffix(ex, i + j)
  BY SMT DEF Suffix, Executions

THEOREM EventuallyIntro ==
  \A P \in SUBSET Executions : \A ex \in Executions :
    ex \in P => ex \in Eventually(P)
  BY SMT, SuffixZero DEF Eventually

THEOREM EventuallyType == \A P : Eventually(P) \subseteq Executions
  BY DEF Eventually

THEOREM LeadsToSelf ==
  \A P \in SUBSET Executions : Valid(LeadsTo(P, P))
  BY SMT, SuffixType, EventuallyIntro
    DEF Valid, LeadsTo, Always, Implies

THEOREM AlwaysToAlwaysLater ==
  \A P \in SUBSET Executions : Entails(Always(P), Always(Later(P)))
  BY SMT, SuffixType, SuffixAssoc DEF Entails, Always, Later

THEOREM AlwaysAnd ==
  \A P, Q \in SUBSET Executions :
    Always(And(P, Q)) = And(Always(P), Always(Q))
  BY SMT DEF Always, And

THEOREM AlwaysDouble ==
  \A P : Always(Always(P)) = Always(P)
  BY SMT, SuffixType, SuffixAssoc, SuffixZero DEF Always

THEOREM AlwaysSuffix ==
  \A ex \in Executions : \A P : \A i \in Nat :
    ex \in Always(P) => Suffix(ex, i) \in Always(P)
  BY SMT, SuffixType, SuffixAssoc DEF Always

THEOREM AlwaysType == \A P : Always(P) \subseteq Executions
  BY DEF Always

THEOREM AlwaysEntailsCurrent ==
  \A P \in SUBSET Executions : Entails(Always(P), P)
  BY SMT, SuffixZero DEF Entails, Always

THEOREM EliminateAlways ==
  \A S, P \in SUBSET Executions :
    Entails(S, Always(P)) => Entails(S, P)
  BY SMT, AlwaysEntailsCurrent DEF Entails

THEOREM StableImpliesAlways ==
  \A P \in SUBSET Executions : Valid(Stable(P)) => Entails(P, Always(P))
  BY SMT DEF Valid, Stable, Implies, Entails

THEOREM StableToAlways ==
  \A P \in SUBSET Executions : Valid(Stable(P)) => P = Always(P)
  BY SMT, AlwaysEntailsCurrent, StableImpliesAlways, SetExtensionality DEF Entails

THEOREM AlwaysPIsStable ==
  \A P \in SUBSET Executions : Valid(Stable(Always(P)))
  BY SMT, AlwaysDouble, AlwaysType DEF Valid, Stable, Implies

THEOREM LeadsToIsStable ==
  \A P, Q \in SUBSET Executions : Entails(LeadsTo(P, Q), Always(LeadsTo(P, Q)))
  BY SMT, AlwaysDouble DEF Entails, LeadsTo

THEOREM FalseIsStable == Valid(Stable(FalsePred))
  BY SMT DEF Valid, Stable, FalsePred, Implies, Always

THEOREM TrueIsStable == Valid(Stable(TruePred))
  BY SMT, SuffixType DEF Valid, Stable, TruePred, Implies, Always

THEOREM StableAnd ==
  \A P, Q \in SUBSET Executions :
    Entails(And(Stable(P), Stable(Q)), Stable(And(P, Q)))
  BY SMT DEF Entails, And, Stable, Implies, Always

THEOREM ForallApply ==
  \A D, F : F \in [D -> SUBSET Executions] =>
    \A a \in D : Entails(Forall(D, F), F[a])
  BY SMT DEF Entails, Forall

THEOREM SpecEntailsForall ==
  \A D, F, S : (F \in [D -> SUBSET Executions] /\ S \subseteq Executions) =>
    (\A a \in D : Entails(S, F[a])) => Entails(S, Forall(D, F))
  BY SMT DEF Entails, Forall

THEOREM ExistsIntro ==
  \A D, F, a : (F \in [D -> SUBSET Executions] /\ a \in D) =>
    Entails(F[a], Exists(D, F))
  BY SMT DEF Entails, Exists

THEOREM SpecEntailsForallApply ==
  \A D, F, S, a : (F \in [D -> SUBSET Executions] /\ a \in D) =>
    Entails(S, Forall(D, F)) => Entails(S, F[a])
  BY SMT, ForallApply DEF Entails

THEOREM EventuallyTrue == Valid(Eventually(TruePred))
  BY SMT, EventuallyIntro, EventuallyType DEF Valid, TruePred

THEOREM EntailsImpliesEventually ==
  \A S, P \in SUBSET Executions :
    Entails(S, P) => Entails(S, Eventually(P))
  BY SMT, EventuallyIntro DEF Entails

THEOREM EntailsPreservedByAlways ==
  \A P, Q \in SUBSET Executions :
    Entails(P, Q) => Entails(Always(P), Always(Q))
  BY SMT DEF Entails, Always

THEOREM AlwaysWeaken ==
  \A S, P, Q \in SUBSET Executions :
    (Entails(P, Q) /\ Entails(S, Always(P))) => Entails(S, Always(Q))
  BY SMT, EntailsPreservedByAlways DEF Entails

THEOREM FalseLeadsToAnything ==
  \A P \in SUBSET Executions : Valid(LeadsTo(FalsePred, P))
  BY SMT, SuffixType DEF Valid, LeadsTo, Always, Implies, FalsePred

THEOREM AlwaysImpliesToLeadsTo ==
  \A S, P, Q \in SUBSET Executions :
    Entails(S, Always(Implies(P, Q))) => Entails(S, LeadsTo(P, Q))
  BY SMT, EventuallyIntro DEF Entails, Always, Implies, LeadsTo, Eventually

THEOREM LeadsToWeakenPremise ==
  \A P, Q, R \in SUBSET Executions :
    Entails(LeadsTo(P, Q), LeadsTo(And(P, R), Q))
  BY SMT DEF Entails, LeadsTo, Always, Implies, And

THEOREM OrLeadsTo ==
  \A P, Q, R \in SUBSET Executions :
    Entails(And(LeadsTo(P, R), LeadsTo(Q, R)), LeadsTo(Or(P, Q), R))
  BY SMT DEF Entails, And, Or, LeadsTo, Always, Implies

THEOREM LeadsToEliminateAlways ==
  \A P, Q \in SUBSET Executions :
    Entails(LeadsTo(P, Always(Q)), LeadsTo(P, Q))
  BY SMT, AlwaysEntailsCurrent DEF Entails, LeadsTo, Always, Implies, Eventually

THEOREM LeadsToCharacterization ==
  \A ex \in Executions : \A P, Q \in SUBSET Executions :
    (ex \in LeadsTo(P, Q)) <=>
      (\A i \in Nat : Suffix(ex, i) \in P =>
        \E j \in Nat : Suffix(ex, i + j) \in Q)
  BY SMT, SuffixType, SuffixAssoc DEF LeadsTo, Always, Implies, Eventually

THEOREM LeadsToType == \A P, Q : LeadsTo(P, Q) \subseteq Executions
  BY SMT, AlwaysType DEF LeadsTo

THEOREM NatAddAssoc ==
  \A i, j, k \in Nat : i + (j + k) = (i + j) + k
  BY SMT

THEOREM NatAddZero == \A i \in Nat : i + 0 = i
  BY SMT

THEOREM NatAddComm == \A i, j \in Nat : i + j = j + i
  BY SMT

THEOREM LeadsToTransAt ==
  ASSUME NEW ex \in Executions,
         NEW P \in SUBSET Executions,
         NEW Q \in SUBSET Executions,
         NEW R \in SUBSET Executions,
         \A i \in Nat : Suffix(ex, i) \in P =>
           \E j \in Nat : Suffix(ex, i + j) \in Q,
         \A i \in Nat : Suffix(ex, i) \in Q =>
           \E j \in Nat : Suffix(ex, i + j) \in R
  PROVE  \A i \in Nat : Suffix(ex, i) \in P =>
           \E j \in Nat : Suffix(ex, i + j) \in R
  BY SMT, NatAddAssoc

THEOREM LeadsToTrans ==
  \A P, Q, R \in SUBSET Executions :
    Entails(And(LeadsTo(P, Q), LeadsTo(Q, R)), LeadsTo(P, R))
  BY SMT, LeadsToCharacterization, LeadsToType, LeadsToTransAt DEF Entails, And

THEOREM ExistsAnd ==
  \A D, F, Q : F \in [D -> SUBSET Executions] =>
    Exists(D, [a \in D |-> And(F[a], Q)]) = And(Exists(D, F), Q)
  BY SMT DEF Exists, And

THEOREM ExistsOrNonempty ==
  \A D, F, Q : (D # {} /\ F \in [D -> SUBSET Executions] /\ Q \subseteq Executions) =>
    Exists(D, [a \in D |-> Or(F[a], Q)]) = Or(Exists(D, F), Q)
  BY SMT DEF Exists, Or

THEOREM ForallAlways ==
  \A D, F : F \in [D -> SUBSET Executions] =>
    Always(Forall(D, F)) = Forall(D, [a \in D |-> Always(F[a])])
  BY SMT, SuffixType DEF Always, Forall

THEOREM ExistsCongruence ==
  \A D, F, G : (F \in [D -> SUBSET Executions] /\ G \in [D -> SUBSET Executions]) =>
    (\A a \in D : F[a] = G[a]) => Exists(D, F) = Exists(D, G)
  BY SMT DEF Exists

THEOREM ForallCongruence ==
  \A D, F, G : (F \in [D -> SUBSET Executions] /\ G \in [D -> SUBSET Executions]) =>
    (\A a \in D : F[a] = G[a]) => Forall(D, F) = Forall(D, G)
  BY SMT DEF Forall

THEOREM ForallAlwaysVariant ==
  \A D, F, G : (F \in [D -> SUBSET Executions] /\ G \in [D -> SUBSET Executions]) =>
    (\A a \in D : G[a] = Always(F[a])) =>
      Forall(D, G) = Always(Forall(D, F))
  BY SMT, ForallAlways, ForallCongruence

THEOREM AlwaysForallApply ==
  \A D, F, a : (F \in [D -> SUBSET Executions] /\ a \in D) =>
    Entails(Always(Forall(D, F)), Always(F[a]))
  BY SMT DEF Entails, Always, Forall

THEOREM SpecEntailsAlwaysForall ==
  \A D, F, S : (F \in [D -> SUBSET Executions] /\ S \subseteq Executions) =>
    (Entails(S, Always(Forall(D, F))) <=>
      (\A a \in D : Entails(S, Always(F[a]))))
  BY SMT, SuffixType DEF Entails, Always, Forall

THEOREM AlwaysImpliesForallIntro ==
  \A D, F, S, P :
    (F \in [D -> SUBSET Executions] /\ S \subseteq Executions /\ P \subseteq Executions) =>
      (\A a \in D : Entails(S, Always(Implies(P, F[a])))) =>
        Entails(S, Always(Implies(P, Forall(D, F))))
  BY SMT, SuffixType DEF Entails, Always, Implies, Forall

THEOREM LeadsToExistsIntro ==
  \A D, F, S, Q :
    (F \in [D -> SUBSET Executions] /\ S \subseteq Executions /\ Q \subseteq Executions) =>
      (\A a \in D : Entails(S, LeadsTo(F[a], Q))) =>
        Entails(S, LeadsTo(Exists(D, F), Q))
  BY SMT, LeadsToCharacterization DEF Entails, Exists

THEOREM LeadsToExistsPointwise ==
  \A D, F, G, S :
    (F \in [D -> SUBSET Executions] /\ G \in [D -> SUBSET Executions] /\ S \subseteq Executions) =>
      (\A a \in D : Entails(S, LeadsTo(F[a], G[a]))) =>
        Entails(S, LeadsTo(Exists(D, F), Exists(D, G)))
  BY SMT, LeadsToCharacterization DEF Entails, Exists

THEOREM EntailsImpliesLeadsTo ==
  \A P, Q \in SUBSET Executions :
    Entails(P, Q) => Valid(LeadsTo(P, Q))
  BY SMT, SuffixType, EventuallyIntro DEF Entails, Valid, LeadsTo, Always, Implies

THEOREM LeadsToApply ==
  \A S, P, Q \in SUBSET Executions :
    (Entails(S, P) /\ Entails(S, LeadsTo(P, Q))) =>
      Entails(S, Eventually(Q))
  BY SMT, LeadsToCharacterization, SuffixZero DEF Entails, Eventually

THEOREM AlwaysImpliesEventuallyAlways ==
  \A ex \in Executions : \A Q \in SUBSET Executions :
    ex \in Always(Q) =>
      \A i \in Nat : Suffix(ex, i) \in Eventually(Always(Q))
  BY SMT, SuffixType, AlwaysSuffix, AlwaysType, EventuallyIntro

THEOREM EventuallyAt ==
  \A ex \in Executions : \A P : \A i \in Nat :
    (Suffix(ex, i) \in Eventually(P)) <=>
      (\E j \in Nat : Suffix(ex, i + j) \in P)
  BY SMT, SuffixAssoc, SuffixType DEF Eventually

THEOREM AlwaysEntailsLeadsToAlways ==
  \A S, P, Q \in SUBSET Executions :
    Entails(S, Always(Q)) => Entails(S, LeadsTo(P, Always(Q)))
  BY SMT, LeadsToCharacterization, AlwaysImpliesEventuallyAlways, EventuallyAt, AlwaysType
    DEF Entails

THEOREM AlwaysImpliesPreservedByAlways ==
  \A S, P, Q \in SUBSET Executions :
    Entails(S, Always(Implies(P, Q))) =>
      Entails(S, Always(Implies(Always(P), Always(Q))))
  BY SMT, SuffixType, SuffixAssoc DEF Entails, Always, Implies

THEOREM LeadsToWeaken ==
  \A S, P1, P2, Q1, Q2 \in SUBSET Executions :
    (Entails(S, Always(Implies(P2, P1))) /\
     Entails(S, Always(Implies(Q1, Q2))) /\
     Entails(S, LeadsTo(P1, Q1))) =>
       Entails(S, LeadsTo(P2, Q2))
  BY SMT, LeadsToCharacterization, SuffixType, SuffixAssoc
    DEF Entails, Always, Implies

THEOREM OrType ==
  \A P, Q \in SUBSET Executions : Or(P, Q) \subseteq Executions
  BY SMT DEF Or

THEOREM AndType ==
  \A P, Q \in SUBSET Executions : And(P, Q) \subseteq Executions
  BY SMT DEF And

THEOREM OrIdempotent == \A P, Q : Or(Or(P, Q), Q) = Or(P, Q)
  BY SMT DEF Or

THEOREM LeadsToFramedAt ==
  ASSUME NEW ex \in Executions,
         NEW P \in SUBSET Executions,
         NEW Q \in SUBSET Executions,
         NEW R \in SUBSET Executions,
         \A i \in Nat : Suffix(ex, i) \in P =>
           \E j \in Nat : Suffix(ex, i + j) \in Q
  PROVE  \A i \in Nat : Suffix(ex, i) \in Or(P, R) =>
           \E j \in Nat : Suffix(ex, i + j) \in Or(Q, R)
  BY SMT, NatAddZero DEF Or

THEOREM LeadsToFramedByOr ==
  \A P, Q, R \in SUBSET Executions :
    Entails(LeadsTo(P, Q), LeadsTo(Or(P, R), Or(Q, R)))
  BY SMT, LeadsToCharacterization, LeadsToFramedAt, LeadsToType, OrType
    DEF Entails, Or

THEOREM VacuousLeadsTo ==
  \A S, P, Q, R \in SUBSET Executions :
    (Entails(S, Always(R)) /\ And(P, R) = FalsePred) =>
      Entails(S, LeadsTo(P, Q))
  BY SMT, LeadsToCharacterization, SuffixType, SuffixAssoc
    DEF Entails, Always, And, FalsePred

THEOREM LeadsToShortcutAt ==
  ASSUME NEW ex \in Executions,
         NEW P \in SUBSET Executions,
         NEW Q \in SUBSET Executions,
         NEW R \in SUBSET Executions,
         NEW U \in SUBSET Executions,
         \A i \in Nat : Suffix(ex, i) \in P =>
           \E j \in Nat : Suffix(ex, i + j) \in Or(Q, U),
         \A i \in Nat : Suffix(ex, i) \in Q =>
           \E j \in Nat : Suffix(ex, i + j) \in Or(R, U)
  PROVE  \A i \in Nat : Suffix(ex, i) \in P =>
           \E j \in Nat : Suffix(ex, i + j) \in Or(R, U)
  BY SMT, NatAddAssoc, NatAddZero DEF Or

THEOREM LeadsToShortcutMember ==
  ASSUME NEW ex \in Executions,
         NEW P \in SUBSET Executions,
         NEW Q \in SUBSET Executions,
         NEW R \in SUBSET Executions,
         NEW U \in SUBSET Executions,
         ex \in LeadsTo(P, Or(Q, U)),
         ex \in LeadsTo(Q, Or(R, U))
  PROVE  ex \in LeadsTo(P, Or(R, U))
PROOF
  <1>1. \A i \in Nat : Suffix(ex, i) \in P =>
           \E j \in Nat : Suffix(ex, i + j) \in Or(Q, U)
    BY SMT, LeadsToCharacterization, OrType
  <1>2. \A i \in Nat : Suffix(ex, i) \in Q =>
           \E j \in Nat : Suffix(ex, i + j) \in Or(R, U)
    BY SMT, LeadsToCharacterization, OrType
  <1>3. \A i \in Nat : Suffix(ex, i) \in P =>
           \E j \in Nat : Suffix(ex, i + j) \in Or(R, U)
    BY SMT, NatAddAssoc, NatAddZero, <1>1, <1>2 DEF Or
  <1>4. QED BY SMT, LeadsToCharacterization, OrType, <1>3

THEOREM LeadsToShortcut ==
  \A P, Q, R, U \in SUBSET Executions :
    Entails(And(LeadsTo(P, Or(Q, U)), LeadsTo(Q, Or(R, U))),
            LeadsTo(P, Or(R, U)))
  BY SMT, LeadsToShortcutMember, OrType, LeadsToType
    DEF Entails, And

THEOREM EventuallyAlwaysAndAt ==
  ASSUME NEW ex \in Executions,
         NEW P \in SUBSET Executions,
         NEW Q \in SUBSET Executions,
         NEW i \in Nat,
         NEW j \in Nat,
         Suffix(ex, i) \in Always(P),
         Suffix(ex, j) \in Always(Q)
  PROVE  Suffix(ex, i + j) \in Always(And(P, Q))
  BY SMT, SuffixType, SuffixAssoc, NatAddComm, AlwaysSuffix, AlwaysAnd
    DEF And, Always

THEOREM EventuallyAlwaysAnd ==
  \A P, Q \in SUBSET Executions :
    Entails(And(Eventually(Always(P)), Eventually(Always(Q))),
            Eventually(Always(And(P, Q))))
  BY SMT, EventuallyAlwaysAndAt
    DEF Entails, And, Eventually

THEOREM EventuallyMonotonic ==
  \A P, Q \in SUBSET Executions :
    Entails(P, Q) => Entails(Eventually(P), Eventually(Q))
  BY SMT DEF Entails, Eventually

THEOREM EventuallyAlwaysAndToIntermediate ==
  ASSUME NEW P \in SUBSET Executions,
         NEW Q \in SUBSET Executions,
         NEW R \in SUBSET Executions,
         Entails(And(P, Q), R)
  PROVE  Entails(Eventually(Always(And(P, Q))), Eventually(Always(R)))
  BY SMT, EntailsPreservedByAlways, EventuallyMonotonic, AndType, AlwaysType
    DEF Entails

THEOREM EventuallyAlwaysAndTo ==
  \A S, P, Q, R \in SUBSET Executions :
    (Entails(S, Eventually(Always(P))) /\
     Entails(S, Eventually(Always(Q))) /\
     Entails(And(P, Q), R)) =>
       Entails(S, Eventually(Always(R)))
  BY SMT, EventuallyAlwaysAnd, EventuallyAlwaysAndToIntermediate
    DEF Entails, And

THEOREM LeadsToAlwaysAndAt ==
  ASSUME NEW ex \in Executions,
         NEW P \in SUBSET Executions,
         NEW Q \in SUBSET Executions,
         NEW R \in SUBSET Executions,
         \A i \in Nat : Suffix(ex, i) \in P =>
           Suffix(ex, i) \in Eventually(Always(Q)),
         \A i \in Nat : Suffix(ex, i) \in P =>
           Suffix(ex, i) \in Eventually(Always(R))
  PROVE  \A i \in Nat : Suffix(ex, i) \in P =>
           Suffix(ex, i) \in Eventually(Always(And(Q, R)))
  BY SMT, SuffixType, EventuallyAlwaysAnd DEF Entails, And

THEOREM LeadsToAlwaysAnd ==
  \A S, P, Q, R \in SUBSET Executions :
    (Entails(S, LeadsTo(P, Always(Q))) /\
     Entails(S, LeadsTo(P, Always(R)))) =>
       Entails(S, LeadsTo(P, Always(And(Q, R))))
  BY SMT, SuffixType, LeadsToAlwaysAndAt, LeadsToCharacterization,
    EventuallyAt, AlwaysType, AndType
    DEF Entails

THEOREM LeadsToAlwaysAndSecond ==
  \A S, P, Q, R \in SUBSET Executions :
    (Entails(S, LeadsTo(P, Always(Q))) /\
     Entails(S, LeadsTo(P, Always(R)))) =>
       Entails(S, LeadsTo(P, And(Always(Q), Always(R))))
  BY SMT, LeadsToAlwaysAnd, AlwaysAnd DEF Entails, And

THEOREM AlwaysTriggerWeakening ==
  \A P1, P2, Q \in SUBSET Executions :
    Entails(LeadsTo(Always(P1), Q), LeadsTo(Always(And(P1, P2)), Q))
  BY SMT, AlwaysAnd, AlwaysType, AndType, LeadsToWeakenPremise
    DEF Entails, And

THEOREM AlwaysTriggerWeakeningRight ==
  \A P1, P2, Q \in SUBSET Executions :
    Entails(LeadsTo(Always(P2), Q), LeadsTo(Always(And(P1, P2)), Q))
  BY SMT, AlwaysAnd, AlwaysType, AndType, AndCommutative, LeadsToWeakenPremise
    DEF Entails, And

THEOREM AlwaysLeadsToAlwaysAnd ==
  \A S, P1, P2, Q1, Q2 \in SUBSET Executions :
    (Entails(S, LeadsTo(Always(P1), Always(Q1))) /\
     Entails(S, LeadsTo(Always(P2), Always(Q2)))) =>
       Entails(S, LeadsTo(Always(And(P1, P2)), Always(And(Q1, Q2))))
  BY SMT, AlwaysTriggerWeakening, AlwaysTriggerWeakeningRight,
    AlwaysType, AndType, LeadsToAlwaysAnd
    DEF Entails, And

THEOREM LeadsToExistsGuard ==
  \A D, F, S, Q, Guard :
    (F \in [D -> SUBSET Executions] /\ S \subseteq Executions /\
     Q \subseteq Executions /\ Guard \subseteq D /\
     (\A a \in D \ Guard : F[a] = {}) /\
     (\A a \in Guard : Entails(S, LeadsTo(F[a], Q)))) =>
       Entails(S, LeadsTo(Exists(D, F), Q))
  BY SMT, LeadsToCharacterization DEF Entails, Exists

THEOREM EventuallyAlwaysForallUnfold ==
  \A D, F, S, a :
    (F \in [D -> SUBSET Executions] /\ S \subseteq Executions /\ a \in D) =>
      Entails(S, Eventually(Always(Forall(D, F)))) =>
        Entails(S, Eventually(Always(F[a])))
  BY SMT, AlwaysForallApply, EventuallyMonotonic, AlwaysType
    DEF Entails

THEOREM LeadsToGoalMonotonic ==
  \A P, Q, R \in SUBSET Executions :
    Entails(Q, R) => Entails(LeadsTo(P, Q), LeadsTo(P, R))
  BY SMT, EventuallyMonotonic DEF Entails, LeadsTo, Always, Implies

THEOREM ForallLeadsToAlways ==
  \A D, F, S, P, a :
    (F \in [D -> SUBSET Executions] /\ S \subseteq Executions /\
     P \subseteq Executions /\ a \in D) =>
      Entails(S, LeadsTo(P, Always(Forall(D, F)))) =>
        Entails(S, LeadsTo(P, Always(F[a])))
  BY SMT, AlwaysForallApply, LeadsToGoalMonotonic, AlwaysType
    DEF Entails

THEOREM StableForall ==
  \A D, F : F \in [D -> SUBSET Executions] =>
    (\A a \in D : Valid(Stable(F[a]))) => Valid(Stable(Forall(D, F)))
  BY SMT, SuffixType DEF Valid, Stable, Implies, Always, Forall

THEOREM LeadsToValidStable ==
  \A P, Q \in SUBSET Executions : Valid(Stable(LeadsTo(P, Q)))
  BY SMT, LeadsToIsStable, LeadsToType, AlwaysType
    DEF Valid, Stable, Implies, Entails

THEOREM ForallPLeadsToQIsStable ==
  ASSUME NEW D,
         NEW P \in SUBSET Executions,
         NEW Q \in [D -> SUBSET Executions]
  PROVE  Valid(Stable(Forall(D, [a \in D |-> LeadsTo(P, Q[a])])))
PROOF
  <1>1. DEFINE F == [a \in D |-> LeadsTo(P, Q[a])]
  <1>2. F \in [D -> SUBSET Executions]
    BY SMT, LeadsToType DEF F
  <1>3. \A a \in D : Valid(Stable(F[a]))
    BY SMT, LeadsToValidStable DEF F
  <1>4. QED BY SMT, StableForall, <1>2, <1>3 DEF F

THEOREM ForallPOfALeadsToQOfAIsStable ==
  ASSUME NEW D,
         NEW P \in [D -> SUBSET Executions],
         NEW Q \in [D -> SUBSET Executions]
  PROVE  Valid(Stable(Forall(D, [a \in D |-> LeadsTo(P[a], Q[a])])))
PROOF
  <1>1. DEFINE F == [a \in D |-> LeadsTo(P[a], Q[a])]
  <1>2. F \in [D -> SUBSET Executions]
    BY SMT, LeadsToType DEF F
  <1>3. \A a \in D : Valid(Stable(F[a]))
    BY SMT, LeadsToValidStable DEF F
  <1>4. QED BY SMT, StableForall, <1>2, <1>3 DEF F


THEOREM UnpackConditionsFromSpec ==
  \A S, C, P, Q \in SUBSET Executions :
    (Valid(Stable(S)) /\ Entails(And(S, C), LeadsTo(P, Q))) =>
      Entails(S, LeadsTo(And(P, C), Q))
  BY SMT, SuffixType, SuffixZero
    DEF Valid, Stable, Entails, And, LeadsTo, Always, Implies, Eventually

THEOREM PackConditionsToSpec ==
  \A S, C, P, Q \in SUBSET Executions :
    Entails(S, LeadsTo(And(P, C), Q)) =>
      Entails(And(S, Always(C)), LeadsTo(P, Q))
  BY SMT, SuffixType, AlwaysSuffix, SuffixZero
    DEF Entails, And, LeadsTo, Always, Implies, Eventually

THEOREM LeadsToByBorrowingInv ==
  \A S, P, Q, Inv \in SUBSET Executions :
    (Entails(S, LeadsTo(And(P, Inv), Q)) /\ Entails(S, Always(Inv))) =>
      Entails(S, LeadsTo(P, Q))
  BY SMT, SuffixType, AlwaysSuffix, SuffixZero
    DEF Entails, And, LeadsTo, Always, Implies, Eventually

THEOREM LeadsToAlwaysEnhance ==
  ASSUME NEW S \in SUBSET Executions,
         NEW Inv \in SUBSET Executions,
         NEW P \in SUBSET Executions,
         NEW Q1 \in SUBSET Executions,
         NEW Q2 \in SUBSET Executions,
         Entails(S, Always(Inv)),
         Entails(S, LeadsTo(P, Always(Q1))),
         Entails(And(Q1, Inv), Q2)
  PROVE  Entails(S, LeadsTo(P, Always(Q2)))
PROOF
  <1>1. Entails(S, LeadsTo(P, Always(Inv)))
    BY SMT, AlwaysEntailsLeadsToAlways
  <1>2. Entails(S, LeadsTo(P, Always(And(Q1, Inv))))
    BY SMT, LeadsToAlwaysAnd, <1>1
  <1>3. Entails(Always(And(Q1, Inv)), Always(Q2))
    BY SMT, EntailsPreservedByAlways, AndType
  <1>4. Entails(LeadsTo(P, Always(And(Q1, Inv))),
                LeadsTo(P, Always(Q2)))
    BY SMT, LeadsToGoalMonotonic, AlwaysType, AndType, <1>3
  <1>5. QED BY SMT, <1>2, <1>4 DEF Entails

THEOREM EntailsEventuallyToValidLeadsTo ==
  \A P, Q \in SUBSET Executions :
    Entails(P, Eventually(Q)) => Valid(LeadsTo(P, Q))
  BY SMT, SuffixType
    DEF Entails, Eventually, Valid, LeadsTo, Always, Implies

THEOREM LeadsToTransWithEntailedLeadsTo ==
  ASSUME NEW S \in SUBSET Executions,
         NEW P \in SUBSET Executions,
         NEW Q \in SUBSET Executions,
         NEW R \in SUBSET Executions,
         NEW U \in SUBSET Executions,
         Entails(S, LeadsTo(P, And(Q, R))),
         Entails(Q, LeadsTo(R, U))
  PROVE  Entails(S, LeadsTo(P, U))
PROOF
  <1>1. Entails(And(Q, R), R) /\
        Entails(And(Q, R), LeadsTo(R, U))
    BY SMT DEF Entails, And
  <1>2. Entails(And(Q, R), Eventually(U))
    BY SMT, LeadsToApply, AndType, <1>1
  <1>3. Valid(LeadsTo(And(Q, R), U))
    BY SMT, EntailsEventuallyToValidLeadsTo, AndType, <1>2
  <1>4. Entails(S, LeadsTo(And(Q, R), U))
    BY SMT, <1>3 DEF Entails, Valid
  <1>5. Entails(And(LeadsTo(P, And(Q, R)),
                    LeadsTo(And(Q, R), U)), LeadsTo(P, U))
    BY SMT, LeadsToTrans, LeadsToType, AndType
  <1>6. QED BY SMT, <1>4, <1>5 DEF Entails, And

THEOREM LeadsToWithAlwaysAt ==
  ASSUME NEW ex \in Executions,
         NEW P \in SUBSET Executions,
         NEW Q \in SUBSET Executions,
         NEW C \in SUBSET Executions,
         ex \in LeadsTo(P, Q)
  PROVE  \A i \in Nat : Suffix(ex, i) \in And(P, Always(C)) =>
           \E j \in Nat : Suffix(ex, i + j) \in And(Q, Always(C))
  BY SMT, LeadsToCharacterization, AlwaysSuffix, SuffixAssoc,
    SuffixType DEF And

THEOREM LeadsToWithAlways ==
  \A S, P, Q, C \in SUBSET Executions :
    Entails(S, LeadsTo(P, Q)) =>
      Entails(S, LeadsTo(And(P, Always(C)), And(Q, Always(C))))
  BY SMT, LeadsToWithAlwaysAt, LeadsToCharacterization, AndType,
    AlwaysType DEF Entails

THEOREM EventuallyAlwaysSuffix ==
  \A ex \in Executions : \A P \in SUBSET Executions :
    ex \in Eventually(Always(P)) =>
      \A i \in Nat : Suffix(ex, i) \in Eventually(Always(P))
  BY SMT, EventuallyAt, AlwaysSuffix, SuffixAssoc, NatAddComm,
    SuffixType DEF Eventually

THEOREM TrueLeadsToEqualsAlwaysEventually ==
  \A Q \in SUBSET Executions :
    LeadsTo(TruePred, Q) = Always(Eventually(Q))
  BY SMT DEF LeadsTo, Always, Implies, TruePred, Eventually

THEOREM AlwaysEventuallyAlwaysEquality ==
  \A P \in SUBSET Executions :
    Always(Eventually(Always(P))) = Eventually(Always(P))
  BY SMT, EventuallyAlwaysSuffix, SuffixZero, AlwaysType,
    EventuallyType, SetExtensionality
    DEF Always, Eventually

THEOREM TrueLeadsToEventuallyAlwaysEquality ==
  \A S, P \in SUBSET Executions :
    Entails(S, LeadsTo(TruePred, Always(P))) <=>
      Entails(S, Eventually(Always(P)))
  BY SMT, TrueLeadsToEqualsAlwaysEventually,
    AlwaysEventuallyAlwaysEquality, AlwaysType DEF Entails

THEOREM StrengthenAlways ==
  \A S, P, Q, R \in SUBSET Executions :
    (Entails(S, Always(P)) /\ Entails(S, Always(Q)) /\
     Entails(And(P, Q), R)) => Entails(S, Always(R))
  BY SMT, AlwaysAnd, EntailsPreservedByAlways, AndType
    DEF Entails, And

THEOREM StrengthenNext ==
  \A S \in SUBSET Executions :
  \A A, B \in SUBSET (States \X States) :
  \A I \in SUBSET States :
    (Entails(S, Always(LiftAction(A))) /\
     Entails(S, Always(LiftState(I))) /\
     Entails(LiftAction(B), And(LiftAction(A), LiftState(I))) /\
     Entails(And(LiftAction(A), LiftState(I)), LiftAction(B))) =>
      Entails(S, Always(LiftAction(B)))
  BY SMT, StrengthenAlways DEF Entails, LiftAction, LiftState, And

THEOREM StableExists ==
  \A D, F : F \in [D -> SUBSET Executions] =>
    (\A a \in D : Valid(Stable(F[a]))) => Valid(Stable(Exists(D, F)))
  BY SMT, SuffixType DEF Valid, Stable, Implies, Always, Exists

THEOREM StableGoalsCombine ==
  ASSUME NEW S \in SUBSET Executions,
         NEW P \in SUBSET Executions,
         NEW Q \in SUBSET Executions,
         NEW R \in SUBSET Executions,
         Valid(Stable(Q)),
         Valid(Stable(R)),
         Entails(S, LeadsTo(P, Q)),
         Entails(S, LeadsTo(P, R))
  PROVE  Entails(S, LeadsTo(P, And(Q, R)))
PROOF
  <1>1. Q = Always(Q) /\ R = Always(R)
    BY SMT, StableToAlways
  <1>2. Entails(S, LeadsTo(P, Always(And(Q, R))))
    BY SMT, LeadsToAlwaysAnd, <1>1
  <1>3. QED BY SMT, LeadsToEliminateAlways, <1>2, AndType
    DEF Entails

THEOREM ExistsAlwaysStable ==
  ASSUME NEW D,
         NEW F \in [D -> SUBSET Executions]
  PROVE  Valid(Stable(Exists(D, [a \in D |-> Always(F[a])])))
PROOF
  <1>1. [a \in D |-> Always(F[a])] \in [D -> SUBSET Executions]
    BY SMT, AlwaysType
  <1>2. \A a \in D : Valid(Stable(Always(F[a])))
    BY SMT, AlwaysPIsStable
  <1>3. QED BY SMT, StableExists, <1>1, <1>2

THEOREM ExistsAlwaysAndEquality ==
  \A D, F, R : (F \in [D -> SUBSET Executions] /\ R \subseteq Executions) =>
    Exists(D, [a \in D |-> Always(And(F[a], R))]) =
      And(Exists(D, [a \in D |-> Always(F[a])]), Always(R))
  BY SMT, AlwaysAnd, ExistsAnd, AlwaysType, AndType
    DEF Exists, And

THEOREM LeadsToExistsAlwaysAnd ==
  ASSUME NEW D,
         NEW F \in [D -> SUBSET Executions],
         NEW S \in SUBSET Executions,
         NEW P \in SUBSET Executions,
         NEW R \in SUBSET Executions,
         Entails(S, LeadsTo(P, Exists(D, [a \in D |-> Always(F[a])]))),
         Entails(S, LeadsTo(P, Always(R)))
  PROVE
    /\ Entails(S, LeadsTo(P,
         Exists(D, [a \in D |-> Always(And(F[a], R))])))
    /\ Entails(S, LeadsTo(P,
         Exists(D, [a \in D |-> And(Always(F[a]), Always(R))])))
    /\ Entails(S, LeadsTo(P,
         And(Exists(D, [a \in D |-> Always(F[a])]), Always(R))))
PROOF
  <1>1. DEFINE E == Exists(D, [a \in D |-> Always(F[a])])
  <1>2. E \in SUBSET Executions
    BY SMT, AlwaysType DEF E, Exists
  <1>3. Valid(Stable(E)) /\ Valid(Stable(Always(R)))
    BY SMT, ExistsAlwaysStable, AlwaysPIsStable DEF E
  <1>4. E = Always(E) /\ Always(R) = Always(Always(R))
    BY SMT, StableToAlways, AlwaysType, <1>2, <1>3
      DEF E, Valid, Stable
  <1>5. Entails(S, LeadsTo(P, Always(And(E, Always(R)))))
    BY SMT, LeadsToAlwaysAnd, AlwaysType, <1>2, <1>4
      DEF E, Entails, And, LeadsTo
  <1>6. Entails(S, LeadsTo(P, And(E, Always(R))))
    BY SMT, LeadsToEliminateAlways, <1>2, <1>5
      DEF Entails, And
  <1>7. Exists(D, [a \in D |-> Always(And(F[a], R))]) =
         And(E, Always(R))
    BY SMT, ExistsAlwaysAndEquality DEF E
  <1>8. Exists(D, [a \in D |-> And(Always(F[a]), Always(R))]) =
         And(E, Always(R))
    BY SMT, ExistsAnd, AlwaysType DEF E
  <1>9. QED BY SMT, <1>6, <1>7, <1>8 DEF E

THEOREM PairInProduct ==
  \A D, G : \A a \in D : \A b \in G : <<a, b>> \in D \X G
  BY SMT

THEOREM ExistsProductAndAt ==
  \A D, G, F, H, ex :
    (F \in [D -> SUBSET Executions] /\
     H \in [G -> SUBSET Executions] /\ ex \in Executions) =>
      (ex \in Exists(D \X G,
        [ab \in D \X G |-> And(F[ab[1]], H[ab[2]])]) <=>
       ex \in And(Exists(D, F), Exists(G, H)))
  BY SMT, PairInProduct DEF Exists, And

THEOREM ExistsProductAnd ==
  \A D, G, F, H :
    (F \in [D -> SUBSET Executions] /\
     H \in [G -> SUBSET Executions]) =>
      Exists(D \X G, [ab \in D \X G |-> And(F[ab[1]], H[ab[2]])]) =
        And(Exists(D, F), Exists(G, H))
  BY SMT, ExistsProductAndAt, SetExtensionality DEF Exists, And

THEOREM LeadsToExistsAlwaysAndExists ==
  ASSUME NEW D, NEW G,
         NEW F \in [D -> SUBSET Executions],
         NEW H \in [G -> SUBSET Executions],
         NEW S \in SUBSET Executions,
         NEW P \in SUBSET Executions,
         Entails(S, LeadsTo(P, Exists(D, [a \in D |-> Always(F[a])]))),
         Entails(S, LeadsTo(P, Exists(G, [b \in G |-> Always(H[b])])))
  PROVE Entails(S, LeadsTo(P,
    Exists(D \X G, [ab \in D \X G |->
      And(Always(F[ab[1]]), Always(H[ab[2]]))])))
PROOF
  <1>1. DEFINE E1 == Exists(D, [a \in D |-> Always(F[a])])
  <1>2. DEFINE E2 == Exists(G, [b \in G |-> Always(H[b])])
  <1>3. E1 \in SUBSET Executions /\ E2 \in SUBSET Executions
    BY SMT, AlwaysType DEF E1, E2, Exists
  <1>4. Valid(Stable(E1)) /\ Valid(Stable(E2))
    BY SMT, ExistsAlwaysStable DEF E1, E2
  <1>5. E1 = Always(E1) /\ E2 = Always(E2)
    BY SMT, StableToAlways, <1>3, <1>4 DEF E1, E2, Valid, Stable
  <1>6. Entails(S, LeadsTo(P, Always(And(E1, E2))))
    BY SMT, LeadsToAlwaysAnd, <1>3, <1>5
      DEF E1, E2, Entails, And, LeadsTo
  <1>7. Entails(S, LeadsTo(P, And(E1, E2)))
    BY SMT, LeadsToEliminateAlways, <1>3, <1>6
      DEF Entails, And
  <1>8. Exists(D \X G, [ab \in D \X G |->
           And(Always(F[ab[1]]), Always(H[ab[2]]))]) = And(E1, E2)
    BY SMT, ExistsProductAnd, AlwaysType DEF E1, E2
  <1>9. QED BY SMT, <1>7, <1>8 DEF E1, E2



==========================================================================
