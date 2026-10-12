-------------------- MODULE TemporalPredicates --------------------
\* Value-level image of src/defs.rs. A TempPred is a set of executions.
\* This module states generic laws; its infinite domain is not a TLC model.
EXTENDS Naturals

CONSTANT States
ASSUME States # {}

Executions == [Nat -> States]
Head(ex) == ex[0]
HeadNext(ex) == ex[1]
Suffix(ex, n) == [i \in Nat |-> ex[i + n]]

LiftState(P) == {ex \in Executions : Head(ex) \in P}
LiftStatePrime(P) == {ex \in Executions : HeadNext(ex) \in P}
LiftAction(A) == {ex \in Executions : <<Head(ex), HeadNext(ex)>> \in A}

And(P, Q) == P \cap Q
Or(P, Q) == P \cup Q
Implies(P, Q) == (Executions \ P) \cup Q
Not(P) == Executions \ P
Forall(D, F) == {ex \in Executions : \A a \in D : ex \in F[a]}
Exists(D, F) == {ex \in Executions : \E a \in D : ex \in F[a]}

Always(P) == {ex \in Executions : \A i \in Nat : Suffix(ex, i) \in P}
Eventually(P) == {ex \in Executions : \E i \in Nat : Suffix(ex, i) \in P}
Later(P) == {ex \in Executions : Suffix(ex, 1) \in P}
LeadsTo(P, Q) == Always(Implies(P, Eventually(Q)))
Stable(P) == Implies(P, Always(P))

Enabled(A) == {s \in States : \E t \in States : <<s, t>> \in A}
WeakFairness(A) == LeadsTo(Always(LiftState(Enabled(A))), LiftAction(A))

Entails(P, Q) == P \subseteq Q
Valid(P) == P = Executions
TruePred == Executions
FalsePred == {}

==================================================================
