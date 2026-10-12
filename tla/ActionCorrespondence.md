# Action preservation and stuttering

`TemporalActionRules.tla` treats a state predicate as a subset `I` of
`States` and an action as a subset `A` of `States \X States`. `NextToStable`
matches `next_to_stable` in `src/rules.rs`: preserving `I` on each `A` step
implies `Always(LiftAction(A))` entails `Stable(LiftState(I))`.
`InitInvariant` adds an initial-state subset and derives `Always(LiftState(I))`.

Verus states the two rules with `always(lift_action(next))`, which requires
each transition to satisfy `next`. Native `[Next]_vars` permits an identity
step as well. `IdentityAction` and `StutteringClosure(A)` give the behavior-set
image of this allowance. `StutteringClosurePreserves`,
`NextToStableStuttering`, and `InitInvariantStuttering` prove that an identity
step preserves every state predicate, so the same invariant reasoning applies.
These theorems do not claim a generic checked equivalence between the
behavior-set model and the native TLA+ action syntax; that formulation
correspondence remains open in the coverage ledger.

`TemporalPreservationAt` handles temporal predicates directly: under `[]N`
and `[](Q /\ N => Later(Q))`, a behavior satisfying `Q` satisfies `[]Q`.
`LeadsToStable` uses that fact to match the temporal `leads_to_stable` rule.
`ActionPreservesExistsAt` holds an existential witness fixed while its state
predicate is preserved. It supports both `EntailsExistsStable` and
`LeadsToExistsStable` for an arbitrary witness domain `D`.
