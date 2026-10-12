# Finite macro correspondence

`TemporalMacroRules.tla` represents a macro invocation's finite list of temporal
predicate arguments by the set `C` of those arguments. `ConjoinPair` proves
the two-argument conjunction law, and `ConjoinAdd` proves the step for adding
one argument. Argument order and duplicates do not affect conjunction.
For a macro whose first argument is called `next`, `CombineWithNext` proves
`Conjoin(C \cup {next}) = And(next, Conjoin(C))`, including the empty tail.
`DisjoinPair` and `DisjoinAdd` give the corresponding base and recursive
step for `.or` chains. `MergedActionAt` proves the result of the generated
action closure for every source and destination state; `LiftMergedAction`
proves its exact temporal lifting.

| Exported macro names | Checked result theorem |
| --- | --- |
| `always_and_equality_n`, `always_and_equality_n_internal` | `AlwaysConjoin` |
| `entails_and_n`, `entails_and_n_internal` | `EntailsConjoin` |
| `entails_always_and_n`, `entails_always_and_n_internal` | `EntailsAlwaysConjoin` |
| `entails_always_unpack_n`, `entails_always_unpack_n_internal` | `AlwaysUnpackConjoin` |
| `combine_with_next`, `combine_with_next_internal` | `CombineWithNext` |
| `combine_spec_entails_n`, `combine_spec_entails_n_internal` | `CombineSpecEntails` |
| `combine_spec_entails_always_n`, `combine_spec_entails_always_n_internal` | `CombineSpecEntailsAlways` |
| `invariant_n`, `invariant_n_internal` | `InvariantConjoin` |
| `stable_and_n`, `stable_and_n_internal` | `StableConjoin` |
| `stable_and_always_n`, `stable_and_always_n_internal` | `StableAlwaysConjoin` |
| `or_leads_to_n`, `or_leads_to_n_internal` | `OrLeadsToFamily` |
| `or_leads_to_combine_and_equality` | `OrLeadsToNamedResult` |
| `merge_into_next`, `merge_into_next_internal` | `MergedActionAt`, `LiftMergedAction` |

Each theorem quantifies over an arbitrary family of predicates.
`TemporalFoldRules.tla` proves the missing ordered-fold bridge for every
finite sequence of arguments. `FoldAndTraceCorrespondence` and
`FoldOrTraceCorrespondence` equate any trace satisfying the macro's recursive
conjunction or disjunction equations with `Conjoin` or `Disjoin` of the
sequence prefix. `MergedActionTraceCorrespondence` does the same for the
source-state tests in `merge_into_next`. The checked `AndTraceRecurrence`,
`OrTraceRecurrence`, and `ActionTraceRecurrence` construct traces satisfying
those equations, including the empty-list case. Thus the result theorems in
the table apply at the last trace position for arbitrary finite argument
lists, with order and duplicates preserved by the trace and erased only by
the proved set-family equivalence. `AndFoldResult`, `OrFoldResult`, and
`MergedActionFoldResult` state these last-position results explicitly. Six
proof-script macros remain open; they
need separate finite chaining or persistent-conjunction arguments.
The exact `TempPred` interpretation is the set of executions from
`TemporalPredicates.tla`. These are proof schemata for macro results, not
claims that the TLA+ checker parses or executes Rust macro syntax.
