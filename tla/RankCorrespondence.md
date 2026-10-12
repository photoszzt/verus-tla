# Finite rank and ascending-chain rules

`TemporalRankRules.tla` checks four source rules with explicit behavior-set
premises. `AscendingChainToEnd` corresponds to
`leads_to_greater_until_rec`: for every `n <= Max`, a sequence of adjacent
`S => F[i] ~> F[i+1]` facts gives `S => F[n] ~> F[Max]`.
`LeadsToGreaterUntil` adds the source premise that `P` implies some `F[n]`
for `n <= Max`; the checked existential leads-to law then gives
`S => P ~> F[Max]`.

`RankStepOne` proves by natural-number induction that a step from each
positive rank to its predecessor gives `S => F[n] ~> F[0]` for every natural
`n`. `BoundedRankStepOne` proves the same result on every finite range
`0..Max`. Instantiating `Max` with the platform's largest `usize` value
covers the source `usize` variant. The proof is generic in the finite bound;
it does not assume a particular machine word size.
