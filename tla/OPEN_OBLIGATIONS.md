# Open TLA+ verification obligations

The source inventory and current verification status are in
[`coverage.csv`](coverage.csv). Rows marked `open`, `defined`, or
`model_checked` are not yet certified by the agreed completion gate. A TLC
finite pass and a native `BY PTL` theorem do not prove an exact generic source
correspondence.

The largest open proof groups are:

1. Generic state/action and behavior-to-native bridges, especially raw Verus
   weak fairness versus native `WF_vars`, enabledness, and stuttering.
2. Arbitrary temporal `Later`, finite-domain quantifier convergence,
   natural-number rank induction, and ESR recursion.
3. The exact invariant-preservation and WF1 rules tied to `Next`.
4. Exact behavior-set closures of the remaining leads-to combinations and
   quantified stability rules.
5. Source-level definition correspondence for the macro result schemata.

The local proof command is
`cd tla && "$TLAPM_BIN" TemporalSetRules.tla`.

Pull requests run the checked proof modules and finite models, then validate
the source inventory with
`python3 tools/check-tla-coverage.py`. The stricter `--complete` gate remains
red until every ledger row has checked evidence.
