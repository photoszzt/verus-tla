# Verus-TLA

[![CI](https://github.com/anvil-verifier/verus-tla/actions/workflows/ci.yml/badge.svg)](https://github.com/anvil-verifier/verus-tla/actions/workflows/ci.yml)

A [Verus](https://github.com/verus-lang/verus) embedding of TLA (Temporal Logic of Actions), ported from [Anvil](https://github.com/anvil-verifier/anvil).

The crate provides:

- **`defs`** — `Execution`, `TempPred`, and the temporal connectives (`always`, `eventually`, `leads_to`, `weak_fairness`, `valid`, `entails`, `tla_forall`, `tla_exists`, `stable`, …).
- **`rules`** — verified TLA helper lemmas (modus ponens, weak-fairness, induction, monotonicity, ESR, etc.) for liveness and safety proofs.
- **`state_machine`** — `Action`, `StateMachine`, and `NetworkStateMachine` structs for defining state-transition systems with preconditions, transitions, and weak-fairness assumptions.

**Execution Model**

```rust
pub struct Execution<T> {
    pub nat_to_state: spec_fn(nat) -> T,
}
```

## Usage

```toml
[dependencies]
vstd = { git = "https://github.com/verus-lang/verus.git" }
verus_temporal_logic = { git = "https://github.com/anvil-verifier/verus-tla" }
```

Build your local Verus binary following the instructions in [`BUILD.md`](https://github.com/verus-lang/verus/blob/main/BUILD.md) from the `main` branch of Verus.

## Example

See [`src/mutex_example.rs`](src/mutex_example.rs).

## Build & verify

This crate uses [`cargo verus`](https://github.com/verus-lang/verus).

```sh
# Verify the library (defs + rules + state_machine)
cargo verus verify --lib

# Verify the mutex liveness example
cargo verus verify --bin mutex_example
```

## TLA+ translation (in progress)

The [`tla` directory](tla/) contains a behavior-set image of the Verus
definitions, generic action and machine formulations, native temporal laws,
and a finite two-thread mutex model. [`tla/coverage.csv`](tla/coverage.csv)
tracks every public source rule, exported macro, definition, and formulation.
An `open` or `defined` row is **not** a checked generic correspondence.

The exact image treats a temporal predicate as a set of infinite behaviors and
defines `Later(P)` by applying `P` to the behavior's suffix at index one. The
native mutex uses `[Next]_vars` and `WF_vars` so TLC can check safety and
fairness-dependent liveness. Native `WF_vars(A)` excludes stuttering instances
of `A`; Verus's `weak_fairness(A)` uses its raw action predicate. The generic
fairness bridge remains an open proof obligation.

The verified subset can be checked locally with Java 17, the official
`tla2tools.jar` v1.8.0 (SHA-256
`7beec0f04818732a62fa193731711a99aa4f11279499b2360a7d156c519ea78d`),
and TLAPM. On Linux, [`tools/setup-tla-linux.sh`](tools/setup-tla-linux.sh)
installs the pinned TLC JAR and TLAPM `1.6.0-pre` archive (SHA-256
`13eff4e3dd0a4570c1c33c46f052fd4eb3afad465eb201ebade607961f09d43c`).
Then run:

```sh
export TLA_TOOLS_JAR="$PWD/.tla-tools/tla2tools.jar"
export TLAPM_BIN="$PWD/.tla-tools/tlapm/bin/tlapm"
tools/verify-tla.sh
python3 tools/check-tla-coverage.py --complete
```

`verify-tla.sh` prints each SANY, TLAPM, and TLC command. TLC exhausts the
finite generic-machine and mutex models; the unfair mutex configuration must
fail its progress property. CI checks these proofs, finite models, and the
source inventory on every pull request with a 30-minute TLA+ job limit. The
separate `--complete` gate currently fails while generic rules and
correspondence proofs remain open.

## License

MIT (inherited from the original [anvil temporal_logic module](https://github.com/anvil-verifier/anvil/tree/main/src/temporal_logic)).
