#!/usr/bin/env python3
"""Check that the TLA+ evidence ledger accounts for the Verus API surface."""

import argparse
import csv
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "tla" / "coverage.csv"
REQUIRED_COLUMNS = {
    "kind", "name", "source", "statement", "evidence", "status",
    "semantic_assumptions", "proof_dependencies", "verification_command",
    "remaining_obligation", "attempt_command", "attempt_result",
}


def names(pattern: str, path: Path) -> set[str]:
    return set(re.findall(pattern, path.read_text()))


PUBLIC_SPEC_FN = r"pub\s+(?:(?:open|closed)\s+)?spec\s+fn\s+(\w+)"


def expected() -> set[tuple[str, str]]:
    rules = ROOT / "src" / "rules.rs"
    defs = ROOT / "src" / "defs.rs"
    action = ROOT / "src" / "action.rs"
    machine = ROOT / "src" / "state_machine.rs"
    result = {("rule", name) for name in names(r"pub\s+proof\s+fn\s+(\w+)", rules)}
    result |= {("macro", name) for name in names(r"#\[macro_export\]\s*macro_rules!\s+(\w+)", rules)}
    result |= {("definition", f"defs::{name}") for name in names(PUBLIC_SPEC_FN, defs)}
    result |= {("definition", f"Action::{name}") for name in names(PUBLIC_SPEC_FN, action)}
    result |= {
        ("definition", "StateMachine::next_result"),
        ("definition", "StateMachine::next_action_result"),
        ("definition", "NetworkStateMachine::next_result"),
        ("formulation", "Action"),
        ("formulation", "StateMachine"),
        ("formulation", "NetworkStateMachine"),
        ("formulation", "Mutex"),
        ("rule", "Action::wf1"),
    }
    machine_names = names(PUBLIC_SPEC_FN, machine)
    if machine_names != {"next_result", "next_action_result"}:
        raise ValueError(f"Update the machine inventory for public spec functions: {sorted(machine_names)}")
    if names(r"pub\s+proof\s+fn\s+(\w+)", action) != {"wf1"}:
        raise ValueError("Update the action proof inventory")
    if names(r"pub\s+proof\s+fn\s+(\w+)", machine):
        raise ValueError("Update the machine proof inventory")
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--complete", action="store_true", help="require every item to be fully proved")
    args = parser.parse_args()
    with LEDGER.open(newline="") as stream:
        reader = csv.DictReader(stream)
        missing_columns = REQUIRED_COLUMNS - set(reader.fieldnames or ())
        if missing_columns:
            print(f"missing ledger columns: {sorted(missing_columns)}")
            return 1
        rows = list(reader)
    actual = {(row["kind"], row["name"]) for row in rows}
    missing = expected() - actual
    extra = actual - expected()
    duplicates = len(actual) != len(rows)
    invalid = [row["name"] for row in rows if row["status"] not in {"proved", "defined", "model_checked", "open"}]
    incomplete_evidence = [row["name"] for row in rows if row["status"] == "proved" and not row["evidence"]]
    missing_context = [row["name"] for row in rows if not all(row[field] for field in (
        "source", "statement", "semantic_assumptions", "proof_dependencies", "verification_command"
    ))]
    missing_open_obligation = [row["name"] for row in rows if row["status"] != "proved" and not row["remaining_obligation"]]
    bad_operator_links = []
    for row in rows:
        if row["kind"] != "definition":
            continue
        match = re.fullmatch(r"(TemporalPredicates|GenericMachines)::([A-Za-z][A-Za-z0-9_]*)", row["statement"])
        if match and not re.search(rf"^{re.escape(match.group(2))}\s*(?:\(|==)",
                                   (ROOT / "tla" / f"{match.group(1)}.tla").read_text(), re.MULTILINE):
            bad_operator_links.append(row["name"])
    if (missing or extra or duplicates or invalid or incomplete_evidence or
            missing_context or missing_open_obligation or bad_operator_links):
        print(f"missing={sorted(missing)} extra={sorted(extra)} duplicates={duplicates} "
              f"invalid_status={invalid} incomplete_evidence={incomplete_evidence} "
              f"missing_context={missing_context} missing_open_obligation={missing_open_obligation} "
              f"bad_operator_links={bad_operator_links}")
        return 1
    print(f"Coverage inventory matches source: {len(rows)} items.")
    if args.complete:
        unfinished = [row["name"] for row in rows if row["status"] != "proved"]
        if unfinished:
            print(f"Incomplete translation: {len(unfinished)} items still lack checked proofs.")
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
