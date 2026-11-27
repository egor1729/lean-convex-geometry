#!/usr/bin/env python3
"""Validate formalization.yaml (v0.4) and comparator.json cross-file consistency.

Schema validation is delegated to the official mathlib-initiative v0.4 JSON Schema
via `--schema <path>`. This script performs only the repository-specific checks
that JSON Schema cannot express:
1. No unresolved `TEMPLATE` placeholders in `formalization.yaml`.
2. `comparator.json` structure, standard-only `permitted_axioms`, no committed
   `external_kernels`, and no duplicate `theorem_names`.
3. Cross-file consistency between `formalization.yaml` `status.main_results`,
   repository files, and `comparator.json`.
4. `Challenge.lean` imports only Lean core / Mathlib modules.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

import yaml

TEMPLATE_RE = re.compile(r"^\s*TEMPLATE(?::|\Z)")
IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+(\S+)", re.MULTILINE)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def find_template_placeholders(obj: Any, path: str = "$") -> list[str]:
    hits: list[str] = []
    if isinstance(obj, dict):
        for k, v in obj.items():
            hits.extend(find_template_placeholders(v, f"{path}.{k}"))
    elif isinstance(obj, list):
        for idx, v in enumerate(obj):
            hits.extend(find_template_placeholders(v, f"{path}[{idx}]"))
    elif isinstance(obj, str) and TEMPLATE_RE.match(obj):
        hits.append(path)
    return hits


def validate(root: Path, yaml_path: Path, schema_path: Path | None) -> list[str]:
    errors: list[str] = []
    if not yaml_path.exists():
        return [f"Missing {yaml_path}"]

    doc = yaml.safe_load(yaml_path.read_text(encoding="utf-8"))
    if not isinstance(doc, dict):
        return [f"{yaml_path}: root must be a YAML mapping"]

    if schema_path is not None:
        import jsonschema

        schema = json.loads(schema_path.read_text(encoding="utf-8"))
        try:
            jsonschema.validate(instance=doc, schema=schema)
        except jsonschema.ValidationError as exc:
            errors.append(f"JSON Schema validation failed: {exc.message}")

    for hit in find_template_placeholders(doc):
        errors.append(f"formalization.yaml: unresolved TEMPLATE placeholder at {hit}")

    # Validate comparator.json
    comp_path = root / "comparator.json"
    if not comp_path.exists():
        errors.append("Missing comparator.json")
        return errors

    comp = json.loads(comp_path.read_text(encoding="utf-8"))
    if not isinstance(comp, dict):
        errors.append("comparator.json must be a JSON object")
        return errors

    if "external_kernels" in comp:
        errors.append(
            "comparator.json: `external_kernels` must not be committed "
            "(pass bundled kernels via scripts/verify-comparator.sh)"
        )

    for req_key in ("challenge_module", "solution_module", "theorem_names", "permitted_axioms"):
        if req_key not in comp:
            errors.append(f"comparator.json: missing required field `{req_key}`")

    axioms = set(comp.get("permitted_axioms", []))
    if not axioms.issubset(STANDARD_AXIOMS):
        errors.append(
            f"comparator.json: non-standard permitted_axioms {sorted(axioms - STANDARD_AXIOMS)}"
        )

    theorem_names = comp.get("theorem_names", [])
    if not isinstance(theorem_names, list) or not theorem_names:
        errors.append("comparator.json: theorem_names must be nonempty")
    elif len(theorem_names) != len(set(theorem_names)):
        errors.append("comparator.json: duplicate entries in theorem_names")

    # Cross-check status.main_results against comparator.json and repository files
    status = doc.get("status", {})
    if isinstance(status, dict):
        for i, res in enumerate(status.get("main_results", []) or []):
            decl = res.get("declaration", "")
            frel = res.get("file", "")
            ccfg = res.get("comparator_config", "")
            if frel and not (root / frel).exists():
                errors.append(f"formalization.yaml: main_results[{i}].file `{frel}` not found")
            if ccfg and not (root / ccfg).exists():
                errors.append(
                    f"formalization.yaml: main_results[{i}].comparator_config `{ccfg}` not found"
                )
            if ccfg == "comparator.json" and decl not in theorem_names:
                errors.append(
                    f"formalization.yaml: main_results[{i}].declaration `{decl}` "
                    "not listed in comparator.json"
                )

    # Check Challenge.lean imports only Lean core / Mathlib
    challenge_path = root / "Challenge.lean"
    if not challenge_path.exists():
        errors.append("Missing Challenge.lean")
    else:
        for m in IMPORT_RE.finditer(challenge_path.read_text(encoding="utf-8")):
            mod = m.group(1)
            if not (mod == "Mathlib" or mod.startswith(("Mathlib.", "Init", "Lean", "Std"))):
                errors.append(f"Challenge.lean: disallowed non-Mathlib import `{mod}`")

    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--file", default="formalization.yaml", help="Path to formalization.yaml")
    parser.add_argument("--schema", default=None, help="Path to official v0.4.schema.json")
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    yaml_path = (root / args.file).resolve()
    schema_path = Path(args.schema).resolve() if args.schema else None

    errors = validate(root, yaml_path, schema_path)
    if errors:
        print("Metadata validation FAILED:", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        return 1

    print(f"Metadata validation PASSED ({args.file} + comparator.json).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
