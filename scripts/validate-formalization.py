#!/usr/bin/env python3
"""Validate formalization.yaml (v0.4) and comparator.json consistency.

Runs fast with zero network access by default; pass `--schema <path>` to also
validate against the official mathlib-initiative v0.4 JSON schema (requires
`jsonschema` + `pyyaml`).
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

TEMPLATE_RE = re.compile(r"^\s*TEMPLATE(?::|\Z)")
VALID_RELATIONSHIPS = {
    "formalizes",
    "adapts",
    "independently-proves",
    "background",
    "other",
}
VALID_METHODS = {"manual", "copilot", "agent", "autonomous", "other"}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def load_yaml(path: Path) -> Any:
    """Parse YAML via PyYAML, falling back to /usr/bin/python3 or ruby stdlib."""
    try:
        import yaml  # type: ignore

        return yaml.safe_load(path.read_text(encoding="utf-8"))
    except ModuleNotFoundError:
        pass

    sys_py = Path("/usr/bin/python3")
    if sys_py.exists() and str(sys_py) != sys.executable:
        res = subprocess.run(
            [str(sys_py), "-c", "import json,sys,yaml; print(json.dumps(yaml.safe_load(open(sys.argv[1], encoding='utf-8'))))", str(path)],
            capture_output=True,
            text=True,
        )
        if res.returncode == 0:
            return json.loads(res.stdout)

    res = subprocess.run(
        [
            "ruby",
            "-ryaml",
            "-rjson",
            "-e",
            "puts JSON.generate(YAML.safe_load(File.read(ARGV[0]), permitted_classes: [], permitted_symbols: [], aliases: false))",
            str(path),
        ],
        capture_output=True,
        text=True,
    )
    if res.returncode == 0:
        return json.loads(res.stdout)

    raise RuntimeError(
        "Could not parse YAML: install PyYAML (`pip install pyyaml` or `python3-yaml`)."
    )


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


def validate_formalization(root: Path, yaml_path: Path, schema_path: Path | None) -> list[str]:
    errors: list[str] = []
    if not yaml_path.exists():
        return [f"Missing {yaml_path}"]

    doc = load_yaml(yaml_path)
    if not isinstance(doc, dict):
        return [f"{yaml_path}: root must be a YAML mapping"]

    # Optional official JSON Schema validation
    if schema_path is not None:
        try:
            import jsonschema  # type: ignore

            schema = json.loads(schema_path.read_text(encoding="utf-8"))
            jsonschema.validate(instance=doc, schema=schema)
        except ModuleNotFoundError:
            sys_py = Path("/usr/bin/python3")
            if sys_py.exists():
                res = subprocess.run(
                    [
                        str(sys_py),
                        "-c",
                        "import json,sys,yaml,jsonschema; jsonschema.validate(yaml.safe_load(open(sys.argv[1])), json.load(open(sys.argv[2])))",
                        str(yaml_path),
                        str(schema_path),
                    ],
                    capture_output=True,
                    text=True,
                )
                if res.returncode != 0:
                    errors.append(f"JSON Schema validation failed: {res.stderr.strip()}")
            else:
                errors.append("`--schema` requested but `jsonschema` is not installed")
        except Exception as exc:
            errors.append(f"JSON Schema validation failed: {exc}")

    # No retained template placeholders
    for hit in find_template_placeholders(doc):
        errors.append(f"formalization.yaml: unresolved TEMPLATE placeholder at {hit}")

    # Version and core required sections
    if doc.get("version") != "v0.4":
        errors.append(f"formalization.yaml: $.version must be 'v0.4', got {doc.get('version')!r}")

    for sec in ("project", "sources", "automation", "review"):
        if sec not in doc:
            errors.append(f"formalization.yaml: missing required section `{sec}`")

    project = doc.get("project", {})
    if isinstance(project, dict):
        if not isinstance(project.get("name"), str) or not project["name"].strip():
            errors.append("formalization.yaml: project.name must be nonempty")
        desc = project.get("description", "")
        if not isinstance(desc, str) or not desc.strip() or len(desc.strip()) > 10_000:
            errors.append("formalization.yaml: project.description must be nonempty and <= 10,000 chars")
        for key in ("authors", "responsible_maintainers"):
            vals = project.get(key)
            if not isinstance(vals, list) or not vals or not all(isinstance(x, str) and x.strip() for x in vals):
                errors.append(f"formalization.yaml: project.{key} must be a nonempty list of strings")
        lic = project.get("license")
        if lic != "Apache-2.0":
            errors.append(f"formalization.yaml: project.license must be 'Apache-2.0', got {lic!r}")
        lic_file = root / "LICENSE"
        if not lic_file.exists() or "Apache License" not in lic_file.read_text(encoding="utf-8"):
            errors.append("LICENSE file missing or does not match Apache-2.0")

    sources = doc.get("sources", [])
    if not isinstance(sources, list) or not sources:
        errors.append("formalization.yaml: sources must be a nonempty list")
    else:
        for i, src in enumerate(sources):
            if not isinstance(src, dict) or not str(src.get("title", "")).strip():
                errors.append(f"formalization.yaml: sources[{i}].title must be nonempty")
            rel = src.get("relationship", "")
            if rel not in VALID_RELATIONSHIPS:
                errors.append(f"formalization.yaml: sources[{i}].relationship={rel!r} not in {sorted(VALID_RELATIONSHIPS)}")

    automation = doc.get("automation", {})
    methods = automation.get("methods") if isinstance(automation, dict) else None
    if not isinstance(methods, list) or not methods:
        errors.append("formalization.yaml: automation.methods must be a nonempty list")
    else:
        for i, m in enumerate(methods):
            if not isinstance(m, dict) or m.get("method") not in VALID_METHODS:
                errors.append(f"formalization.yaml: automation.methods[{i}].method invalid")

    review = doc.get("review", {})
    if not isinstance(review, dict) or not str(review.get("status", "")).strip():
        errors.append("formalization.yaml: review.status must be nonempty")

    # Validate comparator.json consistency
    comp_path = root / "comparator.json"
    if not comp_path.exists():
        errors.append("Missing comparator.json")
        return errors

    comp = json.loads(comp_path.read_text(encoding="utf-8"))
    if not isinstance(comp, dict):
        errors.append("comparator.json must be a JSON object")
        return errors

    if "external_kernels" in comp:
        errors.append("comparator.json: `external_kernels` must not be committed (Palomar rejects it; pass via scripts/verify-comparator.sh)")

    for req_key in ("challenge_module", "solution_module", "theorem_names", "permitted_axioms"):
        if req_key not in comp:
            errors.append(f"comparator.json: missing required field `{req_key}`")

    axioms = set(comp.get("permitted_axioms", []))
    if not axioms.issubset(STANDARD_AXIOMS):
        errors.append(f"comparator.json: non-standard permitted_axioms {sorted(axioms - STANDARD_AXIOMS)}")

    theorem_names = comp.get("theorem_names", [])
    if not isinstance(theorem_names, list) or not theorem_names:
        errors.append("comparator.json: theorem_names must be nonempty")
    elif len(theorem_names) != len(set(theorem_names)):
        errors.append("comparator.json: duplicate entries in theorem_names")

    # Cross-check status.main_results against comparator.json and repository files
    status = doc.get("status", {})
    if isinstance(status, dict):
        for key in ("sorry_count", "sorry_in_definitions"):
            val = status.get(key)
            if not isinstance(val, int) or isinstance(val, bool) or val < 0:
                errors.append(f"formalization.yaml: status.{key} must be a nonnegative integer")
        for i, res in enumerate(status.get("main_results", []) or []):
            decl = res.get("declaration", "")
            frel = res.get("file", "")
            ccfg = res.get("comparator_config", "")
            if frel and not (root / frel).exists():
                errors.append(f"formalization.yaml: main_results[{i}].file `{frel}` not found")
            if ccfg and not (root / ccfg).exists():
                errors.append(f"formalization.yaml: main_results[{i}].comparator_config `{ccfg}` not found")
            if ccfg == "comparator.json" and decl not in theorem_names:
                errors.append(f"formalization.yaml: main_results[{i}].declaration `{decl}` not listed in comparator.json")

    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--file", default="formalization.yaml", help="Path to formalization.yaml")
    parser.add_argument("--schema", default=None, help="Optional path to v0.4.schema.json")
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    yaml_path = (root / args.file).resolve()
    schema_path = Path(args.schema).resolve() if args.schema else None

    errors = validate_formalization(root, yaml_path, schema_path)
    if errors:
        print("Metadata validation FAILED:", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        return 1

    print(f"Metadata validation PASSED ({args.file} + comparator.json).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
