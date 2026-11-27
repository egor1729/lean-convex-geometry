#!/usr/bin/env python3
"""Fast pre-build static checks for Lean source files (Palomar-compatible).

Checks:
1. Every regular `.lean` file outside `.git`/`.lake` is valid UTF-8, not a
   symlink, has <= 10,000 physical lines, and starts with the `module` header
   keyword (except `lakefile.lean`).
2. `Challenge.lean` is <= 1,000 physical lines, <= 100 KiB, and imports only
   Lean core / Mathlib (no `ConvexGeom` or `Solution` imports).
3. No `sorry`, `admit`, `native_decide`, `implemented_by`, or `@[extern`
   tokens appear in non-comment code outside `Challenge.lean`.
"""
from __future__ import annotations

import os
import re
import sys
from pathlib import Path

COMMENT_MARKER = re.compile(r"/-|-/")
ID_LETTER_LIKE = (
    r"\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    r"\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
)
ID_FIRST = rf"A-Za-z_{ID_LETTER_LIKE}"
ID_REST = rf"{ID_FIRST}0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
IDENTIFIER_CONTINUATION = re.compile(rf"[{ID_REST}]|\.[{ID_FIRST}«]")

IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+(\S+)", re.MULTILINE)
FORBIDDEN_CODE_RE = re.compile(
    r"\b(?:sorry|admit|native_decide|implemented_by)\b|@\[extern\b"
)


def strip_comments_and_strings(text: str) -> str:
    """Strip Lean line comments, nested block comments, and string literals."""
    out: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if text.startswith("--", i):
            end = text.find("\n", i + 2)
            if end < 0:
                break
            out.append("\n")
            i = end + 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while i < n and depth > 0:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    if text[i] == "\n":
                        out.append("\n")
                    i += 1
        elif ch == '"':
            out.append(" ")
            i += 1
            while i < n:
                if text[i] == "\\" and i + 1 < n:
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    if text[i] == "\n":
                        out.append("\n")
                    i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def has_module_header(text: str) -> bool:
    """Recognize the initial `module` header keyword without being fooled by comments."""
    index = 0
    while index < len(text):
        if text[index] in " \r\n":
            index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index + 2)
            index = len(text) if end < 0 else end + 1
        elif text.startswith("/-", index) and not text.startswith(("/--", "/-!"), index):
            index += 3
            depth = 1
            while depth:
                marker = COMMENT_MARKER.search(text, index)
                if marker is None:
                    break
                depth += 1 if marker.group() == "/-" else -1
                index = marker.end()
            if depth:
                return False
        else:
            return text.startswith("module", index) and (
                IDENTIFIER_CONTINUATION.match(text, index + 6) is None
            )
    return False


def physical_lines(text: str) -> int:
    return text.count("\n") + int(bool(text) and not text.endswith("\n"))


def lean_source_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for directory, subdirectories, names in os.walk(root, followlinks=False):
        subdirectories[:] = sorted(
            name for name in subdirectories
            if name not in {".git", ".lake"} and not (Path(directory) / name).is_symlink()
        )
        for name in sorted(names):
            path = Path(directory) / name
            if name.endswith(".lean") and (path.is_symlink() or path.is_file()):
                files.append(path)
    return files


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    errors: list[str] = []
    files = lean_source_files(root)

    for path in files:
        rel = path.relative_to(root).as_posix()
        if path.is_symlink():
            errors.append(f"{rel}: must be a regular file, not a symbolic link")
            continue
        raw = path.read_bytes()
        try:
            text = raw.decode("utf-8")
        except UnicodeDecodeError:
            errors.append(f"{rel}: not valid UTF-8")
            continue

        lines = physical_lines(text)
        if path.name != "lakefile.lean" and not has_module_header(text):
            errors.append(f"{rel}: missing Lean `module` header keyword")
        if lines > 10_000:
            errors.append(f"{rel}: {lines} lines exceeds 10,000-line cap")

        code = strip_comments_and_strings(text)
        if rel == "Challenge.lean":
            if lines > 1_000:
                errors.append(f"Challenge.lean: {lines} lines exceeds 1,000-line Palomar cap")
            if len(raw) > 100 * 1024:
                errors.append(f"Challenge.lean: {len(raw)} bytes exceeds 100 KiB Palomar cap")
            for m in IMPORT_RE.finditer(code):
                mod = m.group(1)
                if not (mod == "Mathlib" or mod.startswith(("Mathlib.", "Init", "Lean", "Std"))):
                    errors.append(f"Challenge.lean: disallowed non-Mathlib import `{mod}`")
            if re.search(r"^\s*(?:public\s+)?import\s+Mathlib\s*$", code, re.MULTILINE):
                errors.append("Challenge.lean: avoid blanket `import Mathlib`; use targeted imports")
        else:
            for m in FORBIDDEN_CODE_RE.finditer(code):
                lineno = code[: m.start()].count("\n") + 1
                errors.append(f"{rel}:{lineno}: forbidden token `{m.group(0)}`")

    if errors:
        print("Lean source hygiene check FAILED:", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        return 1

    print(f"Lean source hygiene check PASSED ({len(files)} .lean files checked).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
