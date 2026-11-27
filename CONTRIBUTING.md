# Contributing to `lean-convex-geometry`

Contributions are welcome. Please follow these guidelines when adding or updating modules.

## Design Guidelines

- **General building blocks first:** State definitions and theorems at natural Mathlib generality rather than building single-use machinery. Reuse existing Mathlib abstractions and add bridge lemmas where helpful.
- **Structural proofs:** Build on existing layers; extract missing general lemmas rather than duplicating arguments inline.
- **Focused commits:** Keep commits small and cohesive (one module, lemma group, or doc change per commit).
- **Module headers and style:** Follow Mathlib's standard linter set (`weak.linter.mathlibStandardSet = true`, 100-character line limit) and include the 3-line Apache-2.0 header at the top of each `.lean` file.

## Local Verification

Run the standard Lake checks before opening a pull request:

```bash
# Build the library and Comparator solution with warnings as errors
lake build ConvexGeom Solution --wfail

# Run the test suite (ConvexGeomTest)
lake test

# Run Batteries environment linters on ConvexGeom
lake lint

# Verify ConvexGeom.lean imports every module in ConvexGeom/
lake exe mk_all --check --lib ConvexGeom

# Replay a compiled module environment through the bundled leanchecker
lake env leanchecker ConvexGeom.Metric.SupportFunction

# Optional: sandboxed statement comparison with bundled external kernels (Linux + bwrap)
bash scripts/verify-comparator.sh --skip-cache
```

If you add a new module under `ConvexGeom/`, regenerate `ConvexGeom.lean` with:

```bash
lake exe mk_all --lib ConvexGeom
```

You can also regenerate the module import graph with `lake exe graph`.

## Licensing

All contributions are licensed under the [Apache License 2.0](LICENSE).
