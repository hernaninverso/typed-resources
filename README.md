# Typed Resource Bounds for LLM-Agent Workflows

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20661092.svg)](https://doi.org/10.5281/zenodo.20661092)

Machine-checked (Lean 4) cost-soundness for LLM-agent workflows: a potential-based calculus where
**well-typed ⟹ accumulated gas ≤ declared budget** on every trace, plus an affine no-double-spend
layer. Companion static checker: **[gasket](https://github.com/hernaninverso/gasket)**.

- **Paper (PDF + DOI):** https://doi.org/10.5281/zenodo.20661092
- **`lean/TypedResources.lean`** — `steps_sound`, `hastype_iff_pot`, `step_decreases` (axioms `[propext, Quot.sound]`, no `sorry`)
- **`lean/Affine.lean`** — `no_double_spend` (axioms `[propext]`)
- **`PAPER.md`** — full preprint source

Build: `lean lean/TypedResources.lean && lean lean/Affine.lean` (Lean v4.30.0, no Mathlib).
