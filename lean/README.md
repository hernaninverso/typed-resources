# Lean 4 mechanization — Typed Resource Bounds for Agent Workflows

Self-contained, **no Mathlib**. Three files:
- `TypedResources.lean` — the potential calculus: cost-soundness, relational↔functional equivalence,
  termination measure.
- `TypedResourcesVec.lean` — the **vector** version: the same cost-soundness theorem (`vsteps_sound`)
  for an arbitrary-dimension resource vector `Res k = Fin k → ℕ` with pointwise `≤`/`+`/`max`
  (k=3 = ⟨tokens, calls, $⟩). Axioms `[propext, Quot.sound]`.
- `Affine.lean` — the affine handle layer: **no-double-spend** (`no_double_spend`, axioms `[propext]`).
  Each context handle is consumed at most once on every trace; `seqH` splits handles, `branchH`
  shares them. This is the ownership half Khan enforces with the Rust borrow checker, here mechanized.

All build with `lean <file>.lean` (exit 0, zero `sorry`).

---

## TypedResources.lean

## What is proved

`steps_sound` (the theorem of §4 of the paper):

```
theorem steps_sound {e e' g'} (h : Steps e 0 e' g') (wt : WellTyped e) : g' ≤ pot e
```

A well-typed workflow `e`, run from zero gas, spends gas `g' ≤ pot e` (its declared potential)
on **every** trace `Steps e 0 e' g'` — including partial and divergent ones (the statement
quantifies over all reachable configurations, not just terminal ones). The cost-incurring rules
`Step.call`/`Step.tool` encode the **cap axiom**: actual cost `a` satisfies `a ≤ c`.

Supporting lemmas:
- `step_sound` — single-step credit invariant: a well-typed step preserves `WellTyped` and never
  increases `gas + pot` (the AARA potential invariant).
- `steps_credit` — the same invariant lifted to the reflexive–transitive closure.

Also mechanized (added in response to the multi-model audit):
- `hastype_iff_pot : HasType p e p' ↔ (WellTyped e ∧ pot e ≤ p ∧ p' = p - pot e)` — **Lemma 0**: the
  exact relational typing judgment (`HasType`, the §3 rules written with deterministic residuals)
  coincides with the closed-form `pot`. This closes the paper's relational↔functional gap, which a
  reviewer flagged as a potential hole. Proved via `hastype_sound` (→) and `hastype_complete` (←).
- `step_decreases : Step e g e' g' → Lex e' e` — **§5 termination**: every operational step strictly
  decreases the lexicographic measure `(Wm, Sz)` (`Lex`). This refutes the objection that the measure
  fails to decrease on some rule (e.g. `loop` unfolding duplicates the body, growing `Sz`, but `Wm`
  strictly drops, so the pair decreases). Well-foundedness of `<ₗₑₓ` on ℕ×ℕ then gives SN (standard,
  not re-proved here).

## Build / verify

```
lean TypedResources.lean        # exit 0, no errors, no warnings
```

Toolchain: Lean `v4.30.0` (pinned in `lean-toolchain`). No external dependencies.

## Trust base

`#print axioms` output for every mechanized theorem (verified, Lean v4.30.0):

```
#print axioms TypedResources.steps_sound
--   depends on axioms: [propext, Quot.sound]
#print axioms TypedResources.hastype_iff_pot
--   depends on axioms: [propext, Quot.sound]
#print axioms TypedResources.step_decreases
--   depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms TypedResourcesVec.vsteps_sound
--   depends on axioms: [propext, Quot.sound]
#print axioms Affine.no_double_spend
--   depends on axioms: [propext]
```

`steps_sound`, `hastype_iff_pot`, `vsteps_sound` and `no_double_spend` use only Lean's foundational
kernel axioms (`propext`, `Quot.sound`) — **no `sorryAx`, constructive**. `step_decreases`
additionally uses `Classical.choice` (in the lexicographic-measure machinery); the headline
cost-soundness theorems do not.

## Scope (matches the paper)

This mechanizes the **weak fragment**: one resource, integer costs, pure potential, bounded
(`fuel`-carrying) loops. The fuel-free "retry until done" loop is *not representable* in `Expr`
(every `loop` carries fuel), which is exactly why the runaway pattern cannot be typed. Not
mechanized here (future work, §8): the affine no-double-spend layer, `par`/`retry`/concurrency,
and probabilistic expected-cost.
