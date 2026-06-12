# Lean 4 mechanization — Typed Resource Bounds for Agent Workflows

Self-contained, **no Mathlib**. Single file: `TypedResources.lean`.

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

## Build / verify

```
lean TypedResources.lean        # exit 0, no errors, no warnings
```

Toolchain: Lean `v4.30.0` (pinned in `lean-toolchain`). No external dependencies.

## Trust base

```
#print axioms TypedResources.steps_sound
-- 'TypedResources.steps_sound' depends on axioms: [propext, Quot.sound]
```

Only `propext` and `Quot.sound` — Lean's two foundational kernel axioms. **No `sorryAx`, no
`Classical.choice`.** The proof is constructive.

## Scope (matches the paper)

This mechanizes the **weak fragment**: one resource, integer costs, pure potential, bounded
(`fuel`-carrying) loops. The fuel-free "retry until done" loop is *not representable* in `Expr`
(every `loop` carries fuel), which is exactly why the runaway pattern cannot be typed. Not
mechanized here (future work, §8): the affine no-double-spend layer, `par`/`retry`/concurrency,
and probabilistic expected-cost.
