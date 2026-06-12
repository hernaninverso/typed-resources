/-
  Typed Resource Bounds for Agent Workflows — Lean 4 mechanization (self-contained, no Mathlib).

  Central result (`steps_sound`): a well-typed workflow `e` with declared potential `pot e`
  spends gas `g' ≤ pot e` on EVERY trace from `(e, 0)`, including partial / divergent ones,
  under the cap axiom (per-call actual cost `a ≤ c`). This is the machine-checked form of §4.

  Build:  lean TypedResources.lean   (exit 0, zero `sorry`, zero extra axioms)
-/

namespace TypedResources

/-- Workflow expressions. `call`/`tool` are the cost-incurring primitives, capped at `c`. -/
inductive Expr where
  | skip   : Expr
  | call   : Nat → Expr            -- call(c): model call, billed ≤ c
  | tool   : Nat → Expr            -- tool(c): tool call, billed ≤ c
  | seq    : Expr → Expr → Expr
  | branch : Expr → Expr → Expr    -- if with two branches (potential = max)
  | loop   : Nat → Expr → Expr     -- loop(n,e): bounded iteration with fuel n
  | deleg  : Nat → Expr → Expr     -- delegate(q,e): child runs under transferred potential q
  deriving Repr

open Expr

/-- Declared potential: the closed form of the §3 typing rules. `HasCost e b := pot e ≤ b`. -/
def pot : Expr → Nat
  | skip       => 0
  | call c     => c
  | tool c     => c
  | seq a b    => pot a + pot b
  | branch a b => Nat.max (pot a) (pot b)
  | loop n e   => n * pot e
  | deleg q _  => q                -- parent loses the full transferred q (linear split)

/-- Well-typedness side-condition: `delegate q e` requires the child to fit within `q`.
    Marked `reducible` so `WellTyped skip ≡ True` is seen through in term mode. -/
@[reducible] def WellTyped : Expr → Prop
  | skip       => True
  | call _     => True
  | tool _     => True
  | seq a b    => WellTyped a ∧ WellTyped b
  | branch a b => WellTyped a ∧ WellTyped b
  | loop _ e   => WellTyped e
  | deleg q e  => pot e ≤ q ∧ WellTyped e

/-- Instrumented small-step semantics, on `(expr, gas)` given as two explicit arguments.
    The cap axiom is the `call`/`tool` rules: the actual cost `a` is anything with `a ≤ c`. -/
inductive Step : Expr → Nat → Expr → Nat → Prop where
  | call   {c a g} (h : a ≤ c)                : Step (call c) g skip (g + a)
  | tool   {c a g} (h : a ≤ c)                : Step (tool c) g skip (g + a)
  | seqL   {a a' b g g'} (h : Step a g a' g') : Step (seq a b) g (seq a' b) g'
  | seqSkip {b g}                             : Step (seq skip b) g b g
  | brL    {a b g}                            : Step (branch a b) g a g
  | brR    {a b g}                            : Step (branch a b) g b g
  | loopUnfold {n e g}                        : Step (loop (n+1) e) g (seq e (loop n e)) g
  | loopZero {e g}                            : Step (loop 0 e) g skip g
  | deleg   {q e g}                           : Step (deleg q e) g e g

/-- Reflexive–transitive closure of `Step`. -/
inductive Steps : Expr → Nat → Expr → Nat → Prop where
  | refl {e g}                                : Steps e g e g
  | tail {e g e' g' e'' g''} : Steps e g e' g' → Step e' g' e'' g'' → Steps e g e'' g''

/-- **Single-step soundness (the AARA invariant).**
    A well-typed step preserves well-typedness and never increases the credit `gas + pot`. -/
theorem step_sound {e g e' g'} (h : Step e g e' g') :
    WellTyped e → WellTyped e' ∧ g' + pot e' ≤ g + pot e := by
  induction h with
  | call hac => intro _; exact ⟨trivial, by simp only [pot]; omega⟩
  | tool hac => intro _; exact ⟨trivial, by simp only [pot]; omega⟩
  | seqL hstep ih =>
      intro wt
      obtain ⟨wta, wtb⟩ := wt
      obtain ⟨wta', hle⟩ := ih wta
      exact ⟨⟨wta', wtb⟩, by simp only [pot]; omega⟩
  | seqSkip => intro wt; exact ⟨wt.2, by simp only [pot]; omega⟩
  | @brL a b g =>
      intro wt
      refine ⟨wt.1, ?_⟩
      simp only [pot, Nat.max_def]; split <;> omega
  | @brR a b g =>
      intro wt
      refine ⟨wt.2, ?_⟩
      simp only [pot, Nat.max_def]; split <;> omega
  | @loopUnfold n e g =>
      intro wt
      refine ⟨⟨wt, wt⟩, ?_⟩
      have key : (n + 1) * pot e = n * pot e + pot e := by rw [Nat.add_mul, Nat.one_mul]
      simp only [pot, key]; omega
  | loopZero => intro _; exact ⟨trivial, by simp only [pot]; omega⟩
  | deleg => intro wt; exact ⟨wt.2, by simp only [pot]; omega⟩

/-- **Multi-step credit invariant.** The credit `gas + pot` never increases along any trace. -/
theorem steps_credit {e g e' g'} (h : Steps e g e' g') :
    WellTyped e → WellTyped e' ∧ g' + pot e' ≤ g + pot e := by
  induction h with
  | refl => intro wt; exact ⟨wt, Nat.le_refl _⟩
  | tail _ hstep ih =>
      intro wt
      obtain ⟨wte', h1⟩ := ih wt
      obtain ⟨wte'', h2⟩ := step_sound hstep wte'
      exact ⟨wte'', Nat.le_trans h2 h1⟩

/-- **Cost-soundness (the theorem of §4).**
    A well-typed workflow run from zero gas spends at most its declared potential, on any
    (partial or divergent) trace. -/
theorem steps_sound {e e' g'} (h : Steps e 0 e' g') (wt : WellTyped e) : g' ≤ pot e := by
  have inv := steps_credit h wt
  have h2 : g' + pot e' ≤ 0 + pot e := inv.2
  omega

/-! ### Sanity instances (compile-time checks of the headline numbers, by pure computation). -/

/-- The fuel-free runaway loop is NOT expressible: every `loop` carries fuel, so it cannot even
    be written. The A2A loop with fuel 10 has potential `10*(800+600) = 14000`. -/
def a2aBody : Expr := seq (call 800) (tool 600)
def a2aFuel10 : Expr := loop 10 a2aBody
example : pot a2aFuel10 = 14000 := by decide
example : WellTyped a2aFuel10 := by simp [WellTyped, a2aFuel10, a2aBody]

/-- Delegation conservation: parent potential 5000 ≥ children 2000+2500 = 4500. -/
def parent : Expr := seq (deleg 2000 (call 1500)) (deleg 2500 (tool 2000))
example : pot parent = 4500 := by decide
example : WellTyped parent := by simp [WellTyped, parent, pot]

end TypedResources
