/-
  Typed Resource Bounds — VECTOR resources (⟨tokens, calls, $⟩ and beyond), Lean 4, no Mathlib.

  Companion to `TypedResources.lean` (the scalar core). Here resources are vectors `Res k = Fin k → ℕ`
  with pointwise `≤`, `+`, scalar `n • ·`, and pointwise `max`. The SAME cost-soundness theorem is
  mechanized for ARBITRARY dimension `k` (`vsteps_sound`): a well-typed vector workflow run from the
  zero vector spends, in EVERY component, at most its declared vector potential, on any (partial or
  divergent) trace, under the per-call vector cap axiom (`∀ i, aᵢ ≤ cᵢ`).

  This closes the paper's "multi-resource is only a pen-and-paper pointwise lift" gap: the lift is
  machine-checked. The instance `k = 3` is `⟨tokens, calls, cents⟩`.

  Build:  lean TypedResourcesVec.lean   (exit 0, zero `sorry`)
-/

namespace TypedResourcesVec

/-- A resource vector of dimension `k` (e.g. ⟨tokens, calls, cents⟩ for `k = 3`). -/
abbrev Res (k : Nat) := Fin k → Nat

/-- Vector workflow expressions. `call`/`tool`/`deleg` carry resource VECTORS. -/
inductive VExpr (k : Nat) where
  | skip   : VExpr k
  | call   : Res k → VExpr k
  | tool   : Res k → VExpr k
  | seq    : VExpr k → VExpr k → VExpr k
  | branch : VExpr k → VExpr k → VExpr k
  | loop   : Nat → VExpr k → VExpr k
  | deleg  : Res k → VExpr k → VExpr k

/-- Declared vector potential, componentwise (the §3 rules lifted pointwise). -/
def vpot {k} : VExpr k → Res k
  | .skip       => fun _ => 0
  | .call c     => c
  | .tool c     => c
  | .seq a b    => fun i => vpot a i + vpot b i
  | .branch a b => fun i => Nat.max (vpot a i) (vpot b i)
  | .loop n e   => fun i => n * vpot e i
  | .deleg q _  => q

/-- Well-typedness: `delegate q e` needs the child to fit within `q` in EVERY component. -/
def vWellTyped {k} : VExpr k → Prop
  | .skip       => True
  | .call _     => True
  | .tool _     => True
  | .seq a b    => vWellTyped a ∧ vWellTyped b
  | .branch a b => vWellTyped a ∧ vWellTyped b
  | .loop _ e   => vWellTyped e
  | .deleg q e  => (∀ i, vpot e i ≤ q i) ∧ vWellTyped e

/-- Instrumented vector small-step semantics. The cap axiom is `call`/`tool`: the actual vector
    cost `a` is anything with `∀ i, aᵢ ≤ cᵢ`; gas accrues pointwise. -/
inductive VStep {k} : VExpr k → Res k → VExpr k → Res k → Prop where
  | call   {c a g : Res k} (h : ∀ i, a i ≤ c i)      : VStep (.call c) g .skip (fun i => g i + a i)
  | tool   {c a g : Res k} (h : ∀ i, a i ≤ c i)      : VStep (.tool c) g .skip (fun i => g i + a i)
  | seqL   {a a' b : VExpr k} {g g' : Res k} (h : VStep a g a' g') : VStep (.seq a b) g (.seq a' b) g'
  | seqSkip {b : VExpr k} {g : Res k}                : VStep (.seq .skip b) g b g
  | brL    {a b : VExpr k} {g : Res k}               : VStep (.branch a b) g a g
  | brR    {a b : VExpr k} {g : Res k}               : VStep (.branch a b) g b g
  | loopUnfold {n : Nat} {e : VExpr k} {g : Res k}   : VStep (.loop (n+1) e) g (.seq e (.loop n e)) g
  | loopZero {e : VExpr k} {g : Res k}               : VStep (.loop 0 e) g .skip g
  | deleg   {q : Res k} {e : VExpr k} {g : Res k}    : VStep (.deleg q e) g e g

/-- Reflexive–transitive closure. -/
inductive VSteps {k} : VExpr k → Res k → VExpr k → Res k → Prop where
  | refl {e g}                                     : VSteps e g e g
  | tail {e g e' g' e'' g''} : VSteps e g e' g' → VStep e' g' e'' g'' → VSteps e g e'' g''

/-- **Single-step soundness, pointwise.** A well-typed step preserves well-typedness and never
    increases the credit `gasᵢ + potᵢ` in ANY component. -/
theorem vstep_sound {k} {e g e' g'} (h : @VStep k e g e' g') :
    vWellTyped e → vWellTyped e' ∧ ∀ i, g' i + vpot e' i ≤ g i + vpot e i := by
  induction h with
  | call hac => intro _; exact ⟨trivial, fun i => by simp only [vpot]; have := hac i; omega⟩
  | tool hac => intro _; exact ⟨trivial, fun i => by simp only [vpot]; have := hac i; omega⟩
  | seqL _ ih =>
      intro wt
      obtain ⟨wta, wtb⟩ := wt
      obtain ⟨wta', hle⟩ := ih wta
      exact ⟨⟨wta', wtb⟩, fun i => by simp only [vpot]; have := hle i; omega⟩
  | seqSkip => intro wt; exact ⟨wt.2, fun i => by simp only [vpot]; omega⟩
  | @brL a b g =>
      intro wt
      refine ⟨wt.1, fun i => ?_⟩
      simp only [vpot, Nat.max_def]; split <;> omega
  | @brR a b g =>
      intro wt
      refine ⟨wt.2, fun i => ?_⟩
      simp only [vpot, Nat.max_def]; split <;> omega
  | @loopUnfold n e g =>
      intro wt
      refine ⟨⟨wt, wt⟩, fun i => ?_⟩
      have key : (n + 1) * vpot e i = n * vpot e i + vpot e i := by
        rw [Nat.add_mul, Nat.one_mul]
      simp only [vpot]; omega
  | loopZero => intro _; exact ⟨trivial, fun i => by simp only [vpot]; omega⟩
  | deleg => intro wt; exact ⟨wt.2, fun i => by simp only [vpot]; have := wt.1 i; omega⟩

/-- **Multi-step credit invariant**, pointwise. -/
theorem vsteps_credit {k} {e g e' g'} (h : @VSteps k e g e' g') :
    vWellTyped e → vWellTyped e' ∧ ∀ i, g' i + vpot e' i ≤ g i + vpot e i := by
  induction h with
  | refl => intro wt; exact ⟨wt, fun _ => Nat.le_refl _⟩
  | tail _ hstep ih =>
      intro wt
      obtain ⟨wte', h1⟩ := ih wt
      obtain ⟨wte'', h2⟩ := vstep_sound hstep wte'
      exact ⟨wte'', fun i => Nat.le_trans (h2 i) (h1 i)⟩

/-- **Vector cost-soundness (multi-resource §4, mechanized for arbitrary `k`).**
    From the zero vector, a well-typed workflow spends at most its declared potential in EVERY
    component, on any trace. -/
theorem vsteps_sound {k} {e e' g'} (h : @VSteps k e (fun _ => 0) e' g') (wt : vWellTyped e) :
    ∀ i, g' i ≤ vpot e i := by
  have inv := vsteps_credit h wt
  intro i
  have h2 : g' i + vpot e' i ≤ 0 + vpot e i := inv.2 i
  omega

/-! ### Sanity instance: `k = 3` = ⟨tokens, calls, cents⟩, the paper's worked example as a vector. -/

/-- A concrete 3-vector literal (no Mathlib `![..]`). -/
def v3 (a b c : Nat) : Res 3 := fun i => match i with
  | ⟨0, _⟩ => a | ⟨1, _⟩ => b | _ => c

/-- The §1 worked example, now with a `⟨tokens, calls, cents⟩` cap on each primitive:
    `call⟨4000,1,80⟩ ; loop 3 (tool⟨1000,0,5⟩ ; call⟨2000,1,40⟩) ; if deleg⟨3000,1,60⟩(call⟨2500,1,50⟩) (call⟨1200,1,24⟩)`. -/
def research : VExpr 3 :=
  .seq (.call (v3 4000 1 80))
    (.seq (.loop 3 (.seq (.tool (v3 1000 0 5)) (.call (v3 2000 1 40))))
      (.branch (.deleg (v3 3000 1 60) (.call (v3 2500 1 50))) (.call (v3 1200 1 24))))

-- tokens: 4000 + 3·(1000+2000) + max(3000,1200) = 16000  (matches the SCALAR worked example)
example : vpot research ⟨0, by decide⟩ = 16000 := by decide
-- calls:  1 + 3·(0+1) + max(1,1) = 5
example : vpot research ⟨1, by decide⟩ = 5 := by decide
-- cents:  80 + 3·(5+40) + max(60,24) = 275
example : vpot research ⟨2, by decide⟩ = 275 := by decide

/-- Well-typed: the delegate's child fits within `⟨3000,1,60⟩` in every component
    (`2500≤3000`, `1≤1`, `50≤60`). The `∀ i : Fin 3` goal is closed by a case split (no
    Mathlib `fin_cases`). -/
example : vWellTyped research := by
  refine ⟨trivial, ⟨trivial, trivial⟩, ⟨⟨?_, trivial⟩, trivial⟩⟩
  intro i
  match i with
  | ⟨0, _⟩ => simp [vpot, v3]
  | ⟨1, _⟩ => simp [vpot, v3]
  | ⟨2, _⟩ => simp [vpot, v3]

end TypedResourcesVec
