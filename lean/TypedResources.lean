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

/-! ### Relational typing judgment and its equivalence to `pot` (mechanizes Lemma 0).
    The §3 typing rules, written EXACTLY (deterministic residual, no slack). We prove the relational
    judgment is completely determined by `pot`+`WellTyped`, closing the relational↔functional gap. -/

/-- Exact relational typing `p ⊢ e : ⋄ ; p'` (incoming `p`, residual `p'`). -/
inductive HasType : Nat → Expr → Nat → Prop where
  | skip   {p}                              : HasType p skip p
  | call   {p c} (h : c ≤ p)                : HasType p (call c) (p - c)
  | tool   {p c} (h : c ≤ p)                : HasType p (tool c) (p - c)
  | seq    {p e₁ e₂ p₁ p₂} : HasType p e₁ p₁ → HasType p₁ e₂ p₂ → HasType p (seq e₁ e₂) p₂
  | branch {p e₁ e₂ p₁ p₂} : HasType p e₁ p₁ → HasType p e₂ p₂ → HasType p (branch e₁ e₂) (Nat.min p₁ p₂)
  | loop   {p n e} (hbody : HasType (pot e) e 0) (h : n * pot e ≤ p) : HasType p (loop n e) (p - n * pot e)
  | deleg  {p q e q'} (hbody : HasType q e q') (h : q ≤ p) : HasType p (deleg q e) (p - q)

/-- Soundness of the relational rules: a derivation pins `WellTyped`, the bound, and the residual. -/
theorem hastype_sound {p e p'} (h : HasType p e p') :
    WellTyped e ∧ pot e ≤ p ∧ p' = p - pot e := by
  induction h with
  | @skip p => exact ⟨trivial, by simp [pot], by simp [pot]⟩
  | @call p c hc => exact ⟨trivial, by simpa [pot] using hc, by simp [pot]⟩
  | @tool p c hc => exact ⟨trivial, by simpa [pot] using hc, by simp [pot]⟩
  | @seq p e₁ e₂ p₁ p₂ _ _ ih₁ ih₂ =>
      obtain ⟨w₁, b₁, r₁⟩ := ih₁; obtain ⟨w₂, b₂, r₂⟩ := ih₂
      refine ⟨⟨w₁, w₂⟩, ?_, ?_⟩ <;> simp only [pot] <;> omega
  | @branch p e₁ e₂ p₁ p₂ _ _ ih₁ ih₂ =>
      obtain ⟨w₁, b₁, rfl⟩ := ih₁; obtain ⟨w₂, b₂, rfl⟩ := ih₂
      refine ⟨⟨w₁, w₂⟩, ?_, ?_⟩
      · simp only [pot, Nat.max_def]; split <;> omega
      · simp only [pot, Nat.min_def, Nat.max_def]; split <;> split <;> omega
  | @loop p n e hbody h ihbody =>
      obtain ⟨w, _, _⟩ := ihbody
      exact ⟨w, by simpa [pot] using h, by simp [pot]⟩
  | @deleg p q e q' hbody h ihbody =>
      obtain ⟨w, b, _⟩ := ihbody
      exact ⟨⟨b, w⟩, by simpa [pot] using h, by simp [pot]⟩

/-- Completeness: every well-typed `e` with enough potential has a (unique) derivation. -/
theorem hastype_complete : ∀ {e p}, WellTyped e → pot e ≤ p → HasType p e (p - pot e) := by
  intro e
  induction e with
  | skip => intro p _ _; simpa [pot] using HasType.skip (p := p)
  | call c => intro p _ hb; simpa [pot] using HasType.call (p := p) (c := c) (by simpa [pot] using hb)
  | tool c => intro p _ hb; simpa [pot] using HasType.tool (p := p) (c := c) (by simpa [pot] using hb)
  | seq a b iha ihb =>
      intro p wt hb
      obtain ⟨wa, wb⟩ := wt
      have hba : pot a ≤ p := by simp only [pot] at hb; omega
      have hbb : pot b ≤ p - pot a := by simp only [pot] at hb; omega
      have da := iha wa hba
      have db := ihb wb hbb
      have : HasType p (seq a b) (p - pot a - pot b) := HasType.seq da db
      simpa [pot, Nat.sub_sub] using this
  | branch a b iha ihb =>
      intro p wt hb
      obtain ⟨wa, wb⟩ := wt
      have hbm : Nat.max (pot a) (pot b) ≤ p := by simpa [pot] using hb
      have hba : pot a ≤ p := Nat.le_trans (Nat.le_max_left _ _) hbm
      have hbb : pot b ≤ p := Nat.le_trans (Nat.le_max_right _ _) hbm
      have da := iha wa hba
      have db := ihb wb hbb
      have hmin : Nat.min (p - pot a) (p - pot b) = p - pot (branch a b) := by
        simp only [pot, Nat.min_def, Nat.max_def]; split <;> split <;> omega
      have : HasType p (branch a b) (Nat.min (p - pot a) (p - pot b)) := HasType.branch da db
      rwa [hmin] at this
  | loop n e ih =>
      intro p wt hb
      have hbody : HasType (pot e) e 0 := by
        have := ih wt (Nat.le_refl _); simpa using this
      have hb' : n * pot e ≤ p := by simpa [pot] using hb
      simpa [pot] using HasType.loop hbody hb'
  | deleg q e ih =>
      intro p wt hb
      obtain ⟨hq, we⟩ := wt
      have hbody : HasType q e (q - pot e) := ih we hq
      have hb' : q ≤ p := by simpa [pot] using hb
      simpa [pot] using HasType.deleg hbody hb'

/-- **Lemma 0, mechanized.** The relational judgment is exactly `pot`+`WellTyped`. -/
theorem hastype_iff_pot {p e p'} :
    HasType p e p' ↔ (WellTyped e ∧ pot e ≤ p ∧ p' = p - pot e) := by
  constructor
  · exact hastype_sound
  · rintro ⟨wt, hb, rfl⟩; exact hastype_complete wt hb

/-! ### Strong normalization: a lexicographic measure that strictly decreases on every step.
    This mechanizes §5 and refutes the objection that `(W,S)` fails to decrease on some rule. -/

/-- Fuel-weighted work. -/
def Wm : Expr → Nat
  | skip => 0
  | call _ => 1
  | tool _ => 1
  | seq a b => Wm a + Wm b
  | branch a b => Nat.max (Wm a) (Wm b)
  | loop n e => n * (Wm e + 1)
  | deleg _ e => Wm e

/-- Syntactic size. -/
def Sz : Expr → Nat
  | skip => 1
  | call _ => 1
  | tool _ => 1
  | seq a b => 1 + Sz a + Sz b
  | branch a b => 1 + Sz a + Sz b
  | loop _ e => 1 + Sz e
  | deleg _ e => 1 + Sz e

/-- Lexicographic order on `(Wm, Sz)`. -/
def Lex (e' e : Expr) : Prop := Wm e' < Wm e ∨ (Wm e' = Wm e ∧ Sz e' < Sz e)

/-- Every expression has size ≥ 1 (needed for the `loop 0 → skip` size drop). -/
theorem Sz_pos (e : Expr) : 0 < Sz e := by
  induction e <;> simp only [Sz] <;> omega

/-- **Every operational step strictly decreases `(Wm, Sz)` lexicographically.** Hence the relation is
    contained in the inverse image of `<ₗₑₓ` on `ℕ×ℕ` (well-founded), so the fragment is strongly
    normalizing — the §5 claim, mechanized. -/
theorem step_decreases {e g e' g'} (h : Step e g e' g') : Lex e' e := by
  induction h with
  | call => left; simp [Wm]
  | tool => left; simp [Wm]
  | @seqL a a' b g g' _ ih =>
      rcases ih with hW | ⟨hWe, hSe⟩
      · left; simp only [Wm]; omega
      · right; constructor
        · simp only [Wm]; omega
        · simp only [Sz]; omega
  | seqSkip => right; refine ⟨?_, ?_⟩ <;> simp [Wm, Sz]
  | @brL a b g => simp only [Lex, Wm, Sz, Nat.max_def]; split <;> omega
  | @brR a b g => simp only [Lex, Wm, Sz, Nat.max_def]; split <;> omega
  | @loopUnfold n e g =>
      left
      have key : (n + 1) * (Wm e + 1) = n * (Wm e + 1) + (Wm e + 1) := by rw [Nat.add_mul, Nat.one_mul]
      simp only [Wm]; omega
  | @loopZero e g => right; refine ⟨by simp [Wm], ?_⟩; simp only [Sz]; have := Sz_pos e; omega
  | deleg => right; refine ⟨?_, ?_⟩ <;> simp [Wm, Sz]

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
