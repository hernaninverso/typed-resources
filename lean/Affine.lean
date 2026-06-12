/-
  Affine handle layer — no-double-spend, mechanized (self-contained, no Mathlib).

  Companion to TypedResources.lean. Where the potential calculus bounds *how much* a workflow spends,
  this layer bounds *what* it spends: each handle (a context resource — a session, a lock, a
  sub-agent) is affine, usable at most once per execution. This is the property Khan enforces with the
  Rust borrow checker, here proved by machine.

  Central theorem (`no_double_spend`): a well-typed affine expression, run from any disjoint ledger,
  never records the same handle twice — the consumption ledger stays duplicate-free on every trace.

  Build:  lean Affine.lean   (exit 0, zero `sorry`)
-/

namespace Affine

/-- Handle expressions. `useH h` consumes handle `h`; `seqH` splits handles between the two sides;
    `branchH` shares them (only one branch runs); `delH` delegates a sub-computation. -/
inductive HE where
  | done   : HE
  | useH   : Nat → HE
  | seqH   : HE → HE → HE
  | branchH : HE → HE → HE
  | delH   : HE → HE
  deriving Repr

open HE

/-- Membership/disjointness/no-duplicate predicates, defined by hand to avoid Mathlib. -/
def disj (l₁ l₂ : List Nat) : Prop := ∀ x, x ∈ l₁ → x ∈ l₂ → False

def nodupL : List Nat → Prop
  | []      => True
  | h :: t  => h ∉ t ∧ nodupL t

/-- Handles an expression may consume (a superset of any single trace's consumption). -/
def handles : HE → List Nat
  | done        => []
  | useH h      => [h]
  | seqH a b    => handles a ++ handles b
  | branchH a b => handles a ++ handles b
  | delH e      => handles e

/-- Affine well-typedness: `seqH` requires the two sides' handle sets to be **disjoint** (no handle
    in both — that would allow a double-spend across the sequence); `branchH` does not (only one
    branch executes). -/
def linear : HE → Prop
  | done        => True
  | useH _      => True
  | seqH a b    => linear a ∧ linear b ∧ disj (handles a) (handles b)
  | branchH a b => linear a ∧ linear b
  | delH e      => linear e

/-- Instrumented semantics: `(expr, used-ledger) → (expr', used-ledger')`. Consuming `h` appends it
    to the ledger. -/
inductive HStep : HE → List Nat → HE → List Nat → Prop where
  | use     {h u}            : HStep (useH h) u done (h :: u)
  | seqL    {a a' b u u'} (h : HStep a u a' u') : HStep (seqH a b) u (seqH a' b) u'
  | seqDone {b u}            : HStep (seqH done b) u b u
  | brL     {a b u}          : HStep (branchH a b) u a u
  | brR     {a b u}          : HStep (branchH a b) u b u
  | del     {e u}            : HStep (delH e) u e u

/-- Reflexive–transitive closure. -/
inductive HSteps : HE → List Nat → HE → List Nat → Prop where
  | refl {e u}                                   : HSteps e u e u
  | tail {e u e' u' e'' u''} : HSteps e u e' u' → HStep e' u' e'' u'' → HSteps e u e'' u''

/-! ### Helper lemmas on the hand-rolled list predicates. -/

theorem disj_sub_left {l₁ l₁' l₂ : List Nat} (hsub : ∀ x, x ∈ l₁' → x ∈ l₁) (h : disj l₁ l₂) :
    disj l₁' l₂ := fun x hx₁ hx₂ => h x (hsub x hx₁) hx₂

theorem disj_append_left {a b l : List Nat} (ha : disj a l) (hb : disj b l) : disj (a ++ b) l := by
  intro x hx hxl
  rcases List.mem_append.mp hx with h | h
  · exact ha x h hxl
  · exact hb x h hxl

/-- A step's residual expression can only consume a subset of the original's handles. -/
theorem handles_step_sub {e u e' u'} (h : HStep e u e' u') : ∀ x, x ∈ handles e' → x ∈ handles e := by
  induction h with
  | use => intro x hx; simp [handles] at hx
  | @seqL a a' b u u' hstep ih =>
      intro x hx
      simp only [handles, List.mem_append] at hx ⊢
      rcases hx with h | h
      · exact Or.inl (ih x h)
      · exact Or.inr h
  | seqDone => intro x hx; simp only [handles, List.mem_append]; exact Or.inr hx
  | brL => intro x hx; simp only [handles, List.mem_append]; exact Or.inl hx
  | brR => intro x hx; simp only [handles, List.mem_append]; exact Or.inr hx
  | del => intro x hx; simpa [handles] using hx

/-- A step only appends handles of the current expression to the ledger. -/
theorem ledger_step_sub {e u e' u'} (h : HStep e u e' u') :
    ∀ x, x ∈ u' → x ∈ u ∨ x ∈ handles e := by
  induction h with
  | @use h u =>
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · exact Or.inr (by simp [handles, h])
      · exact Or.inl h
  | @seqL a a' b u u' hstep ih =>
      intro x hx
      rcases ih x hx with h | h
      · exact Or.inl h
      · exact Or.inr (by simp only [handles, List.mem_append]; exact Or.inl h)
  | seqDone => intro x hx; exact Or.inl hx
  | brL => intro x hx; exact Or.inl hx
  | brR => intro x hx; exact Or.inl hx
  | del => intro x hx; exact Or.inl hx

/-- The step invariant: the remaining expression is affine, its handles avoid the ledger, and the
    ledger is duplicate-free. -/
def Inv (e : HE) (u : List Nat) : Prop := linear e ∧ disj (handles e) u ∧ nodupL u

/-- **Preservation.** A single step preserves the invariant. -/
theorem hstep_preserves {e u e' u'} (hs : HStep e u e' u') : Inv e u → Inv e' u' := by
  induction hs with
  | @use h u =>
      intro inv; obtain ⟨_, dj, nd⟩ := inv
      have hnotin : h ∉ u := fun hc => dj h (by simp [handles]) hc
      exact ⟨trivial, by intro x hx _; simp [handles] at hx, ⟨hnotin, nd⟩⟩
  | @seqL a a' b u u' hstep ih =>
      intro inv; obtain ⟨⟨lina, linb, djab⟩, dj, nd⟩ := inv
      have dja : disj (handles a) u :=
        disj_sub_left (fun x hx => by simp only [handles, List.mem_append]; exact Or.inl hx) dj
      obtain ⟨lina', dja', nd'⟩ := ih ⟨lina, dja, nd⟩
      have djab' : disj (handles a') (handles b) := disj_sub_left (handles_step_sub hstep) djab
      refine ⟨⟨lina', linb, djab'⟩, disj_append_left dja' ?_, nd'⟩
      intro x hxb hxu'
      rcases ledger_step_sub hstep x hxu' with hxu | hxa
      · exact dj x (by simp only [handles, List.mem_append]; exact Or.inr hxb) hxu
      · exact djab x hxa hxb
  | @seqDone b u =>
      intro inv; obtain ⟨⟨_, linb, _⟩, dj, nd⟩ := inv
      exact ⟨linb, disj_sub_left (fun x hx => by simp only [handles, List.mem_append]; exact Or.inr hx) dj, nd⟩
  | @brL a b u =>
      intro inv; obtain ⟨⟨lina, _⟩, dj, nd⟩ := inv
      exact ⟨lina, disj_sub_left (fun x hx => by simp only [handles, List.mem_append]; exact Or.inl hx) dj, nd⟩
  | @brR a b u =>
      intro inv; obtain ⟨⟨_, linb⟩, dj, nd⟩ := inv
      exact ⟨linb, disj_sub_left (fun x hx => by simp only [handles, List.mem_append]; exact Or.inr hx) dj, nd⟩
  | @del e u =>
      intro inv; obtain ⟨lin, dj, nd⟩ := inv
      exact ⟨lin, by simpa [handles] using dj, nd⟩

/-- **No double-spend.** A well-typed affine expression, started from a ledger disjoint from its
    handles (e.g. the empty ledger), reaches no state whose consumption ledger has a duplicate:
    every handle is spent at most once, on every trace. -/
theorem no_double_spend {e u e' u'} (lin : linear e) (dj : disj (handles e) u) (nd : nodupL u)
    (run : HSteps e u e' u') : nodupL u' := by
  have inv : Inv e' u' := by
    induction run with
    | refl => exact ⟨lin, dj, nd⟩
    | tail _ hstep ih => exact hstep_preserves hstep ih
  exact inv.2.2

/-- Corollary: from the empty ledger, the consumed set is always duplicate-free. -/
theorem no_double_spend_empty {e e' u'} (lin : linear e) (run : HSteps e [] e' u') : nodupL u' :=
  no_double_spend lin (by intro x _ hx; cases hx) (by trivial) run

/-! ### Sanity: a sequence that reuses a handle is NOT linear; sharing across a branch IS. -/

-- seqH (useH 1) (useH 1): same handle on both sides of a sequence → would double-spend → not linear.
example : ¬ linear (seqH (useH 1) (useH 1)) := by
  intro h; obtain ⟨_, _, dj⟩ := h; exact dj 1 (by simp [handles]) (by simp [handles])

-- branchH (useH 1) (useH 1): same handle on both branches → fine (only one runs) → linear.
example : linear (branchH (useH 1) (useH 1)) := ⟨trivial, trivial⟩

-- seqH (useH 1) (useH 2): distinct handles → linear.
example : linear (seqH (useH 1) (useH 2)) :=
  ⟨trivial, trivial, by intro x h1 h2; simp [handles] at h1 h2; omega⟩

end Affine
