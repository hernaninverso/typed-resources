# A Potential-Based Calculus for Resource Bounds of LLM-Agent Workflows

**Hernán Inverso** · INVERSO HUB S.R.L. / CONICET
*Preprint, v2.7 — 12 June 2026*

> Relation to Khan [2606.04056] (stated up front to avoid any overclaim; **verified verbatim against
> the paper body**). Khan gives an empirical catalogue of 63 budget-overrun incidents and an **affine
> (Rust borrow-checker) mitigation**. Khan's proofs are **pen-and-paper — there is no proof-assistant
> mechanization** (the shipped artifact is "consistency evidence… not a proof"). Source-level
> ownership integrity is enforced by the Rust borrow checker; the **aggregate cost bound** (Σ ≤
> budget) is his **Proposition 1**, sound only under a provider-stratified estimator assumption (A1)
> and **validated empirically** (382 live-API sessions, zero overshoot), *not formally proved*;
> binary-level cap-soundness is his open **Conjecture 1**. **This paper contributes a machine-checked
> (Lean 4) proof of the aggregate cost bound for well-typed multi-step workflows** — amortized
> cost-accounting via a potential calculus, with multi-resource ⟨tokens, calls, $⟩ accounting, a
> compositional delegation rule, and a per-provider billing analysis. The proof technique is textbook
> AARA (and AARA has been mechanized before, for C); the novelty is the **first machine-checked
> instantiation to the agent-workflow / per-call-cap setting** plus the billing analysis — not a new
> proof method. It covers the aggregate accounting Khan establishes only via Proposition 1 + empirics.
> We **do not** address the binary-level gap, and
> we **mechanize the core no-double-spend property** of Khan's ownership as a separate affine Lean
> layer (§8, `no_double_spend`) — a faithful but deliberately thin affine discipline, *not* the full
> borrow apparatus (no explicit ownership context, move, or aliasing; those are roadmap). Both works
> leave the binary-level gap open.

---

## Abstract

Autonomous LLM-agent workflows consume tokens, tool calls and money in loops, and current safeguards
are *runtime* and *fallible*: a per-call cap exists, but the *project-level* budget only notifies
(OpenAI's project budget now warns rather than halts; Azure recommends "implement your own logic"),
and nothing bounds the **aggregate** across many capped calls — a single in-budget call can still
push a multi-step run over its total after it completes. We give a small **affine calculus with numeric
potential** over ⟨tokens, calls, $⟩, in the style of Hofmann–Jost Automatic Amortized Resource
Analysis (AARA), with seven constructs mirroring real frameworks and a delegation rule whose linear
potential split is adapted from resource-aware session types. Our **machine-checked (Lean 4)
cost-soundness theorem** states that a well-typed workflow's accumulated gas never exceeds its
declared potential at *every reachable configuration* — a safety invariant **proved without assuming
termination** (so it covers every finite prefix; the same argument would carry to non-terminating
extensions, an observation we do not mechanize) — **under the cap axiom** (per-call cost ≤ the declared cap), which §3.2 shows holds for some providers
and degrades for others. For the presented weak fragment we additionally prove progress and strong
normalization,
upgrading the guarantee from "spends ≤ P" to "*completes consuming* ≤ P tokens" (under the cap axiom
and a declared-window assumption on re-sent context) — a liveness-flavored property no kill-switch
provides. We additionally mechanize the
**affine no-double-spend property** (§8): a separate Lean development proving each context handle is
spent at most once on every trace (`no_double_spend`, axioms `[propext]`) — the core of the ownership
half Khan leaves to the borrow checker (a faithful but thin affine discipline, not a full borrow
system). We are explicit about scope: the metatheory is a deliberately minimal fragment (one resource,
integer costs, no concurrency, no expected-cost; the two layers compose but are not fused; the affine
layer has no explicit ownership context/move/aliasing); the rest is roadmap (§8). Finally we
contribute a **per-provider billing analysis** absent from prior work: the operational axiom that a
per-call cap is a hard *billing* ceiling on output (including hidden reasoning tokens) is
**parameter-specific, not provider-specific**. It holds for OpenAI Responses (`max_output_tokens`),
Azure/OpenAI reasoning (`max_completion_tokens` — reasoning tokens are inside `completion_tokens`),
and Anthropic standard (`budget_tokens < max_tokens`), but **degrades** for Anthropic
interleaved/adaptive thinking (budget may exceed `max_tokens`) and Gemini when `maxOutputTokens` is
set without pinning the separate `thinkingBudget` (§3.2, primary docs). Consequently we certify
in tokens/tool-calls (stable) and map to dollars only where the axiom holds.

## 1. Introduction

**The pain.** LLM-agent frameworks reduce a workflow to a small graph of model calls, tool calls,
branches, bounded loops and sub-agent delegations; each step costs tokens and money. Cost is
dominated by *re-sent context* (a stateless API re-sends the system prompt, tool definitions and the
whole conversation each step), which grows superlinearly. The problem is documented with primary
sources: Cursor issued public refunds for surprise agent bills (July 2025); **OpenAI eliminated its
hard budget cap** — a project budget now only notifies, "API requests will continue to be processed
without interruption" [OpenAI Help Center 9186755, accessed Jun 2026]; **Azure OpenAI provides no
hard spending cap** and officially recommends "implementing your own logic in your application to
halt requests" [Microsoft Q&A, accessed Jun 2026]. The `TALE` study [2412.18547] documents *token
elasticity*: under a tight budget the model emits *more* tokens, so prompting is not a ceiling.

**State of the art: runtime and fallible.** Observability vendors (Langfuse, Helicone, Portkey) sell
tracking and alerts, not enforcement; LiteLLM gives runtime per-key budgets for free. *Agent
Contracts* [2601.08815] specifies multi-dimensional resource bounds with conservation laws but
enforces them *at runtime* and admits a single call's cost is known only on completion. Khan
[2606.04056] is the first to bring *static* typing to bear: an affine (Rust borrow-checker)
mitigation whose source-level ownership integrity is enforced by the borrow checker (pen-and-paper,
not mechanized), with the aggregate cost bound given as Proposition 1 (conditional on estimator
assumption A1) and validated empirically, and binary-level soundness left open (Conjecture 1).

**This paper.** We provide an *operational* cost-soundness result via a potential-based calculus —
complementary to Khan's affine ownership discipline, and orthogonal to his open binary-level gap.

*Contributions.*
1. **A calculus** (§2): an affine workflow calculus with numeric potential over the semiring ℕᵏ
   (the metatheory is presented for k=1; the vector form is identical rule-by-rule), with seven
   constructs mirroring real frameworks, including a delegation rule whose linear potential split is
   adapted from resource-aware session types.
2. **A machine-checked (Lean 4) cost-soundness theorem** (§4): well-typed ⟹ gas ≤ declared
   potential at every *reachable configuration* (hence every finite prefix of any trace), *under the
   cap axiom* (§3), proved as a termination-free safety invariant. *Scope of the mechanization, stated
   plainly:* the Lean checks (i) `steps_sound` (the §4 bound), (ii) `hastype_iff_pot` (Lemma 0 — the
   §3 relational rules equal `pot`+`WellTyped`), and (iii) `step_decreases` (every step strictly
   decreases the §5 `(Wm,Sz)` measure); a companion file `lean/Affine.lean` checks (iv)
   `no_double_spend` (the §8 affine layer). It does **not** mechanize the final well-foundedness step
   of strong normalization, progress, the multi-resource vector, the fusion of the two layers into one
   syntax, or the §3.2 billing facts (these remain on paper). The credit-invariant
   technique itself is textbook AARA [Hofmann–Jost 2003], and AARA has been mechanized before (e.g.
   Carbonneaux–Hoffmann–Shao, certified resource bounds, 2015); **our novelty is not the proof technique but (i) its first
   machine-checked instantiation to the agent-workflow/per-call-cap setting and (ii) the billing
   analysis below**. Khan establishes the aggregate bound via Proposition 1 + empirics, unmechanized.
3. **A static-vs-runtime observation** (§5): the type rejects unbounded loops *ahead of time*,
   gives static compositional conservation for sequential/nested delegation, and — via strong
   normalization — certifies completion within budget. (No-double-spend is *not* part of this
   potential fragment; it is the separate affine handle layer of §8, also mechanized — `no_double_spend`.)
4. **A per-provider billing analysis** (§3.2): the operational axiom is *parameter-specific*. It holds
   for OpenAI Responses, Azure/OpenAI reasoning (`max_completion_tokens` bounds reasoning+output), and
   Anthropic standard; it degrades for Anthropic interleaved/adaptive thinking and for Gemini when
   `maxOutputTokens` is set without pinning `thinkingBudget`. We prescribe the correct cap parameter.

Scope is stated throughout: this is the minimal fragment. The affine no-double-spend layer is
mechanized separately (§8); concurrency (`par`/`retry`), the fusion of the two layers, multi-resource
metatheory, and expected-cost are roadmap (§8), not claimed.

### 1.1 Delta vs the closest prior work
| | Khan [2606.04056] | Resource-Bounded Type Theory [2512.06952] | **This paper** |
|---|---|---|---|
| mechanism | affine ownership (Rust borrow checker) | graded modalities, abstract resource lattice | **AARA numeric potential** |
| proofs | pen-and-paper (no proof assistant) | syntactic, recursion-free | **machine-checked (Lean 4)** |
| cost guarantee | Proposition 1 (cond. on A1) + empirical, not proved | syntactic cost-soundness, recursion-free | **operational cost-soundness, termination-free safety invariant** |
| resources | one budget | abstract lattice (time/mem/gas) | **⟨tokens, calls, $⟩ tuple** |
| delegation | — | — | **compositional split (session-type style)** |
| LLM coupling | dollar cap, no reasoning models | none (general resources) | **cap axiom + per-provider billing + framework map** |
| left open | binary-level soundness (Conjecture 1) | recursion | concurrency, full ownership (Γ/move/aliasing), layer fusion, expected-cost |

Our novelty is the *coupling* of amortized potential to the agent setting — the cap axiom, the
⟨tokens,calls,$⟩ tuple, compositional delegation, and the per-provider billing analysis — not the
potential method itself, which we reuse from AARA.

## 2. The calculus (presented fragment: one resource, integer costs, pure potential)

We present the fragment used in the metatheory: a single resource, integer costs, *pure numeric
potential* `p ∈ ℕ` (no affine context Γ). The vector form replaces ℕ by ℕᵏ and `≥`/`−` pointwise; all
rules are unchanged. The affine *handle* layer that yields no-double-spend is a separate calculus,
mechanized in its core form in §8; we keep this base case minimal so the theorem is checkable.

**Syntax.**
```
e ::= call(c) | tool(c)      -- model/tool call, declared cap c (the API token ceiling)
    | skip                   -- terminated workflow (value)
    | e₁ ; e₂                -- sequence
    | if e₁ e₂               -- branch (nondeterministic choice of a branch)
    | loop(n, e)             -- bounded loop, fuel n a literal. No fuel ⇒ no rule ⇒ does not type.
    | delegate(q, e)         -- sub-agent with transferred potential q (linear split of parent)
```
We write `e` *typable* iff `∃p,p′. p ⊢ e:⋄;p′`.

**Judgment.** `p ⊢ e : ⋄ ; p′`: with incoming potential `p` and residual `p′`.

**Typing rules.**
```
(T-Call)  p ≥ c                         (T-Skip) ──────────────
          ─────────────────────                  p ⊢ skip : ⋄ ; p
          p ⊢ call(c) : ⋄ ; p − c       (T-Tool) identical to T-Call.

(T-Seq)   p ⊢ e₁:⋄;p₁    p₁ ⊢ e₂:⋄;p₂   (T-If)  p ⊢ e₁:⋄;p₁    p ⊢ e₂:⋄;p₂   -- SAME input p
          ─────────────────────────             ─────────────────────────       to both branches
          p ⊢ e₁;e₂ : ⋄ ; p₂                    p ⊢ if e₁ e₂ : ⋄ ; min(p₁,p₂)

(T-Loop)  p_b ⊢ e:⋄;p_b′   b := p_b − p_b′   p ≥ n·b
          ──────────────────────────────────────────   -- fuel n literal. No fuel ⇒ no rule.
          p ⊢ loop(n,e) : ⋄ ; p − n·b

(T-Del)   q ⊢ e:⋄;q′    p ≥ q
          ────────────────────                  -- linear split: parent transfers q; conservative.
          p ⊢ delegate(q,e) : ⋄ ; p − q
```
**Every rule is *exact*: the residual is a deterministic function of the inputs, not a slack
inequality.** (T-Call residual `p−c`, T-Skip `p`, T-Seq `p₂`, T-If `min(p₁,p₂)`, T-Loop `p−n·b`,
T-Del `p−q`.) Exactness is what makes Lemma 0 hold; an earlier draft wrote T-Loop/T-Del with a free
residual `p′` in the premise (`p ≥ n·b + p′`), which would have made `p−p′` ambiguous (e.g.
`loop(0,e)` at `p=10` could derive any residual `0…10`) — that version is **wrong** and is corrected
here. In T-If both branches are typed from the **same** input `p`; the residual is `min(p₁,p₂)`
(worst residual) and the cost is `b_{if} = max(b_{e₁}, b_{e₂})` (worst branch). The cost `b` in
T-Loop is well-defined because, with exact rules, every typable `e` has a unique cost `b_e = pot(e)`
independent of the incoming potential (Lemma 0, now immediate by induction).

## 3. Instrumented semantics and the billing axiom

### 3.1 Small-step semantics with monotone gas
Configurations `⟨e, g⟩`, gas `g ∈ ℕ`. The **operational axiom** is the only place provider behavior
enters: `⟨call(c), g⟩ → ⟨skip, g+a⟩` and `⟨tool(c), g⟩ → ⟨skip, g+a⟩` for some `0 ≤ a ≤ c` — the API
enforces actual cost ≤ the declared cap (it truncates and bills at most `c`), *not* the model's
obedience (token elasticity shows the model does not obey budgets in the prompt). Remaining rules:
```
skip ; e → e        e₁;e₂ → e₁′;e₂  (if e₁→e₁′)      if e₁ e₂ → e_i
loop(n+1, e) → e ; loop(n, e)        loop(0, e) → skip        delegate(q, e) → e
```
Input cost (re-sent context, ~62% of the bill in practice) is folded into `c = W + cap_out`, with a
**declared window** annotation `W`.

> **Modeling assumption (not a derived lemma).** Setting `c = W + cap_out` with fuel-bounded loops is
> sound *iff* `W` is a worst-case bound on the re-sent context at *any* iteration (a full window).
> We treat `W` as a declared annotation, not inferred; under it, accumulated context never exceeds
> `W` per call, so per-call cost ≤ `c`. Loops with strictly growing context (the source of several
> incidents in Khan's catalogue) require `W` = the maximal-window cost, which is conservative
> (over-reservation). Inferring tighter `W` is future work.

The gas `g` is a global additive counter the semantics never reads — hence invariance under shifting
the initial gas (§4.4).

### 3.2 When the axiom holds: per-provider billing (sample, primary docs accessed June 2026)
The cap axiom requires the declared per-call parameter to be a hard *billing* ceiling on **billed
output tokens, including hidden reasoning/thinking tokens** (which every provider bills as output).
Whether a given parameter achieves this is **parameter-specific, not provider-specific** — the same
vendor both satisfies and breaks the axiom depending on which knob you set. Getting this right is a
prescriptive contribution prior work lacks. This is a *sample*, not a complete characterization, and
these APIs are volatile (each row cites the primary doc consulted):

| Provider / mode | Cap parameter | Bounds billed reasoning+output? | Cap axiom |
|---|---|---|---|
| **OpenAI** Responses | `max_output_tokens` | **yes** — `reasoning_tokens ⊆ output_tokens`, bounded | **holds** |
| **Azure/OpenAI** Chat, reasoning (o-series/GPT-5) | `max_completion_tokens` | **yes** — `reasoning_tokens ∈ completion_tokens_details`, capped¹ | **holds** |
| **Anthropic** standard | `max_tokens` (with `budget_tokens < max_tokens`) | **yes** — `max_tokens` caps total output (thinking+text)² | **holds** |
| **Anthropic** interleaved / adaptive thinking | `max_tokens` | **no** — "`budget_tokens` can exceed `max_tokens`… across all thinking blocks"² | **degrades** |
| **Google** Gemini 2.5/3, thinking on | `maxOutputTokens` *alone* | **no** — thinking billed as output but governed by a *separate* `thinkingBudget`/`thinkingLevel`³ | **degrades** unless `thinkingBudget` is also pinned |
| *any* reasoning model | legacy `max_tokens` | n/a — ignored/unsupported on o-series; must use the param above | **n/a (misconfig)** |

¹ Azure Foundry "reasoning models" doc: reasoning tokens are part of `completion_tokens` and
`max_completion_tokens` is the cap (Chat); `max_output_tokens` on Responses. ² Anthropic
extended-thinking doc: standard requires `budget_tokens < max_tokens` and `max_tokens` limits total
output; interleaved explicitly lifts this. ³ Gemini thinking doc: "response pricing is the sum of
output tokens and thinking tokens"; thinking is steered by `thinkingBudget` (2.5) / `thinkingLevel`
(3), distinct from `maxOutputTokens`. **The earlier intuition that *reasoning models* uniformly break
the cap is wrong** — OpenAI/Azure reasoning *do* bound billed reasoning via the completion cap; what
actually breaks it is (a) Anthropic interleaved/adaptive thinking, (b) Gemini with `maxOutputTokens`
set but `thinkingBudget` unpinned, and (c) using a legacy/wrong parameter. **Corollary:** certify in
**tokens/tool-calls** (stable) and map to dollars as a separate layer; the dollar bound is a
guarantee exactly where the correct per-call parameter is pinned, and degrades on the three failure
modes above.

## 4. Cost-soundness

We prove safety (the bound holds on every trace) and, for this fragment, progress + strong
normalization (§5).

*Two equivalent presentations.* The on-paper development below uses the **relational** judgment
`p ⊢ e:⋄;p′` (potential `p` in, residual `p′` out). The Lean mechanization uses the equivalent
**functional** presentation: a closed-form `pot : Expr → ℕ` (the minimal potential the rules consume)
plus a `WellTyped` side-condition for `delegate`; a budget `b` suffices iff `pot e ≤ b`, with residual
`b − pot e`. The two agree rule-by-rule — `pot` is exactly what the residual rules compute — so a
proof in either transfers; we mechanize the functional one because it makes the induction a direct
credit (`gas + pot`) invariant. Lemmas 0–2 below are the relational-side justification of that
equivalence.

### 4.1 Lemma 1 (weakening — raise the input)
If `p ⊢ e:⋄;p′` then `p+r ⊢ e:⋄;p′+r` for all `r ≥ 0`. *Proof:* induction on the derivation; each
rule passes the extra `r` from incoming to residual. ∎

### 4.2 Lemma 0 (exact characterization — relational ⟺ functional)
Define the closed-form potential `pot : Expr → ℕ` by `pot(skip)=0`, `pot(call c)=pot(tool c)=c`,
`pot(e₁;e₂)=pot(e₁)+pot(e₂)`, `pot(if e₁ e₂)=max(pot e₁,pot e₂)`, `pot(loop(n,e))=n·pot(e)`,
`pot(delegate(q,e))=q`. With the exact rules, the relational judgment is *completely determined* by it:
**`p ⊢ e:⋄;p′` iff `p ≥ pot(e)` and `p′ = p − pot(e)`** (for well-typed `e`; well-typedness is the
delegate side-condition `pot(child) ≤ q`).
*Proof by structural induction on `e`.* `call(c)`/`tool(c)`: derivable iff `p ≥ c = pot`, residual
`p − c`. `skip`: always, `pot=0`, residual `p`. `e₁;e₂`: by IH `p₁ = p − pot(e₁)` and (composing)
`p₂ = p₁ − pot(e₂) = p − (pot e₁ + pot e₂) = p − pot(e₁;e₂)`, needing `p ≥ pot e₁` and `p₁ ≥ pot e₂`,
i.e. `p ≥ pot(e₁;e₂)`. `if e₁ e₂`: same input `p`, residual `min(p−pot e₁, p−pot e₂) = p − max(…) =
p − pot(if)`, needing `p ≥ max = pot(if)`. `loop(n,e)`: `b = pot(e)` by IH (unique!), residual
`p − n·pot(e) = p − pot(loop)`, needing `p ≥ n·pot(e)`. `delegate(q,e)`: needs `q ≥ pot(e)` (child
types) and `p ≥ q = pot(delegate)`, residual `p − q`. ∎
**Corollary (cost is fungible):** `b_e := p − p′ = pot(e)`, independent of the incoming `p`. *This
lemma is now **machine-checked**: `lean/TypedResources.lean` defines the relational `HasType` and
proves `hastype_iff_pot : HasType p e p' ↔ (WellTyped e ∧ pot e ≤ p ∧ p' = p - pot e)` (the
`WellTyped` conjunct is essential — it carries the delegate side-condition `pot(child) ≤ q`; without
it the equivalence is false, e.g. `delegate(0, call(1))`), closing the
relational↔functional gap rather than leaving it on paper.*

### 4.3 Lemma 2 (one-step preservation, strengthened)
**If `p ⊢ e:⋄;p′` and `⟨e,g⟩ → ⟨e′,g′⟩` with `d := g′−g`, then (i) `d ≤ p` and (ii) ∃`r ≥ p′` with
`p−d ⊢ e′:⋄;r`.** The clause `r ≥ p′` lets T-Seq recompose. *Proof by cases (inversion):*
- `call(c)→skip, d=a≤c`: `p≥c, p′=p−c`; (i) `a≤c≤p`; (ii) `p−a⊢skip:⋄;p−a`, `r=p−a≥p−c=p′`.
- `skip;e₂→e₂, d=0`: `p₁=p`, `p⊢e₂:⋄;p′`; `r=p′`.
- `e₁;e₂, e₁→e₁′, d≥0`: T-Seq `p⊢e₁:⋄;p₁`, `p₁⊢e₂:⋄;p′`; IH on `e₁`: `d≤p`, `∃r₁≥p₁. p−d⊢e₁′:⋄;r₁`;
  Lemma 1 raises `e₂` from `p₁` to `r₁`: `r₁⊢e₂:⋄;p′+(r₁−p₁)`; T-Seq gives `r=p′+(r₁−p₁)≥p′`.
- `if e₁ e₂→e_i, d=0`: `p⊢e_i:⋄;p_i`, `p_i≥min(p₁,p₂)=p′`; `r=p_i`.
- `loop(n+1,e)→e;loop(n,e), d=0`: body cost `b=b_e`, `p≥(n+1)b+p′`; by Lemma 0 (normal form of body,
  raised to `p`, valid as `p≥(n+1)b≥b`) `p⊢e:⋄;p−b`; T-Loop (fuel n) `p−b⊢loop(n,e):⋄;p−(n+1)b`;
  T-Seq `p⊢e;loop(n,e):⋄;p−(n+1)b`; `r=p−(n+1)b≥p′`. `loop(0,e)→skip`: `r=p≥p′`.
- `delegate(q,e)→e, d=0`: `q⊢e:⋄;q′`, `p≥q+p′`; Lemma 1 raises child `q→p`: `p⊢e:⋄;p−q+q′`,
  `r=p−q+q′≥p−q≥p′`. ∎

*Note on the `delegate` case (the `q′` slack).* The static rule **T-Del debits the parent's residual
by the full `q`** — the parent declares the transfer lost irrevocably (the linear split). The
operational step, however, **inlines `e` into the parent's single global gas counter** (there is no
separate child process to "burn" its unused budget), so when we recompose, the child's unspent
potential `q′` is still accounted. That is why `r = p−q+q′ ≥ p−q`. The invariant only needs `r ≥ p′`,
so the `q′` slack is sound *over*-accounting, never double-spend. The Lean model is strictly more
conservative: `pot (delegate q e) = q` unconditionally, never crediting `q′` back — so the mechanized
bound is `q`, exactly the static debit, with no reliance on the recomposition slack.

### 4.4 Theorem (gas bound — a safety invariant on every reachable configuration)
**For all `g₀`: if `p ⊢ e:⋄;_` and `⟨e,g₀⟩ →* ⟨e″,g⟩`, then `g−g₀ ≤ p`** (with `g₀=0`: `g ≤ p`).
*Proof* by induction on the number `m` of steps. `m=0`: `0≤p`. `m→m+1`: `⟨e,g₀⟩→⟨e₁,g₁⟩→*⟨e″,g⟩`;
by Lemma 2, `d₁=g₁−g₀≤p` and `p−d₁⊢e₁:⋄;_`; by IH on the `m`-step subtrace (incoming `p−d₁`),
`g−g₁≤p−d₁`; summing, `g−g₀≤d₁+(p−d₁)=p`. ∎

This is a **safety property**: it holds at every reachable configuration `⟨e″,g⟩` and **its proof
never appeals to termination** (it is the transitive lift of the per-step credit invariant
`g + Φ` non-increasing, Lemma 2). The weak fragment is in fact strongly normalizing (§5), so no
divergent trace exists *here*, and the Lean theorem quantifies over the (necessarily finite) `Steps`
reachable from `⟨e,0⟩`. The payoff of proving a *termination-free* invariant — rather than deriving
the bound as a corollary of termination — is methodological: the **same `g + Φ` argument would carry
over** to an extension with genuine non-termination (e.g. fuel-free recursion), since it never uses
strong normalization. We flag that this carry-over is an *observation about the technique*, **not a
mechanized claim**: the Lean covers exactly this fragment. The theorem `steps_sound`
(`Steps e 0 e′ g′ → WellTyped e → g′ ≤ pot e`) is the safety statement, quantified over all reachable
`⟨e′,g′⟩`.

## 5. Progress, termination, and what the type adds over a runtime tracker

**Measure for termination.** Use the lexicographic order on pairs `(W, S)`, where `W` is fuel-weighted
work and `S` is syntactic size. Define `W(skip)=0`, `W(call(c))=W(tool(c))=1`, `W(e₁;e₂)=W(e₁)+W(e₂)`,
`W(if e₁ e₂)=max(W(e₁),W(e₂))`, `W(delegate(q,e))=W(e)`, and `W(loop(n,e))=n·(W(e)+1)` (the `+1` per
iteration is the unrolling overhead). `S(e)` is the number of AST nodes (always `≥ 1`). **Lemma (decrease) — mechanized as `step_decreases`
in Lean.** Every operational rule strictly decreases `(W,S)` lexicographically; the Lean proof checks
all nine rule cases, so the informal reasoning below is backed by the machine, not just prose:
- `call(c)→skip`: `W` drops `1→0`.
- `loop(n+1,e)→e;loop(n,e)`: `W` drops by **exactly 1** — LHS `W=(n+1)(W(e)+1)`, RHS
  `W=W(e)+n(W(e)+1)`, so LHS−RHS `= 1`. The unfold **duplicates `e` syntactically, so `S` grows
  here**; this is harmless because `W` (the higher-priority component) strictly decreases — standard
  lexicographic pattern, where `S` only governs the `W`-constant steps.
- The `W`-non-increasing steps — `skip;e→e`, `if e₁ e₂→e_i` (where `W(e_i) ≤ max(W(e₁),W(e₂)) = W(if)`,
  so `W` drops or stays equal; if equal, `S` drops), `loop(0,e)→skip`, `delegate(q,e)→e` — each
  strictly drop `S` when `W` is unchanged (they remove an AST node; `W(delegate(q,e))=W(e)` makes the
  delegate step `W`-equal, `S`-down).
- `e₁;e₂→e₁′;e₂` decreases `(W,S)` by IH on `e₁` (lifted through `W(e₁;e₂)=W(e₁)+W(e₂)`).

Since `<ₗₑₓ` on ℕ×ℕ is well-founded, the fragment is strongly normalizing. ∎ (`step_decreases`
mechanizes the per-rule decrease; the well-foundedness step is standard.) **Progress.** Every typable
`e≠skip` steps (by inversion:
call/tool/if/loop/delegate have a rule; `e₁;e₂` reduces `e₁` or consumes a leading `skip`). ∎

**What is and isn't mechanized.** Machine-checked in `lean/TypedResources.lean`: (1) the §4
cost-soundness safety invariant `steps_sound`; (2) **Lemma 0** — the relational↔functional equivalence
`hastype_iff_pot : HasType p e p' ↔ (WellTyped e ∧ pot e ≤ p ∧ p' = p − pot e)`, so the bridge from
the §3 typing rules to `pot` is no longer on paper; (3) **the §5 termination measure**
`step_decreases : Step e g e' g' → Lex e' e`, i.e. every operational step strictly decreases the
lexicographic `(Wm, Sz)` — the load-bearing content of strong normalization. `steps_sound` and
`hastype_iff_pot` use only `[propext, Quot.sound]` (constructive); `step_decreases` additionally uses
`Classical.choice`; the affine layer's `no_double_spend` (in `lean/Affine.lean`) uses `[propext]`.
Still **pen-and-paper**: the final step from `step_decreases` to "no infinite
reduction" (standard well-foundedness of `<ₗₑₓ` on ℕ×ℕ), progress, the multi-resource vector, the
fusion of the two layers, and the §3.2 billing facts. So the "*completes* within budget" upgrade now rests on a
mechanized measure-decrease plus a standard well-foundedness step; the headline *mechanized* guarantee
remains the safety bound "never *spends* more than the declared potential."

A runtime budget with a kill-switch gives safety only — it aborts at meter `B`, after spending `B`,
possibly mid-task. The type gives more, *ahead of time*:
- **(a)** *Ex-ante rejection of unbounded loops.* A `loop` without a fuel literal does not type; the
  canonical runaway is a type error at check time, not a runtime abort after overspending. (Light —
  syntactic — but a tracker cannot reject it ex-ante.)
- **(b)** *Static compositional conservation for sequential/nested delegation.* T-Del gives `Σ qᵢ ≤ p`
  before execution. *Scope:* sequential/nested only; the concurrent tree needs `par` + interleaving
  (§8).
- **(c)** *Completes consuming ≤ P tokens.* By strong normalization + progress + the gas bound, a
  well-typed workflow with potential `p` **terminates and consumes ≤ p** — "I will finish within P
  tokens." A tracker gives only "aborts at B": you pay `B` for a half-finished result. **Two
  conditions, both explicit:** (i) the cap axiom holds (§3.2) — else per-call cost may exceed `c`;
  (ii) the declared window `W` upper-bounds the re-sent context at every iteration (§3.1) — if `W`
  underestimates real context (prompt caching, large tool outputs, retries that regrow context), the
  token bound breaks though the calculus stays sound. The dollar version additionally needs the cap
  axiom's billing form. We therefore state the guarantee in tokens/tool-calls, conditional on (i)–(ii).

*What the fragment does not give.* No-double-spend of a context resource is not a consequence of the
pure-potential rules; it needs affine handles with linear split. That orthogonal property is exactly
what Khan's affine layer targets — and what our separate `lean/Affine.lean` development mechanizes in
its core form (§8, `no_double_spend`).

## 6. Mapping to frameworks: the checker is a linter, not a new DSL

| Construct | LangGraph | OpenAI Agents SDK | CrewAI | Temporal |
|---|---|---|---|---|
| `call(c)` | model cap | `max_output_tokens` | model cap | activity |
| `loop(n,·)` | `recursion_limit` | `max_turns` | `max_iter` | retry policy |
| `delegate(q,·)` | `Send`/subgraph | handoff | hierarchical | child workflow |
| `par(·)` †roadmap | parallel `Send` | parallel tools | — | parallel children |

The seven constructs type annotations developers already write; a checker enters as a *linter over
existing config*, not a language to adopt. (`par` is roadmap, marked †; it is not in the calculus.)

## 7. Related work

- **Khan [2606.04056]** (Jun 2026): 63-incident catalogue + affine (Rust) mitigation; source-level
  ownership enforced by the borrow checker (**pen-and-paper, not mechanized**); the aggregate cost
  bound is Proposition 1 (conditional on estimator assumption A1) + empirical validation (382 live
  sessions), not a proof; **binary-level** soundness left open (Conjecture 1). *We give a
  machine-checked, operational cost-soundness via potential; we do not touch the binary gap, and our
  affine layer (§8) mechanizes the core of his no-double-spend (thin discipline; full ownership is roadmap).*
- **Graded / cost-aware type systems.** Resource-Bounded Type Theory [2512.06952] (Dec 2025) proves
  syntactic cost-soundness for a recursion-free fragment over an abstract resource lattice; its
  dependent MLTT variant [2601.10772]; `calf` [2107.04663]; RelCost;
  Granule. *None is agent/token-specific. Our contribution is the LLM coupling — the cap axiom, the
  ⟨tokens,calls,$⟩ tuple, per-provider billing, framework map — not the potential/grading method.*
- **AARA** (Hofmann–Jost POPL 2003; "Two Decades of AARA", MSCS 2022): the potential method; soundness
  formulations valid for non-terminating executions. *Our fragment is the degenerate linear case.*
- **Resource-aware session types** (Das–Hoffmann–Pfenning, LICS 2018; digital contracts 2019):
  potential over message-passing; potential↔gas. *Our delegation split adapts this to sub-agents.*
- **Agent Contracts [2601.08815]** (AAMAS 2026): runtime multi-dimensional bounds with conservation
  laws; admits a single call can exceed the budget. *Our conservation corollary is its static counterpart.*
- **The LLMbda calculus [2602.20064]** (Gordon, Sands, Feb 2026): λ-calculus for agentic programming
  with information-flow control. *Complementary (info-flow vs resources); LLMbda has no potential/
  grading, so budget-typing is not a free extension of it — integrating the two is roadmap (§8).*

## 8. The affine handle layer (no-double-spend), and roadmap

The potential calculus bounds *how much* a workflow spends. Its orthogonal half — *what* it spends,
i.e. that each **context resource** (a session, a lock, a sub-agent handle) is used at most once — is
the property at the heart of the ownership discipline Khan enforces with the Rust borrow checker. We
mechanize **that essential property** (affine no-double-spend) as a self-contained layer
(`lean/Affine.lean`). *We are precise about what this is and is not:* it is a syntactic affine
discipline over named handles proving the consumption ledger stays duplicate-free; it is **not** the
full borrow apparatus — there is no explicit ownership context `Γ` with membership checks, no
move/borrow distinction, no aliasing or handle allocation. Those are the genuine remaining content of
"mechanizing Khan's ownership" and are roadmap, not claimed here.

A handle expression consumes named handles; `seqH` **splits** the available handles between its two
sides (a handle may appear in at most one), while `branchH` **shares** them (only one branch runs).
Affine well-typedness `linear` enforces the split. The instrumented semantics records consumed
handles in a ledger, and the central theorem is

> `no_double_spend : linear e → disj (handles e) u → nodupL u → HSteps e u e′ u′ → nodupL u′`

— a well-typed affine expression, run from a fresh ledger, **never records the same handle twice on
any trace**. `#print axioms no_double_spend` reports `[propext]` only (constructive). The proof is a
preservation invariant: each step keeps the remaining expression affine, its handles disjoint from
the ledger, and the ledger duplicate-free.

Together with §4, this mechanizes the *core* of both source-level guarantees: the aggregate cost
bound (the half Khan leaves to Proposition 1 + empirics) *and* the affine no-double-spend property
(the core of the half he leaves to the borrow checker). The aggregate-cost mechanization we believe
is the first; the affine layer is a faithful but deliberately thin discipline, not a full borrow
system. The two layers compose as a product judgment `p; Γ ⊢ e ⊣ p′; Γ′` (numeric potential `p` ×
affine context `Γ`), each component independent.

**Still roadmap:** promoting the affine layer to a **full ownership type system** — explicit context
`Γ ⊢ e ⊣ Γ′` with membership checks on `useH`, move/borrow distinction, aliasing and handle allocation
(this is the substance of Khan's borrow discipline that the thin layer here does not capture); unifying
the two layers in a *single* `Expr` (here they are separate calculi that compose, not one fused
syntax); **multi-resource metatheory** over ℕᵏ (here k=1; rules are pointwise-identical, proofs should
be restated for the tuple); **`par`/`retry`** with an interleaving semantics; **expected-cost** via
probabilistic AARA (Ngo–Carbonneaux–Hoffmann, PLDI 2018), with its subtleties (optional stopping,
supermartingales); **inferred windows `W`**; and **integration with LLMbda** for a combined
information-flow + resource type system.

---

*Artifacts. (1) A **Lean 4 mechanization** (`lean/TypedResources.lean`, self-contained, no Mathlib,
Lean v4.30.0) of the calculus: the §4 theorem*
`steps_sound : Steps e 0 e′ g′ → WellTyped e → g′ ≤ pot e`
*(a well-typed workflow from zero gas spends `g′ ≤ pot e` at every reachable configuration — every
finite prefix of any trace — where `Step.call`/`Step.tool` encode the cap axiom `a ≤ c`; proved via
the single-step credit invariant `step_sound` and its transitive lift `steps_credit`), plus the
Lemma 0 equivalence `hastype_iff_pot` and the §5 measure decrease `step_decreases`.*
`#print axioms steps_sound` *reports only `[propext, Quot.sound]` — Lean's two foundational kernel
axioms; no `sorryAx`, no `Classical.choice`, so the proof is constructive. This is the
machine-checked claim. (2) The **affine layer** (`lean/Affine.lean`): `no_double_spend`, axioms
`[propext]` (§8). (3) A Python sanity harness (`check.py`) on a fixed 5-program battery, which
(i) confirms the no-fuel runaway loop does not type, (ii) confirms sequential delegation
conservation, and (iii) reports zero `g ≤ p` violations over random cost assignments. Note (ii)–(iii)
only test that the executable rules agree with the paper: the generator enforces `a ≤ c` by
construction, so the harness **cannot** witness a cap violation — it validates rule/code
consistency, not soundness under an adversarial provider. Soundness is the Lean theorem, not an
empirical claim.*
