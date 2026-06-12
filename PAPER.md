# A Potential-Based Calculus for Resource Bounds of LLM-Agent Workflows

**Hernán Inverso** · INVERSO HUB S.R.L. / CONICET
*Preprint, draft v1 — 12 June 2026*

> Relation to Khan [2606.04056] (stated up front to avoid any overclaim): Khan gives an empirical
> catalogue of 63 budget-overrun incidents and an **affine (Rust borrow-checker) mitigation** whose
> *source-level* cap integrity is enforced by the borrow checker and is **already mechanized** (Coq
> artifact). Khan explicitly leaves open only **binary-level** cap-soundness ("on the running binary
> is left open") — the source→binary gap. **This paper does not address that binary-level gap.** We
> contribute a different, complementary object: a *potential-based* calculus with an **operational
> cost-soundness** theorem (the gas consumed by a well-typed workflow is bounded by its declared
> potential), with multi-resource ⟨tokens, calls, $⟩ accounting, a compositional delegation rule, and
> a per-provider billing analysis. Where Khan's affine discipline forbids double-spend of a budget
> *handle*, our potential discipline bounds aggregate *cost*; the two are orthogonal and combine
> (§8).

---

## Abstract

Autonomous LLM-agent workflows consume tokens, tool calls and money in loops, and current safeguards
are *runtime* and *fallible*: provider budget caps that only notify (OpenAI removed its hard cap;
Azure recommends "implement your own logic"), and behavioral contracts that admit a single expensive
call can exceed the budget after it completes. We give a small **affine calculus with numeric
potential** over ⟨tokens, calls, $⟩, in the style of Hofmann–Jost Automatic Amortized Resource
Analysis (AARA), with seven constructs mirroring real frameworks and a delegation rule whose linear
potential split is adapted from resource-aware session types. Our **cost-soundness theorem** states
that a well-typed workflow's accumulated gas never exceeds its declared potential, on *every* trace
including partial and divergent ones. For the presented weak fragment we additionally prove progress
and strong normalization, upgrading the guarantee from "spends ≤ P" to "*completes consuming* ≤ P
tokens" — a liveness-flavored property no kill-switch provides. We are explicit about scope: this is
a deliberately minimal fragment (one resource in the metatheory, integer costs, no concurrency, no
affine no-double-spend layer, no expected-cost); the full development is roadmap (§8). Finally we
contribute a **per-provider billing analysis** absent from prior work: the operational axiom that a
per-call cap is a hard *billing* ceiling holds for Anthropic standard/adaptive thinking, the OpenAI
Responses API and Gemini, but **degrades** for Azure reasoning models and Anthropic interleaved
thinking, where hidden reasoning tokens are billed beyond the declared cap. Consequently we certify
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
mitigation whose source-level cap integrity is enforced and mechanized, leaving only binary-level
soundness open.

**This paper.** We provide an *operational* cost-soundness result via a potential-based calculus —
complementary to Khan's affine ownership discipline, and orthogonal to his open binary-level gap.

*Contributions.*
1. **A calculus** (§2): an affine workflow calculus with numeric potential over the semiring ℕᵏ
   (the metatheory is presented for k=1; the vector form is identical rule-by-rule), with seven
   constructs mirroring real frameworks, including a delegation rule whose linear potential split is
   adapted from resource-aware session types.
2. **A cost-soundness theorem** (§4): well-typed ⟹ gas ≤ declared potential, on every trace
   including partial and divergent ones — the cap holds by construction. Plus progress and strong
   normalization for the fragment (§5), giving the "completes within budget" guarantee.
3. **A static-vs-runtime observation** (§5): the type rejects unbounded loops *ahead of time*,
   gives static compositional conservation for sequential/nested delegation, and — via strong
   normalization — certifies completion within budget. (We mark explicitly what the fragment does
   *not* give: no-double-spend belongs to the affine handle layer, i.e. Khan's discipline, §8.)
4. **A per-provider billing analysis** (§3.2): the operational axiom holds for Anthropic
   standard/adaptive, OpenAI Responses and Gemini, and degrades for Azure reasoning and Anthropic
   interleaved thinking. We prescribe the correct cap parameter per provider.

Scope is stated throughout: this is the minimal fragment. Concurrency (`par`/`retry`), the affine
no-double-spend layer, multi-resource metatheory, and expected-cost are roadmap (§8), not claimed.

### 1.1 Delta vs the closest prior work
| | Khan [2606.04056] | Resource-Bounded Type Theory [2512.06952] | **This paper** |
|---|---|---|---|
| mechanism | affine ownership (Rust borrow checker) | graded modalities, abstract resource lattice | **AARA numeric potential** |
| guarantee | no-double-spend of a handle (source-level, mechanized) | cost-soundness, recursion-free | **operational cost-soundness incl. divergent traces** |
| resources | one budget | abstract lattice (time/mem/gas) | **⟨tokens, calls, $⟩ tuple** |
| delegation | — | — | **compositional split (session-type style)** |
| LLM coupling | dollar cap, no reasoning models | mentions "time-bounded agents", no API model | **cap axiom + per-provider billing + framework map** |
| left open | binary-level soundness | recursion | concurrency, affine layer, expected-cost |

Our novelty is the *coupling* of amortized potential to the agent setting — the cap axiom, the
⟨tokens,calls,$⟩ tuple, compositional delegation, and the per-provider billing analysis — not the
potential method itself, which we reuse from AARA.

## 2. The calculus (presented fragment: one resource, integer costs, pure potential)

We present the fragment used in the metatheory: a single resource, integer costs, *pure numeric
potential* `p ∈ ℕ` (no affine context Γ). The vector form replaces ℕ by ℕᵏ and `≥`/`−` pointwise; all
rules are unchanged. The affine *handle* layer that yields no-double-spend (Khan's ownership,
formalized) is an extension (§8); we keep the base case minimal so the theorem is checkable.

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

(T-Loop)  p_b ⊢ e:⋄;p_b′   b := p_b − p_b′   p ≥ n·b + p′
          ───────────────────────────────────────────────   -- fuel n literal. No fuel ⇒ no rule.
          p ⊢ loop(n,e) : ⋄ ; p′

(T-Del)   q ⊢ e:⋄;q′    p ≥ q + p′
          ────────────────────────              -- linear split: parent transfers q; conservative.
          p ⊢ delegate(q,e) : ⋄ ; p − q
```
In T-If both branches are typed from the **same** input `p`; the residual is `min(p₁,p₂)` (worst
residual) and, by Lemma 0, the cost is `b_{if} = max(b_{e₁}, b_{e₂})` (worst branch). The cost `b`
in T-Loop is well-defined: Lemma 0(a) shows every typable `e` has a unique cost `b_e` independent of
the incoming potential.

## 3. Instrumented semantics and the billing axiom

### 3.1 Small-step semantics with monotone gas
Configurations `⟨e, g⟩`, gas `g ∈ ℕ`. The **operational axiom** is the only place provider behavior
enters: `⟨call(c), g⟩ → ⟨skip, g+a⟩` for some `0 ≤ a ≤ c` — the API enforces actual cost ≤ the
declared cap (it truncates and bills at most `c`), *not* the model's obedience (token elasticity
shows the model does not obey budgets in the prompt). Remaining rules:
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

### 3.2 When the axiom holds: per-provider billing (sample, accessed June 2026)
The cap axiom requires the declared per-call parameter to be a hard *billing* ceiling, **including
hidden reasoning tokens**. This holds unevenly; getting it right is a contribution prior work lacks.
This is a *sample*, not a complete characterization, and these APIs are volatile (dated access):

| Provider / mode | Cap parameter | Bounds reasoning tokens? | Cap axiom |
|---|---|---|---|
| **Anthropic** standard (`budget_tokens`†) / adaptive (effort, Opus 4.7+) | `max_tokens` | yes — thinking ⊆ `max_tokens`, billed as output | **holds** |
| **Anthropic** interleaved thinking (beta) | `max_tokens` | **no** — budget may exceed `max_tokens` across blocks | **degrades** |
| **OpenAI** Responses API | `max_output_tokens` | yes — caps reasoning+output combined | **holds** |
| **Google** Gemini 2.5/3 | `maxOutputTokens` | yes — combined thinking+output budget | **holds** |
| **Azure OpenAI** reasoning (o-series/GPT-5) | `max_completion_tokens` | **no** — caps visible output only; reasoning billed unbounded | **degrades** |

† `budget_tokens` is deprecated for the newest Claude models in favor of adaptive/effort, but the
axiom persists (thinking still counts within `max_tokens`). AWS Bedrock replicates Anthropic's
behavior. **Corollary:** certify in **tokens/tool-calls** (stable) and map to dollars as a separate
layer parameterized by the provider's billing semantics; the dollar bound is a guarantee only where
the axiom holds (Anthropic standard/adaptive, OpenAI Responses, Gemini), degrading to a
visible-output bound on Azure-reasoning / Anthropic-interleaved.

## 4. Cost-soundness

We prove safety (the bound holds on every trace) and, for this fragment, progress + strong
normalization (§5).

### 4.1 Lemma 1 (weakening — raise the input)
If `p ⊢ e:⋄;p′` then `p+r ⊢ e:⋄;p′+r` for all `r ≥ 0`. *Proof:* induction on the derivation; each
rule passes the extra `r` from incoming to residual. ∎

### 4.2 Lemma 0 (cost invariance + normal form)
**(a)** For every typable `e`, `p − p′` is the same in every typing `p ⊢ e:⋄;p′`; call it `b_e`.
**(b)** `b_e ⊢ e:⋄;0` is derivable. **Cor.:** for all `x ≥ b_e`, `x ⊢ e:⋄;x − b_e`.
*Proof of (a),(b) by structural induction.* `call(c)`: `b=c`; `c⊢call(c):⋄;0`. `skip`: `b=0`.
`e₁;e₂`: `p−p₂=(p−p₁)+(p₁−p₂)=b₁+b₂`; normal form `b₁+b₂⊢e₁:⋄;b₂` (Lemma 1 on `b₁⊢e₁:⋄;0`),
`b₂⊢e₂:⋄;0` (IH), T-Seq. `if e₁ e₂`: `p−min(p₁,p₂)=max(p−p₁,p−p₂)=max(b₁,b₂)`; normal form via Lemma 1
then T-If with residual `min=0`. `loop(n,e)`: `b=n·b_body`; `n·b_body⊢loop(n,e):⋄;0`. `delegate(q,e)`:
`b=q`; `q⊢delegate(q,e):⋄;0`. ∎
*(`b_e` is fungible — independent of input. Lemma 1 cannot* lower *a derivation; one re-derives from
the normal form `b_e` and raises, which is what the loop case of Lemma 2 needs.)*

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

### 4.4 Theorem (gas bound — safety, every trace incl. partial/divergent)
**For all `g₀`: if `p ⊢ e:⋄;_` and `⟨e,g₀⟩ →* ⟨e″,g⟩`, then `g−g₀ ≤ p`** (with `g₀=0`: `g ≤ p`).
*Proof* by induction on the number `m` of steps. `m=0`: `0≤p`. `m→m+1`: `⟨e,g₀⟩→⟨e₁,g₁⟩→*⟨e″,g⟩`;
by Lemma 2, `d₁=g₁−g₀≤p` and `p−d₁⊢e₁:⋄;_`; by IH on the `m`-step subtrace (incoming `p−d₁`),
`g−g₁≤p−d₁`; summing, `g−g₀≤d₁+(p−d₁)=p`. ∎

## 5. Progress, termination, and what the type adds over a runtime tracker

**Measure for termination.** Use the lexicographic order on pairs `(W, S)`, where `W` is fuel-weighted
work and `S` is syntactic size. Define `W(skip)=0`, `W(call(c))=W(tool(c))=1`, `W(e₁;e₂)=W(e₁)+W(e₂)`,
`W(if e₁ e₂)=max(W(e₁),W(e₂))`, `W(delegate(q,e))=W(e)`, and `W(loop(n,e))=n·(W(e)+1)` (the `+1` per
iteration is the unrolling overhead). `S(e)` is the number of AST nodes. **Lemma (decrease).** Every
operational rule strictly decreases `(W,S)` lexicographically:
- `call(c)→skip`: `W` drops `1→0`.
- `loop(n+1,e)→e;loop(n,e)`: `W` drops by **exactly 1** — LHS `W=(n+1)(W(e)+1)`, RHS
  `W=W(e)+n(W(e)+1)`, so LHS−RHS `= 1`. (This is the case the unrolling makes subtle: `S` grows here,
  but `W` strictly decreases, so the pair decreases.)
- The steps that leave `W` unchanged — `skip;e→e`, `if e₁ e₂→e_i` (when the taken branch's `W` equals
  the max), `loop(0,e)→skip`, `delegate(q,e)→e` — each strictly drop `S` (they remove an AST node).
- `e₁;e₂→e₁′;e₂` decreases `(W,S)` by IH on `e₁` (lifted through `W(e₁;e₂)=W(e₁)+W(e₂)`).

So the fragment is strongly normalizing. ∎ **Progress.** Every typable `e≠skip` steps (by inversion:
call/tool/if/loop/delegate have a rule; `e₁;e₂` reduces `e₁` or consumes a leading `skip`). ∎

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
  tokens." A tracker gives only "aborts at B": you pay `B` for a half-finished result. **We state
  this in tokens/tool-calls; the dollar version holds only where the §3.2 cap axiom holds.**

*What the fragment does not give.* No-double-spend of a context resource is not a consequence of the
pure-potential rules; it needs affine handles with linear context split (Khan's ownership,
formalized; §8). We flag this to avoid over-claiming: it is exactly the part Khan already mechanizes.

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
  cap integrity enforced by the borrow checker and mechanized; **binary-level** soundness left open.
  *We give an orthogonal, operational cost-soundness via potential; we do not touch the binary gap,
  and our affine layer (§8) recovers his no-double-spend.*
- **Graded / cost-aware type systems.** Resource-Bounded Type Theory [2512.06952] (Dec 2025) proves
  cost-soundness for a recursion-free fragment over an abstract resource lattice (and mentions
  time-bounded agents); its dependent MLTT variant [2601.10772]; `calf` [2107.04663]; RelCost;
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

## 8. Limitations and roadmap

This is the minimal fragment, deliberately small so the metatheory is checkable. The full development
adds: the **affine handle layer** (linear context split ⟹ no-double-spend, formalizing Khan's
ownership and recovering it inside this framework); **multi-resource metatheory** over ℕᵏ (here
presented for k=1; the rules are pointwise-identical but the proofs should be stated for the tuple);
**`par`/`retry` with an interleaving semantics** (conservation over concurrent trees); **expected-cost**
via probabilistic AARA (Ngo–Carbonneaux–Hoffmann, PLDI 2018) to tighten the worst-case
over-reservation, with its own subtleties (optional stopping, supermartingales); **inferred windows
`W`** instead of declared; and **integration with LLMbda** for a combined information-flow + resource
type system.

---

*Artifact (`check.py`): a mechanization of the typing rules and instrumented semantics on a fixed
5-program battery, which (i) confirms the runaway loop without fuel does not type, (ii) confirms
sequential delegation conservation, and (iii) reports zero `g ≤ p` violations over random cost
assignments (`a ≤ c`, seed 0). The artifact validates that the mechanization agrees with the
paper rules; soundness itself is the theorem of §4, not an empirical claim.*
