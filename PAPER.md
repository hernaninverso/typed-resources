# Typed Resource Bounds for Agent Workflows: Resolving the Base Case of Khan's Conjecture

**Hernán Inverso** · INVERSO HUB S.R.L. / CONICET
*Preprint, draft v0 — 12 June 2026*

---

## Abstract

Autonomous LLM-agent workflows consume tokens, tool calls and money in loops, and current
safeguards are *runtime* and *fallible*: provider budget caps that only notify (OpenAI removed its
hard cap; Azure recommends "implement your own logic"), and behavioral contracts that admit a single
expensive call can exceed the budget after it completes. Ten days before this writing, Khan
[2606.04056] catalogued 63 budget-overrun incidents and proposed an affine-typed (Rust borrow
checker) mitigation, but left soundness — "well-typed implies the declared cap is respected" — as an
**open conjecture (Conjecture 1)**, with no formal calculus. We give the calculus and prove the
conjecture's **base case**: an affine calculus with numeric potential ⟨tokens, calls, $⟩ in the
style of Hofmann–Jost Automatic Amortized Resource Analysis, with a delegation rule from
resource-aware session types (Das–Hoffmann–Pfenning). Our soundness theorem states that a well-typed
workflow's gas never exceeds its declared potential, on *every* trace including partial and divergent
ones. For the weak fragment we additionally obtain progress and termination, upgrading the guarantee
from "spends ≤ $X" to "*completes within* $X" — a liveness-flavored property no kill-switch provides.
We are explicit about scope: this is the base case (one resource, no concurrency, no affine
no-double-spend layer, no expected-cost), and we lay out the full calculus as roadmap. Finally we
contribute a per-provider billing analysis the empirical prior work lacks: the operational axiom
(per-call cap = a hard billing ceiling) holds for Anthropic (non-interleaved) and the OpenAI
Responses API, but **degrades** for Azure reasoning models and Anthropic interleaved thinking, where
hidden reasoning tokens are billed beyond the declared cap; we prescribe the correct parameter per
provider.

---

## 1. Introduction

**The pain.** LLM-agent frameworks reduce a workflow to a small graph of model calls, tool calls,
branches, loops and sub-agent delegations, and each step consumes tokens (hence money). The cost is
dominated not by reasoning but by *re-sent context*: a stateless API re-sends the system prompt, tool
definitions and the whole conversation on every step, growing superlinearly. The problem is now
documented with primary sources: Cursor issued public refunds for surprise agent bills (July 2025);
**OpenAI eliminated its hard budget cap** — a project budget now only notifies, "API requests will
continue to be processed without interruption" [OpenAI Help Center 9186755]; **Azure OpenAI provides
no hard spending cap** and officially recommends "implementing your own logic in your application to
halt requests" [Microsoft Q&A]. The `TALE` study [2412.18547] documents *token elasticity*: under a
tight budget the model emits *more* tokens, so prompting is not a ceiling.

**The state of the art is runtime and fallible.** Observability vendors (Langfuse, Helicone, Portkey)
sell tracking and alerts, not enforcement; LiteLLM gives runtime per-key budgets for free. The
closest formal work, *Agent Contracts* [2601.08815], specifies multi-dimensional resource bounds
with "conservation laws" but enforces them *at runtime* and admits that a single call's cost is known
only on completion. Khan [2606.04056] is the first to bring *static* typing to bear — an affine
(Rust borrow-checker) mitigation that prevents double-spend of a budget handle — but the paper is
empirical: it offers no calculus and states explicitly that "binary-level cap-soundness… remains
open" (**Conjecture 1**), and excludes reasoning models.

**This paper.** We provide the formal calculus Khan lacks and prove the base case of his conjecture.

*Contributions.*
1. **A calculus** (§2): an affine workflow calculus with numeric potential over the semiring ℕᵏ
   (here k=1 for the weak fragment), with seven constructs mirroring real frameworks, including a
   delegation rule whose linear potential split is adapted from resource-aware session types.
2. **A soundness theorem** (§4): well-typed ⟹ gas ≤ declared potential, on every trace including
   partial and divergent ones — the cap is respected by construction. Proof by induction, audited to
   convergence over three passes (each pass found a real gap; the first "closes" did not close).
3. **A static-vs-runtime characterization** (§5): the type rejects unbounded loops *ahead of time*,
   gives compositional conservation for sequential delegation, and — because the weak fragment is
   strongly normalizing and progresses — certifies *completion* within budget, not just abortion at
   budget. We are precise about what the weak fragment does *not* give (no-double-spend belongs to
   the affine layer).
4. **A per-provider billing analysis** (§3.2): the operational axiom holds for Anthropic
   (non-interleaved) and OpenAI Responses, and degrades for Azure reasoning and Anthropic interleaved
   thinking. The paper prescribes the correct cap parameter per provider — a refinement the empirical
   prior work does not have.

We are explicit about scope throughout: this is the **base case**. Concurrency (`par`/`retry`), the
affine no-double-spend layer, and expected-cost analysis are stated as roadmap (§8), not claimed.

## 2. The calculus (weak fragment: one resource, integer costs, pure potential)

We present the weak fragment used in the soundness proof: a single resource (tokens), integer costs,
and *pure numeric potential* `p ∈ ℕ` (no affine context Γ). The affine handle layer that yields
no-double-spend (Khan's ownership, formalized) is an extension (§8); we keep the base case minimal so
the theorem is checkable.

**Syntax.**
```
e ::= call(c) | tool(c)      -- model/tool call, declared cap c (the API token ceiling)
    | skip                   -- terminated workflow (value)
    | e₁ ; e₂                -- sequence
    | if e₁ e₂               -- branch (nondeterministic choice of a branch)
    | loop(n, e)             -- bounded loop, fuel n a literal. No fuel ⇒ no rule ⇒ does not type.
    | delegate(q, e)         -- sub-agent with transferred potential q (linear split of parent)
```

**Judgment.** `p ⊢ e : ⋄ ; p′`, with `p` the incoming potential and `p′` the residual. (The vector
form ⟨tokens, calls, $⟩ is the same rule over ℕ³; the weak fragment uses k=1.)

**Typing rules.**
```
(T-Call)  p ≥ c                         (T-Skip) ──────────────
          ─────────────────────                  p ⊢ skip : ⋄ ; p
          p ⊢ call(c) : ⋄ ; p − c       (T-Tool) identical to T-Call.

(T-Seq)   p ⊢ e₁:⋄;p₁    p₁ ⊢ e₂:⋄;p₂   (T-If)  p ⊢ e₁:⋄;p₁    p ⊢ e₂:⋄;p₂
          ─────────────────────────             ─────────────────────────
          p ⊢ e₁;e₂ : ⋄ ; p₂                    p ⊢ if e₁ e₂ : ⋄ ; min(p₁,p₂)

(T-Loop)  p_b ⊢ e:⋄;p_b′   b := p_b − p_b′   p ≥ n·b + p′
          ───────────────────────────────────────────────   -- fuel n literal; body has some
          p ⊢ loop(n,e) : ⋄ ; p′                                cost typing b. No fuel ⇒ no rule.

(T-Del)   q ⊢ e:⋄;q′    p ≥ q + p′
          ────────────────────────              -- linear split: parent transfers q;
          p ⊢ delegate(q,e) : ⋄ ; p − q            conservative (does not return q′).
```

The cost `b` in T-Loop is well-defined: Lemma 0(a) below shows every typable `e` has a unique cost
`b_e` independent of the incoming potential, so "some cost typing b" is unambiguous.

## 3. Instrumented semantics and the billing axiom

### 3.1 Small-step semantics with monotone gas
Configurations `⟨e, g⟩` with gas `g ∈ ℕ`. The **operational axiom** is the only place provider
behavior enters:

> **(Cap axiom).** `⟨call(c), g⟩ → ⟨skip, g+a⟩` for some `0 ≤ a ≤ c`.

That is: the API enforces actual cost ≤ the declared cap — *not* the model's obedience (token
elasticity shows the model does not obey budgets in the prompt; the cap is enforced by the API,
which truncates and bills at most `c`). Remaining rules:
```
skip ; e → e        e₁;e₂ → e₁′;e₂  (if e₁→e₁′)      if e₁ e₂ → e_i
loop(n+1, e) → e ; loop(n, e)        loop(0, e) → skip        delegate(q, e) → e
```
Input cost (re-sent context, ~62% of the bill in practice) is subsumed by setting `c = W + cap_out`,
where `W` is a *declared window* annotation; the fuel bounds accumulated context to `n·Δctx ≤ W`.
Without `W` the additive model breaks (this is the load-bearing modeling assumption; §6 / Lemma
discussion). The gas `g` is a global additive counter the semantics never reads — hence invariance
under shifting the initial gas (§4.3).

### 3.2 When the axiom holds: a per-provider billing analysis
The Cap axiom requires that the declared per-call parameter is a hard *billing* ceiling, including
hidden reasoning tokens. This holds unevenly across providers, and getting it right is a contribution
the empirical prior work lacks:

| Provider / mode | Cap parameter | Bounds reasoning tokens? | Cap axiom |
|---|---|---|---|
| **Anthropic** (standard) | `max_tokens` | yes — thinking ⊆ `max_tokens`, billed as output | **holds** |
| **Anthropic** (interleaved thinking, beta) | `max_tokens` | **no** — budget may exceed `max_tokens` across blocks | **degrades** |
| **OpenAI Responses API** | `max_output_tokens` | yes — caps reasoning+output combined | **holds** |
| **Azure OpenAI** (reasoning, o-series/GPT-5) | `max_completion_tokens` | **no** — caps visible output only; reasoning billed unbounded | **degrades** |

So the type's dollar bound is sound where the API truly truncates billing (Anthropic standard,
OpenAI Responses), and on the degrading surfaces the guarantee weakens to a token-on-visible-output
bound. A practical corollary: certify in **tokens/tool-calls** (stable) and map to dollars as a
separate layer parameterized by the provider's billing semantics, rather than baking a dollar figure
into the certificate.

## 4. Soundness

Throughout, "typable" means `∃p,p′. p ⊢ e:⋄;p′`. We prove safety (the bound holds on every trace)
and, for the weak fragment, progress + termination (§5).

### 4.1 Lemma 1 (weakening / monotonicity — raise the input)
If `p ⊢ e:⋄;p′` then `p+r ⊢ e:⋄;p′+r` for all `r ≥ 0`. *Proof:* trivial induction on the derivation;
each rule passes the extra `r` intact from incoming to residual. ∎

### 4.2 Lemma 0 (cost invariance + normal form — the loop-case fix)
**(a) Cost invariance.** For every typable `e`, the cost `p − p′` is the same in every typing
`p ⊢ e:⋄;p′`; call it `b_e`. **(b) Normal form.** `b_e ⊢ e:⋄;0` is derivable. **Corollary:** for all
`x ≥ b_e`, `x ⊢ e:⋄;x − b_e` (normal form + Lemma 1).

*Proof of (a),(b) by structural induction.*
- `call(c)`: `b=c`; `c ⊢ call(c):⋄;0`. `skip`: `b=0`; `0 ⊢ skip:⋄;0`.
- `e₁;e₂`: invariance `p−p₂ = (p−p₁)+(p₁−p₂) = b₁+b₂`; normal form `b₁+b₂ ⊢ e₁:⋄;b₂` (Lemma 1 on
  `b₁ ⊢ e₁:⋄;0`), `b₂ ⊢ e₂:⋄;0` (IH), (T-Seq) gives `b₁+b₂ ⊢ e₁;e₂:⋄;0`.
- `if e₁ e₂`: invariance `p − min(p₁,p₂) = max(p−p₁, p−p₂) = max(b₁,b₂)`; normal form
  `max(b₁,b₂) ⊢ e_i:⋄; max−b_i` (Lemma 1), (T-If) with residual `min = max−max = 0`.
- `loop(n,e)`: `b = n·b_body` (T-Loop); `n·b_body ⊢ loop(n,e):⋄;0`.
- `delegate(q,e)`: `b = q`; `q ⊢ delegate(q,e):⋄;0` by (T-Del) with `p=q, p′=0`. ∎

*(`b_e` is independent of the input — what AARA calls fungible potential. Lemma 1 cannot* lower *a
derivation from `p_b` to `p`; but one can re-derive from the normal form `b_e` and raise, which is
what the loop case needs.)*

### 4.3 Lemma 2 (one-step preservation, strengthened — the sequence-case fix)
**If `p ⊢ e:⋄;p′` and `⟨e,g⟩ → ⟨e′,g′⟩` with `d := g′−g`, then (i) `d ≤ p` and (ii) there exists
`r ≥ p′` with `p−d ⊢ e′:⋄;r`.** The clause `r ≥ p′` (which an earlier version omitted) is what lets
T-Seq recompose: a step costing ≤ its cap leaves *at least* the residual the type predicted.

*Proof by cases (inversion of typing).*
- **`call(c)→skip`, `d=a≤c`.** (T-Call): `p≥c`, `p′=p−c`. (i) `a≤c≤p`. (ii) (T-Skip):
  `p−a ⊢ skip:⋄;p−a`; `r=p−a ≥ p−c = p′`. (tool identical.)
- **`skip;e₂→e₂`, `d=0`.** (T-Seq)+(T-Skip): `p₁=p`, `p ⊢ e₂:⋄;p′`. `r=p′`.
- **`e₁;e₂` with `e₁→e₁′`, `d≥0`.** (T-Seq): `p ⊢ e₁:⋄;p₁`, `p₁ ⊢ e₂:⋄;p′`. IH on `e₁`: `d≤p` and
  `∃r₁≥p₁. p−d ⊢ e₁′:⋄;r₁`. Since `r₁≥p₁`, Lemma 1 raises `e₂` from `p₁` to `r₁`:
  `r₁ ⊢ e₂:⋄;p′+(r₁−p₁)`. (T-Seq): `p−d ⊢ e₁′;e₂:⋄; p′+(r₁−p₁)`, and `r := p′+(r₁−p₁) ≥ p′`.
- **`if e₁ e₂→e_i`, `d=0`.** (T-If): `p ⊢ e_i:⋄;p_i` with `p_i ≥ min(p₁,p₂)=p′`. `r=p_i ≥ p′`.
- **`loop(n+1,e)→e;loop(n,e)`, `d=0`.** (T-Loop): body cost `b=b_e`, `p ≥ (n+1)b + p′`. By Lemma 0
  (normal form of body raised to `p`, valid since `p ≥ (n+1)b ≥ b`): `p ⊢ e:⋄;p−b`. Then (T-Loop,
  fuel n): `p−b ⊢ loop(n,e):⋄;p−(n+1)b`. (T-Seq): `p ⊢ e;loop(n,e):⋄;p−(n+1)b`. Since
  `p ≥ (n+1)b+p′`, `r := p−(n+1)b ≥ p′`. **`loop(0,e)→skip`:** `r=p≥p′`.
- **`delegate(q,e)→e`, `d=0`.** (T-Del): `q ⊢ e:⋄;q′`, `p≥q+p′`. Lemma 1 raises the child from `q`
  to `p`: `p ⊢ e:⋄;p−q+q′`. `r=p−q+q′ ≥ p−q ≥ p′`. ∎

### 4.4 Theorem (gas bound — safety, every trace incl. partial/divergent)
**For all `g₀`: if `p ⊢ e:⋄;_` and `⟨e,g₀⟩ →* ⟨e″,g⟩`, then `g−g₀ ≤ p`.** (With `g₀=0`: `g ≤ p`.)

*Proof by induction on the number `m` of steps.* `m=0`: `g−g₀=0 ≤ p`. `m→m+1`:
`⟨e,g₀⟩→⟨e₁,g₁⟩→*⟨e″,g⟩`. By Lemma 2: `d₁=g₁−g₀ ≤ p` and `p−d₁ ⊢ e₁:⋄;_` with `p−d₁≥0`. By IH on
the `m`-step subtrace from `⟨e₁,g₁⟩` (incoming potential `p−d₁`): `g−g₁ ≤ p−d₁`. Summing:
`g−g₀ = (g₁−g₀)+(g−g₁) ≤ d₁+(p−d₁) = p`. ∎

**Corollary (Conjecture 1, base case).** Every well-typed workflow with potential `p` spends `≤ p` on
every execution, including prefixes of divergent traces. The cap holds by construction.

## 5. What the type certifies that a runtime tracker does not

A runtime budget with a kill-switch gives safety only — it aborts when the meter hits `B`, after
spending `B`, possibly mid-task. The type gives more, all *ahead of time*:

- **(a) Ex-ante rejection of unbounded loops.** A `loop` without a fuel literal has no typing rule;
  the canonical runaway (an Analyzer↔Verifier "retry-until-done" pair) is a *type error*, rejected at
  check time, not a runtime abort after overspending. (This sub-claim is light — it reduces to a
  syntactic check — but a runtime tracker cannot reject it ex-ante; it discovers the runaway by
  spending up to `B`.)
- **(b) Static compositional conservation for sequential/nested delegation.** (T-Del) guarantees
  `Σ qᵢ ≤ p` *before* execution. *Honest scope:* proved for sequential/nested delegation; the
  concurrent tree needs `par` and an interleaving semantics (§8).
- **(c) "Completes within $X", not just "spends ≤ $X".** The weak fragment is strongly normalizing
  (no general recursion; fuel bounds every loop; the measure ⟨weighted fuel, size⟩ decreases) and
  *progresses* (every non-`skip` typable term can step). Hence a well-typed workflow with potential
  `p` *terminates and spends ≤ p* ⇒ "I will finish for ≤ $X". A tracker gives only "aborts at $X" —
  you pay `X` and get a half-finished result. This liveness-flavored guarantee is genuine and beyond
  any safety-only kill-switch.

**What the weak fragment does *not* give.** No-double-spend of a context resource is *not* a
consequence of the pure-potential rules; it requires affine handles with linear context split
(`Γ = Γ₁ ⊎ Γ₂` in T-Seq/T-Del, forbidden inside loop bodies). That is exactly the ownership
discipline Khan implements empirically in Rust; formalizing it is a standard affine extension,
deferred to the full calculus (§8). We flag this explicitly to avoid over-claiming.

## 6. Mapping to frameworks: the checker is a linter, not a new DSL

The seven constructs type annotations developers *already* write:

| Construct | LangGraph | OpenAI Agents SDK | CrewAI | Temporal |
|---|---|---|---|---|
| `call(c)` | model cap | `max_output_tokens` | model cap | activity |
| `loop(n,·)` | `recursion_limit` | `max_turns` | `max_iter` | retry policy |
| `delegate(q,·)` | `Send`/subgraph | handoff | hierarchical | child workflow |
| `par(·)` | parallel `Send` | parallel tools | — | parallel children |

A checker therefore enters the ecosystem as a *linter/transpiler over existing config*, not as a
language anyone has to adopt. A `loop` whose `recursion_limit` is missing (or whose declared budget
does not cover the fuel-times-cost bound) is flagged before deploy.

## 7. Related work

- **Khan [2606.04056]** (June 2026): 63-incident catalogue + affine (Rust) mitigation; states
  Conjecture 1 (cap-soundness) open; no calculus; excludes reasoning models. *We resolve the base
  case and add the per-provider billing analysis it lacks.*
- **Automatic Amortized Resource Analysis** (Hofmann–Jost POPL 2003; "Two Decades of AARA", MSCS
  2022): the potential method; soundness formulations valid for non-terminating executions. *Our weak
  fragment is the degenerate linear case; no prior AARA work targets LLM agents.*
- **Resource-aware session types** (Das–Hoffmann–Pfenning, LICS 2018; digital contracts, 2019): work
  analysis with potential over message-passing processes; potential↔gas. *Our delegation split adapts
  this; mapping potential↔tokens/$ is new.*
- **Agent Contracts [2601.08815]** (AAMAS 2026): multi-dimensional resource bounds with conservation
  laws, enforced at runtime; admits a single call can exceed the budget. *Our conservation corollary
  is its static counterpart.*
- **The LLMbda calculus [2602.20064]** (Gordon, Sands, Feb 2026): a λ-calculus with information-flow
  control for agent conversations; noninterference. *Complementary: PL theory has entered agent
  formalization, but along information flow, not resources — the slot we occupy.*

## 8. Limitations and roadmap

This is the **base case**, deliberately minimal so the theorem is checkable. The full calculus adds:
the **affine handle layer** (linear context split ⟹ no-double-spend, formalizing Khan's ownership);
**`par`/`retry` with an interleaving semantics** (conservation over concurrent trees; Lemma 2
generalizes to a sum over branches with disjoint affine order); **expected-cost** via probabilistic
AARA (Ngo–Carbonneaux–Hoffmann, PLDI 2018) to tighten the 4–6× worst-case over-reservation — a
separate development with its own subtleties (optional stopping, supermartingales); and **reasoning
models** under the §3.2 billing axiom, with Azure-reasoning marked as the surface where the dollar
bound degrades to a visible-output bound. The accompanying artifact (`check.py`) mechanically
verifies the algebra and reports zero `g ≤ p` violations over 200,000 random traces.

---

*Artifact and proof source: github.com/hernaninverso (to be released). Audited over three passes;
the first "closes" did not close — each audit pass surfaced a real gap (the SEQ case, then the LOOP
case) that was fixed before this draft.*
