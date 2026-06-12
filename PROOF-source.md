# teorema.md — Agentes con recursos tipados: el teorema de la Conjecture 1 (v2, post-audit)

> Spike de papel ($0). Prueba la soundness ("well-typed ⟹ cap respetado") que **arXiv 2606.04056**
> (Khan, jun-2026) deja como **Conjecture 1** abierta. Maquinaria: Hofmann–Jost (AARA, potencial) +
> delegación de resource-aware session types (Das–Hoffmann–Pfenning, 1712.08310).
> **VEREDICTO: VIVE** — la soundness débil cierra por inducción (con el Lema 2 fortalecido que pidió la
> auditoría). Caveats de la auditoría incorporados: ver §3.4 (lo que el tipo SÍ y NO certifica vs un tracker).

## 0. Gate Día 1 AM (GO)
- **KILL-1 (novedad) — PASA.** Khan: catálogo de 63 incidentes + mitigación afín en Rust pero **NO
  cálculo formal ni prueba**: "Binary-level cap-soundness… remains open" (Conjecture 1). AARA y
  resource-aware session types (2018-20) jamás apuntados a agentes LLM. Slot libre (~6 meses).
- **KILL-4 (axioma de facturación) — PASA con caveat.** `max_tokens` es techo DURO de facturación de
  output per-call **incl. reasoning** en **Anthropic** (thinking ⊆ max_tokens) y **OpenAI Responses API**
  (`max_output_tokens` acota total incl. reasoning; "you cannot exceed it"). **DEGRADA** en **Azure
  OpenAI reasoning** (`max_completion_tokens` acota sólo output VISIBLE; reasoning "hidden and unbounded",
  facturado por encima). → El axioma operacional vale en los APIs principales; el paper PRESCRIBE el
  parámetro correcto y marca Azure-reasoning como superficie donde la cota-$ degrada. Contribución, no kill.

## 1. El cálculo (fragmento débil: 1 recurso = tokens, costos enteros; potencial PURO, sin Γ)
> Nota post-audit: el fragmento débil NO usa contexto afín Γ (era peso muerto y, reusado en T-Seq/T-Loop,
> habría violado afinidad). El recurso es el POTENCIAL `p`. La capa de **handles afines** (que da el
> no-double-spend de Khan, §3.4) es una extensión con **split lineal de contexto** (estándar), §6.

Sintaxis:
```
e ::= call(c) | tool(c)   -- llamada/tool, cap declarado c (token ceiling del API)
    | skip                -- valor (workflow terminado)
    | e₁ ; e₂ | if e₁ e₂  -- secuencia / rama
    | loop(n, e)          -- loop con FUEL n (literal). SIN fuel: no hay regla → NO tipa.
    | delegate(q, e)      -- sub-agente con potencial transferido q (split lineal del padre)
```
**Juicio:** `p ⊢ e : ⋄ ; p′` — `p∈ℕ` potencial entrante, `p′∈ℕ` residual. (Vector ⟨tokens,calls,$⟩ =
misma regla sobre el semiring ℕ³; el débil usa k=1.)

### Reglas de tipado
```
(T-Call) p≥c                      (T-Skip) ───────────────
       ──────────────────────              p ⊢ skip:⋄;p
       p ⊢ call(c):⋄;p−c          (T-Tool) idéntica a Call.

(T-Seq)  p ⊢ e₁:⋄;p₁    p₁ ⊢ e₂:⋄;p₂          (T-If)  p ⊢ e₁:⋄;p₁   p ⊢ e₂:⋄;p₂
         ────────────────────────────                 ────────────────────────────
         p ⊢ e₁;e₂:⋄;p₂                               p ⊢ if e₁ e₂:⋄;min(p₁,p₂)

(T-Loop) p_b ⊢ e:⋄;p_b′   b := p_b−p_b′   p ≥ n·b + p′      -- fuel n literal; cuerpo con ALGÚN
         ──────────────────────────────────────────────       tipado de costo b. Residual p′ libre
         p ⊢ loop(n,e):⋄; p′                                  (≤ p−n·b). SIN fuel ⇒ no hay regla.

(T-Del)  q ⊢ e:⋄;q′   p ≥ q+p′                              -- split lineal: el padre transfiere q;
         ──────────────────────────────                       conservativo (no devuelve q′).
         p ⊢ delegate(q,e):⋄;p−q
```

## 2. Semántica small-step instrumentada (gas monótono)
Config `⟨e,g⟩`, `g∈ℕ`. **AXIOMA OPERACIONAL (KILL-4):** `⟨call(c),g⟩→⟨skip,g+a⟩` para algún `0≤a≤c`
(el API enforcea costo real ≤ cap; NO la obediencia del LLM). `skip;e→e`; `e₁;e₂→e₁′;e₂` si `e₁→e₁′`;
`if e₁ e₂→e_i`; `loop(n+1,e)→e;loop(n,e)`; `loop(0,e)→skip`; `delegate(q,e)→e`. (El gas es un contador
aditivo global que la semántica NUNCA lee → invariante por desplazamiento, §3.3.)
Costo de ENTRADA (contexto re-enviado) subsumido en `c = W+cap_out`, `W`=ventana declarada (anotación);
el fuel acota contexto acumulado a `n·Δctx ≤ W`. Sin `W`, el modelo aditivo se rompe (KILL-3, §5).

## 3. Soundness
### 3.1 Lema 1 (weakening / monotonía — sube la entrada)
`p ⊢ e:⋄;p′ ⟹ p+r ⊢ e:⋄;p′+r` para `r≥0`. (Inducción trivial en la derivación: cada regla pasa el
extra `r` intacto de entrante a residual.) ∎

### 3.1bis Lema 0 (costo invariante + forma normal — fix de la auditoría para el caso LOOP)
**(a) Costo invariante:** para todo `e` TIPABLE, el costo `p−p′` es el MISMO en toda tipificación
`p⊢e:⋄;p′`; lo llamamos `b_e`. **(b) Forma normal:** `b_e ⊢ e:⋄;0` es derivable. **Corolario:** `∀x≥b_e,
x ⊢ e:⋄;x−b_e` (forma normal + Lema 1, subiendo de `b_e` a `x`).
*Prueba* de (a)+(b) por inducción estructural: call(c): `b=c`, `c⊢call(c):⋄;0` ✓. skip: `b=0`,
`0⊢skip:⋄;0` ✓. seq: `b=b₁+b₂` (invariante: `p−p₂=(p−p₁)+(p₁−p₂)`); forma normal: `b₁+b₂⊢e₁:⋄;b₂`
(Lema 1 sobre `b₁⊢e₁:⋄;0`), `b₂⊢e₂:⋄;0` (HI), (T-Seq) ⟹ `b₁+b₂⊢e₁;e₂:⋄;0` ✓. if: `b=max(b₁,b₂)`
(invariante: `p−min(p₁,p₂)=max(p−p₁,p−p₂)`); forma normal: `max(b₁,b₂)⊢e_i:⋄;max−b_i` por Lema 1, (T-If)
con residual `min = max−max = 0` ✓. loop: `b=n·b_body` (T-Loop); `n·b_body⊢loop(n,e):⋄;0` por la regla.
delegate: `b=q`; `q⊢delegate(q,e):⋄;0` por (T-Del) con `p=q,p′=0` ✓. ∎
(Nota: `b_e` independiente de la entrada es lo que un AARA estándar llama "el potencial es fungible";
NO se puede BAJAR una derivación con Lema 1, pero SÍ se puede re-derivar desde la forma normal `b_e`.)

### 3.2 Lema 2 (preservación de un paso, FORTALECIDO — fix de la auditoría)
**Si `p ⊢ e:⋄;p′` y `⟨e,g⟩ → ⟨e′,g′⟩` con `d:=g′−g`, entonces (i) `d ≤ p` y (ii) existe `r ≥ p′` con
`p−d ⊢ e′:⋄;r`.**  (La cláusula clave `r ≥ p′` — que la auditoría señaló faltante — es la que permite
recomponer en T-Seq: un paso que cuesta `≤` su cap deja AL MENOS el residual que el tipo predijo.)
*Prueba* por casos (inversión del tipado):
- **call(c)→skip, d=a≤c.** (T-Call): `p≥c`, `p′=p−c`. (i) `a≤c≤p`. (ii) (T-Skip): `p−a ⊢ skip:⋄;p−a`;
  `r=p−a ≥ p−c = p′`. ✓  (tool idéntico.)
- **skip;e₂→e₂, d=0.** (T-Seq)+(T-Skip): `p₁=p`, `p ⊢ e₂:⋄;p′`. (ii) `r=p′`. ✓
- **e₁;e₂ con e₁→e₁′, d≥0.** (T-Seq): `p ⊢ e₁:⋄;p₁`, `p₁ ⊢ e₂:⋄;p₂(=p′)`. HI sobre e₁:
  `d≤p` y `∃r₁≥p₁. p−d ⊢ e₁′:⋄;r₁`. Como `r₁≥p₁`, por Lema 1 (subir e₂ de `p₁` a `r₁`):
  `r₁ ⊢ e₂:⋄;p′+(r₁−p₁)`. (T-Seq): `p−d ⊢ e₁′;e₂:⋄; p′+(r₁−p₁)`, y `r := p′+(r₁−p₁) ≥ p′`. ✓
  **(Este es exactamente el caso que la auditoría marcó; cierra con `r₁≥p₁`.)**
- **if e₁ e₂→e_i, d=0.** (T-If): `p ⊢ e_i:⋄;p_i` con `p_i ≥ min(p₁,p₂)=p′`. (ii) `r=p_i ≥ p′`. ✓
- **loop(n+1,e)→e;loop(n,e), d=0.** (T-Loop): el cuerpo tiene costo `b=b_e`, `p≥(n+1)b+p′`. Por
  **Lema 0** (forma normal del cuerpo + subir a `p`, válido pues `p≥(n+1)b+p′≥b`): `p ⊢ e:⋄;p−b`. Luego
  (T-Loop, fuel n, residual `p−b−nb`): `p−b ⊢ loop(n,e):⋄;p−(n+1)b`. (T-Seq): `p ⊢ e;loop(n,e):⋄;p−(n+1)b`.
  Como el tipado original `p⊢loop(n+1,e):⋄;p′` tiene `p≥(n+1)b+p′`, se cumple `r := p−(n+1)b ≥ p′`. ✓
  **loop(0,e)→skip:** `r=p≥p′`. ✓
  *(Dos fixes de la auditoría: (i) el Lema 1 NO baja de `p_b` a `p`; el Lema 0 re-deriva el cuerpo desde
  su forma normal `b_e` y sube a `p`, legítimo pues `p≥b_e`. (ii) el residual es `p−(n+1)b ≥ p′`, no `=p′`
  — y Lema 2 sólo pide `r≥p′`.)*
- **delegate(q,e)→e, d=0.** (T-Del): `q ⊢ e:⋄;q′`, `p≥q+p′`. Por Lema 1 (subir el hijo de `q` a `p`):
  `p ⊢ e:⋄;p−q+q′`. `r=p−q+q′ ≥ p−q ≥ p′`. ✓ ∎

### 3.3 TEOREMA (cota de gas — safety, toda traza incl. parcial/divergente)
**Para todo `g₀`: si `p ⊢ e:⋄;_` y `⟨e,g₀⟩ →* ⟨e″,g⟩`, entonces `g−g₀ ≤ p`.** (Enunciado con gas
inicial arbitrario `g₀` — invariancia por desplazamiento, ya que la semántica no lee `g`. Con `g₀=0`:
`g ≤ p`.)
*Prueba* por inducción en `m`=nº de pasos. **m=0:** `g−g₀=0 ≤ p`. **m→m+1:**
`⟨e,g₀⟩→⟨e₁,g₁⟩→*⟨e″,g⟩`. Por Lema 2: `d₁=g₁−g₀ ≤ p` y `p−d₁ ⊢ e₁:⋄;_` con `p−d₁≥0`. Por HI sobre la
subtraza de `m` pasos desde `⟨e₁,g₁⟩` (potencial entrante `p−d₁`): `g−g₁ ≤ p−d₁`. Sumando:
`g−g₀ = (g₁−g₀)+(g−g₁) ≤ d₁ + (p−d₁) = p`. ∎
**Corolario (Conjecture 1, nivel cálculo):** todo workflow bien-tipado con potencial `p` tiene gasto
`≤ p` en TODA ejecución (incl. prefijos de trazas divergentes). El cap se respeta por construcción.

### 3.4 Qué certifica el tipo que un tracker runtime+kill-switch NO (KILL-2, post-audit)
La auditoría pulió las 4 afirmaciones originales. Lo que SOBREVIVE como ventaja del tipo (toda
**ESTÁTICA / ahead-of-time**, antes de gastar un token):
- **(a) Rechazo EX-ANTE de loops sin fuel.** `loop` sin literal de fuel **no tipa** → rechazado en
  compile-time. El runaway Analyzer↔Verifier es un **error de tipo**, no un abort tras gastar de más.
  (Auditoría: "reducible a validación sintáctica" — cierto, es ligero, pero un tracker runtime NO puede
  rechazar ex-ante; descubre el runaway gastando hasta B.)
- **(b) Conservación composicional ESTÁTICA en delegación SECUENCIAL/anidada.** Para `delegate`s en
  secuencia, (T-Del) garantiza `Σ q_i ≤ p` ANTES de ejecutar (verificado en check.py: 2000+2500≤5000
  tipa; 3000+3000 no). **Scope honesto (auditoría):** probado para delegación secuencial/anidada; el
  árbol CONCURRENTE necesita `par` + semántica de interleaving (§6, paper completo).
- **(c) "COMPLETA dentro de $X" — requiere Progreso + Terminación (que el fragmento débil SÍ tiene).**
  - **Lema Progreso:** todo `e≠skip` bien-tipado puede dar un paso. (Inducción estructural: call/tool/
    if/loop/delegate tienen regla de paso; seq reduce el sub-término izquierdo o consume skip.) ∎
  - **Terminación:** el fragmento débil es fuertemente normalizante (sin recursión general; el fuel
    acota todo loop; medida = (Σ fuel ponderado, tamaño) decrece). ∎
  - ⟹ con potencial `p`, un workflow bien-tipado **termina Y gasta `≤ p`** ⇒ "lo termino por ≤ $X".
    Un tracker da sólo "aborta en $X" → pagás $X y te queda un resultado a medio terminar. Esta
    distinción liveness-flavored es genuina y NO la da un kill-switch (safety puro).
- **(d) No-double-spend — NO en el fragmento débil; va a la capa afín (formaliza la ownership de Khan).**
  La auditoría tiene razón: las reglas potencial-puras no impiden reusar un recurso de contexto. El
  no-double-spend requiere **handles afines con split lineal de contexto** (Γ=Γ₁⊎Γ₂ en T-Seq/T-Del,
  prohibido en cuerpos de loop). Es la extensión estándar (afín/lineal) y es exactamente lo que Khan ya
  tiene EMPÍRICAMENTE en Rust; la formalización la añade sin obstáculo. **Deferido al cálculo completo.**

→ **KILL-2 NO se dispara**, pero el aporte es más preciso que mi afirmación inicial: el tipo da
**certificación estática ahead-of-time** (rechazo ex-ante + conservación secuencial + completa-dentro-de-$X
vía progreso+terminación) que un tracker dinámico no da. El no-double-spend (4º eje) NO está en el débil:
es la capa afín (Khan-ownership formalizada), extensión estándar del paper completo.

## 4. Test de sanidad (check.py) — pasa
loop A2A sin fuel: **no tipa** (rechazo ex-ante). Con fuel=10: tipa, cota `10·(800+600)=14000`; con
presupuesto 13999 (cota−1): rechaza. Conservación secuencial: 4500≤5000 tipa, 6000>5000 no.
**Soundness §3.3: 0 violaciones de `g≤p` en 200.000 trazas aleatorias** (con `a≤c`).

## 5. KILL-3 (cost model) — NO se dispara, con asunción documentada
El costo de entrada (contexto re-enviado, superlineal) no rompe la aditividad **bajo la anotación de
ventana `W`** (`call` cuesta `≤ W+cap`; fuel acota contexto a `n·Δctx≤W`). Sin `W`, falla → la ventana
es load-bearing (contribución de modelado). Worst-case determinista usa `c=cap` (sobre-reserva 4-6×).

## 6. Roadmap (paper completo, NO el spike)
- **Capa afín** (split lineal de contexto) ⟹ no-double-spend (§3.4d), formalizando la ownership de Khan.
- **`par`/`retry` + semántica concurrente** ⟹ conservación en árboles (§3.4b) — el Lema 2 generaliza a
  la suma de ramas; orden afín disjoint entre ramas.
- **Expected-cost** (AARA probabilístico, Ngo–Carbonneaux–Hoffmann) — capa 2, OTRO spike (optional
  stopping, supermartingalas).
- **Reasoning models** (hidden CoT) — bajo el axioma KILL-4 (Anthropic/OpenAI-Responses), `cap` incluye
  reasoning; Azure-reasoning queda como superficie donde la cota-$ degrada a cota-output-visible.

## 7. Mapeo primitiva ↔ framework (checker = LINTER de configs, no DSL nuevo)
`call(c)`→model cap / `max_output_tokens`·`max_tokens`; `loop(n)`→`recursion_limit`(LangGraph)·
`max_turns`(OpenAI)·`max_iter`(CrewAI); `delegate(q)`→`Send`/subgraph·handoff·hierarchical·child workflow;
`par`→parallel Send/tools. Las 7 primitivas tipifican anotaciones que los devs YA escriben.

## 8. VEREDICTO
**VIVE.** La soundness débil cierra (Teorema §3.3). **Auditada en 3 pasadas** (anti "teorema mal
probado"): (1) council de 6 voces cazó el gap del caso SEQ + sobre-afirmaciones de producto; (2) audit-3
cazó el gap del caso LOOP (Lema 1 no baja de `p_b` a `p`); (3) audit-3 final → sólo cosméticos ("e
tipable" en Lema 0, `r≥p′` no `=p′`). Convergió: el Lema 2 fortalecido (`r≥p′`) + Lema 0 (costo
invariante/forma normal) cierran SEQ y LOOP; gas-shift cubre trazas parciales/divergentes. Kill-criteria: KILL-1 libre,
KILL-3 (ventana), KILL-4 (axioma válido en APIs principales + caveat Azure). **KILL-2 sobrevive pero más
estrecho:** el tipo aporta certificación ESTÁTICA ahead-of-time (rechazo ex-ante + conservación
secuencial + completa-dentro-de-$X vía progreso+terminación); el no-double-spend va a la capa afín
(extensión estándar = ownership de Khan formalizada). **Recomendación (ventana ~6 meses): preprint corto
YA** del fragmento débil como "resolución de la Conjecture 1 de Khan" — cálculo + soundness (auditada) +
el caveat de facturación por-provider (que Khan no tiene) + mapeo a configs. Después: capa afín (no-double-
spend), `par`/`retry`/concurrencia, expected-cost, reasoning. **La decisión de escribir/publicar es de
Hernán** (NO publico nada por mi cuenta).
