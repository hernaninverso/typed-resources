# SPEC — preprint corto "Typed Resource Bounds for Agent Workflows"

> Spec-kit lite del paper (no código). Define claims, scope y estructura ANTES de escribir,
> para que el council revise contra un contrato y no contra el gusto.

## Objetivo (una frase)
Un preprint corto en arXiv que **resuelve a nivel cálculo el caso base de la Conjecture 1 de Khan**
(arXiv 2606.04056): un cálculo afín con potencial para workflows de agentes + prueba de soundness
"well-typed ⟹ el gasto nunca excede el potencial declarado", en TODA traza (incl. parcial/divergente),
más un hallazgo de facturación por-provider que el prior-art empírico no tiene.

## Claims (lo que el paper AFIRMA — el council verifica cada uno)
- **C1 (teorema central):** para el fragmento débil (1 recurso, costos enteros, potencial puro), si
  `p ⊢ e:⋄;_` y `⟨e,g₀⟩→*⟨e″,g⟩` bajo el axioma de cap per-call, entonces `g−g₀ ≤ p`. Probado por
  inducción; auditado a convergencia (3 pasadas).
- **C2 (liveness del fragmento):** el fragmento débil es fuertemente normalizante y progresa →
  certifica "COMPLETA dentro de $X" (no sólo "gasta ≤$X"), distinción que un kill-switch no da.
- **C3 (certificación estática vs runtime):** el tipo da rechazo ex-ante de loops sin fuel +
  conservación composicional secuencial + (C2), todo ahead-of-time. NO reclama no-double-spend en
  el fragmento débil (eso es la capa afín, future work).
- **C4 (hallazgo de billing):** el axioma operacional (cap per-call = techo de facturación) vale en
  Anthropic (no-interleaved) y OpenAI Responses; DEGRADA en Azure reasoning (`max_completion_tokens`
  no acota reasoning tokens) y en Anthropic *interleaved thinking* (budget puede exceder max_tokens).
  El paper prescribe el parámetro correcto por-provider. Khan no tiene esto.
- **C5 (aplicabilidad):** las 7 primitivas tipifican anotaciones que los devs YA escriben
  (recursion_limit/max_turns/max_iter/handoff) → el checker es un linter de configs, no un DSL nuevo.

## Scope — lo que el paper NO reclama (anti sobre-afirmación; explícito en el abstract)
- NO es el cálculo completo: sin `par`/`retry`/concurrencia, sin la capa afín (no-double-spend),
  sin expected-cost probabilístico. Es el **caso base**.
- NO reclama cota en dólares estable (los precios cambian) — certifica tokens/tool-calls; el mapeo a $
  es una capa aparte con la asunción de billing de C4.
- NO reclama manejo de reasoning models donde el provider no acota (Azure-reasoning queda marcado
  como superficie donde la cota degrada).

## Estructura (target: 6-8 pp, workshop/short)
1. Introducción (dolor con fuentes citables + Khan + contribución: resolvemos el caso base de su Conj.1)
2. El cálculo afín con potencial (sintaxis, juicio, reglas)
3. Semántica instrumentada + axioma de cap + el hallazgo de billing por-provider (C4)
4. Soundness (Lemas 0/1/2 + Teorema) — la prueba auditada
5. Qué certifica el tipo que un tracker no (C2/C3) — defensa anti-trivial
6. Mapeo a frameworks (C5)
7. Related work
8. Limitaciones y roadmap (el fragmento débil + future work explícito)

## Gate del council
Convergencia: cada voz APRUEBA o sus P0 están resueltos. P0 = error en la prueba, claim fáctico
falso (billing), sobre-afirmación de scope, o novedad refutada (alguien ya lo probó). El "es trivial"
es P1 de framing, no P0 — se mitiga con presentación, no mata el preprint.

## Venue
Preprint arXiv (prioridad, esta semana) → LMPL 2026 (workshop, 26-jun) → POPL/venue top con la capa
afín agregada (no este draft).
