"""Spike typed-resources — chequeo del ÁLGEBRA del cálculo (no es el producto, es el sanity-check).
(1) type-checker del fragmento débil: el loop A2A sin fuel NO tipa; con fuel tipa con cota.
(2) conservación de delegación: Σ q_hijos ≤ p_padre.
(3) simulador small-step: sobre N trazas aleatorias (a ≤ c), verifica g ≤ p (soundness §3)."""
import random

# AST
class Call:  # call(c) / tool(c)
    def __init__(s, c): s.c = c
class Skip: pass
class Seq:
    def __init__(s, a, b): s.a, s.b = a, b
class If:
    def __init__(s, a, b): s.a, s.b = a, b
class Loop:        # loop(n, e) con fuel n (literal entero)
    def __init__(s, n, e): s.n, s.e = n, e
class LoopNoFuel:  # loop SIN fuel (recursión "until done") — NO debe tipar
    def __init__(s, e): s.e = e
class Delegate:
    def __init__(s, q, e): s.q, s.e = q, e

class TypeError_(Exception): pass

def check(e, p):
    """Devuelve p' tal que ;p ⊢ e:⋄;p'. Lanza TypeError_ si no tipa. (Γ afín implícito.)"""
    if isinstance(e, Skip): return p
    if isinstance(e, Call):
        if p < e.c: raise TypeError_(f"call(c={e.c}) no tipa: p={p} < c")
        return p - e.c
    if isinstance(e, Seq):
        return check(e.b, check(e.a, p))
    if isinstance(e, If):
        return min(check(e.a, p), check(e.b, p))
    if isinstance(e, Loop):
        b = p_body_cost(e.e)         # costo worst-case del cuerpo (un loop con fuel)
        need = e.n * b
        if p < need: raise TypeError_(f"loop(n={e.n}) no tipa: p={p} < n*b={need}")
        return p - need
    if isinstance(e, LoopNoFuel):
        raise TypeError_("loop SIN fuel: no hay regla de tipado → RECHAZADO ex-ante (KILL-2 §4.1)")
    if isinstance(e, Delegate):
        check(e.e, e.q)              # el hijo debe tipar bajo su potencial transferido q
        if p < e.q: raise TypeError_(f"delegate(q={e.q}) no tipa: p={p} < q")
        return p - e.q               # split lineal: el padre pierde q (conservativo, no devuelve q')
    raise TypeError_("nodo desconocido")

def p_body_cost(e):
    """Costo determinista (worst-case) de un cuerpo sin loop-no-fuel, asumiendo entrante=costo."""
    if isinstance(e, Skip): return 0
    if isinstance(e, Call): return e.c
    if isinstance(e, Seq): return p_body_cost(e.a) + p_body_cost(e.b)
    if isinstance(e, If): return max(p_body_cost(e.a), p_body_cost(e.b))
    if isinstance(e, Loop): return e.n * p_body_cost(e.e)
    if isinstance(e, Delegate): return e.q
    if isinstance(e, LoopNoFuel): raise TypeError_("body no-Horn: loop sin fuel")
    raise TypeError_("?")

# (3) simulador small-step: corre e con costos reales a ≤ c aleatorios, devuelve gas total
def run(e, rng):
    if isinstance(e, (Skip,)): return 0
    if isinstance(e, Call): return rng.randint(0, e.c)           # AXIOMA KILL-4: a ≤ c
    if isinstance(e, Seq): return run(e.a, rng) + run(e.b, rng)
    if isinstance(e, If): return run(rng.choice([e.a, e.b]), rng)
    if isinstance(e, Loop): return sum(run(e.e, rng) for _ in range(e.n))
    if isinstance(e, Delegate): return run(e.e, rng)
    raise RuntimeError("no ejecutable (no tipa)")

def typecheck_ok(e, p):
    try:
        check(e, p); return True, None
    except TypeError_ as ex:
        return False, str(ex)

if __name__ == "__main__":
    print("=== (1) loop A2A Analyzer↔Verifier (test de sanidad obligatorio) ===")
    body = Seq(Call(800), Call(600))   # Analyzer cap 800 ; Verifier cap 600
    a2a_nofuel = LoopNoFuel(body)      # "retry until verified" — el patrón runaway
    a2a_fuel   = Loop(10, body)        # con fuel=10 turnos
    ok1, why1 = typecheck_ok(a2a_nofuel, 100000)
    print(f"  loop SIN fuel, p=100000:  tipa={ok1}   ({why1})")
    ok2, why2 = typecheck_ok(a2a_fuel, 100000)
    bound = 10 * (800 + 600)
    print(f"  loop fuel=10, p=100000:   tipa={ok2}   cota = 10*(800+600) = {bound}, residual={check(a2a_fuel,100000)}")
    ok3, _ = typecheck_ok(a2a_fuel, bound - 1)
    print(f"  loop fuel=10, p={bound-1} (cota-1): tipa={ok3}  (rechaza si el presupuesto no cubre la cota)")

    print("\n=== (2) conservación composicional en delegación (Σ q_hijos ≤ p_padre) ===")
    # padre con p=5000 delega 2000 y 2500 a dos hijos (cada hijo hace 1 call dentro de su q)
    child1 = Delegate(2000, Call(1500)); child2 = Delegate(2500, Call(2000))
    parent = Seq(child1, child2)
    ok, why = typecheck_ok(parent, 5000)
    print(f"  padre p=5000, hijos q=2000+2500=4500 ≤ 5000: tipa={ok}  residual={check(parent,5000) if ok else '—'}")
    ok_bad, why_bad = typecheck_ok(Seq(Delegate(3000, Call(2000)), Delegate(3000, Call(2000))), 5000)
    print(f"  padre p=5000, hijos q=3000+3000=6000 > 5000: tipa={ok_bad}  ({why_bad})")

    print("\n=== (3) soundness §3: g ≤ p en TODA traza (simulador, 200k trazas aleatorias) ===")
    progs = {
        "A2A fuel=10":          (a2a_fuel, 100000),
        "seq de 5 calls":       (Seq(Call(1000),Seq(Call(2000),Seq(Call(500),Seq(Call(3000),Call(800))))), 10000),
        "if(call|seq)":         (If(Call(5000), Seq(Call(1000),Call(1000))), 8000),
        "delegate árbol":       (parent, 5000),
        "loop anidado 3x4":     (Loop(3, Loop(4, Call(100))), 5000),
    }
    rng = random.Random(0); viol = 0; total = 0
    for name,(e,p) in progs.items():
        ok,_ = typecheck_ok(e,p); assert ok, name
        pmax = 0
        for _ in range(40000):
            g = run(e, rng); total += 1; pmax = max(pmax, g)
            if g > p: viol += 1
        print(f"  {name:22} p={p:6}  max g observado={pmax:6}  g≤p siempre: {pmax<=p}")
    print(f"\n  VIOLACIONES de g≤p en {total} trazas: {viol}   ->  {'SOUNDNESS OK' if viol==0 else 'BUG'}")
    print("\n>>> El álgebra del cálculo y la soundness §3 se sostienen numéricamente. VIVE.")
