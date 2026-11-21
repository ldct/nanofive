import TweetNaCl.Salsa20Symbolic
import TweetNaCl.Salsa20Reference

/-! The checked circuit reference computes the same bytes as the concrete
word program, for every assignment of input leaves. -/
namespace TweetNaCl.Salsa20RefCert
open TinyFive Salsa20Circuit Salsa20Symbolic Salsa20Reference

def algebra (a : Arena) : Ops (Option Value) where
  literal x := some (.literal x)
  alu op x y := do Salsa20Symbolic.apply a.mk false op (← x) (← y)
  aluWord op x y := do Salsa20Symbolic.apply a.mk true op (← x) (← y)
  byte x := do trunc a.mk (← x)

def ref (a : Arena) (inp key constant : Nat) : Vector (Option Value) 64 :=
  core (algebra a) (readArg a.mk) inp key constant

private def input (env : Leaves) (addr : Nat) : Word :=
  (env.argByte addr).setWidth 64

private abbrev Paired (a : Arena) (env : Leaves) :=
  {p : Option Value × Word // ∀ v, p.1 = some v → v.eval a env = p.2}

private def unary (x : Paired a env) (sym : Value → Option Value) (con : Word → Word)
    (sound : ∀ v r, sym v = some r → r.eval a env = con (v.eval a env)) :
    Paired a env :=
  ⟨(x.1.1.bind sym, con x.1.2), by
    intro r h
    obtain ⟨v, hv, hr⟩ := Option.bind_eq_some_iff.mp h
    rw [sound v r hr, x.2 v hv]⟩

private def binary (x y : Paired a env) (sym : Value → Value → Option Value)
    (con : Word → Word → Word)
    (sound : ∀ v w r, sym v w = some r → r.eval a env = con (v.eval a env) (w.eval a env)) :
    Paired a env :=
  ⟨(x.1.1.bind fun v => y.1.1.bind (sym v), con x.1.2 y.1.2), by
    intro r h
    obtain ⟨v, hv, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨w, hw, hr⟩ := Option.bind_eq_some_iff.mp h'
    rw [sound v w r hr, x.2 v hv, y.2 w hw]⟩

private def pairOps (a : Arena) (env : Leaves) : Ops (Paired a env) where
  literal x := ⟨(some (.literal x), x), fun v h => by cases h; rfl⟩
  alu op x y :=
    binary x y (Salsa20Symbolic.apply a.mk false op) (concreteOps.alu op)
      (fun _ _ _ h => apply_sound env h)
  aluWord op x y :=
    binary x y (Salsa20Symbolic.apply a.mk true op) (concreteOps.aluWord op)
      (fun _ _ _ h => apply_sound env h)
  byte x := unary x (trunc a.mk) concreteOps.byte (fun _ _ h => trunc_sound env h)

private def pairInput (a : Arena) (env : Leaves) (addr : Nat) : Paired a env :=
  ⟨(readArg a.mk addr, input env addr), by
    intro v h
    simp only [readArg, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨i, hi, rfl⟩ := h
    exact a.mk_sound env hi⟩

private def symbolicProjection (a : Arena) (env : Leaves) : Hom (pairOps a env) (algebra a) where
  toFun p := p.1.1
  literal _ := rfl
  alu _ _ _ := rfl
  aluWord _ _ _ := rfl
  byte _ := rfl

private def concreteProjection (a : Arena) (env : Leaves) : Hom (pairOps a env) concreteOps where
  toFun p := p.1.2
  literal _ := rfl
  alu _ _ _ := rfl
  aluWord _ _ _ := rfl
  byte _ := rfl

theorem ref_sound (a : Arena) (env : Leaves) (inp key constant : Nat) (i : Fin 64)
    {v : Value} (h : (ref a inp key constant)[i.val] = some v) :
    v.eval a env = (core concreteOps (fun addr => (env.argByte addr).setWidth 64)
      inp key constant)[i.val] := by
  let paired := core (pairOps a env) (pairInput a env) inp key constant
  have hs : paired[i.val].1.1 = (ref a inp key constant)[i.val] := by
    have he := map_core (symbolicProjection a env) (fun addr => show
      (symbolicProjection a env).toFun (pairInput a env addr) = readArg a.mk addr from rfl)
      inp key constant
    have hi := congrArg (fun xs : Vector (Option Value) 64 => xs[i.val]) he
    change ((core (pairOps a env) (pairInput a env) inp key constant).map
      (symbolicProjection a env).toFun)[i.val] = (ref a inp key constant)[i.val] at hi
    rw [Vector.getElem_map] at hi
    exact hi
  have hc : paired[i.val].1.2 = (core concreteOps (input env) inp key constant)[i.val] := by
    have he := map_core (concreteProjection a env) (fun addr => show
      (concreteProjection a env).toFun (pairInput a env addr) = input env addr from rfl)
      inp key constant
    have hi := congrArg (fun xs : Vector Word 64 => xs[i.val]) he
    change ((core (pairOps a env) (pairInput a env) inp key constant).map
      (concreteProjection a env).toFun)[i.val] =
        (core concreteOps (input env) inp key constant)[i.val] at hi
    rw [Vector.getElem_map] at hi
    exact hi
  exact (paired[i.val].2 v (hs.trans h)).trans hc

end TweetNaCl.Salsa20RefCert
