import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import CyclicFormulas.sumLemmas

@[ext]
structure Graph where
  V : Type
  [V_fin : FinEnum V]

  E : V → V → Prop
  [E_dec : DecidableRel E]

instance : CoeSort Graph Type := ⟨Graph.V⟩

namespace Graph

section instances
  variable {G : Graph} {u v w : G}

  instance instFinEnumGraph : FinEnum G              := G.V_fin
  instance instDecRelAdj    : DecidableRel G.E       := G.E_dec
  instance instDecPredAdj   : DecidablePred <| G.E v := G.E_dec v
  instance instDecAdj       : Decidable <| G.E v w   := G.E_dec ..
  instance instDecEqGraph   : DecidableEq G.V        := G.V_fin.decEq
end instances

section Sum
  open Sum

  @[simp]
  protected def Sum (G₁ G₂ : Graph) : Graph where
    V := G₁.V ⊕ G₂.V
    E := LiftRel G₁.E G₂.E

  infixl:80 " ⊎ " => Graph.Sum

  unif_hint (G₁ G₂ : Graph) where
    ⊢ (G₁ ⊎ G₂).V ≟ G₁.V ⊕ G₂.V

  unif_hint (G₁ G₂ : Graph) where
    ⊢ G₁.V ⊕ G₂.V ≟ (G₁ ⊎ G₂).V

end Sum

section Walk
  variable {G : Graph}

  inductive Walk {G : Graph} : G → G → Type
  | base {u v} (h : G.E u v) : G.Walk u v
  | cons {u w} v (h : G.E u v) : G.Walk v w →  G.Walk u w

  namespace Walk

  @[simp]
  def support : G.Walk u v → List G
  | Walk.base _   => [u, v]
  | Walk.cons _ _ p => u :: support p

  @[simp]
  def length : G.Walk u v → Nat :=
    @List.length G ∘ support

  @[simp]
  def supportSet (walk : G.Walk u v) : Set G :=
    {x | x ∈ walk.support}

  theorem isWalkImpTransE : (W : G.Walk x y) → (Relation.TransGen G.E) x y
  | .base h      => .single h
  | .cons _ h W' => .head h <| isWalkImpTransE W'

  end Walk
end Walk

section Connectivity
  variable {G : Graph}

  @[simp]
  def reach : G → G → Prop := Relation.ReflTransGen G.E

  @[simp]
  def connect (x y : G) := reach x y ∧ reach y x

  def connectedSetoid : Setoid G := ⟨connect, sorry⟩

  def ConnectedComponent (G : Graph) := Quotient G.connectedSetoid

  def connectedComponentMk (v : G) : ConnectedComponent G := .mk _ v

  instance instDecRelConnect : DecidableRel (@connect G) := sorry

end Connectivity



