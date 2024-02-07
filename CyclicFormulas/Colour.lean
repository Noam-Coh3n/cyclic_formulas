import Mathlib.Init.Set

inductive Colour : Type
| o : Colour
| μ : Colour
| ν : Colour

namespace Colour

def repr : Colour → Lean.Format
| o => "o"
| μ => "μ"
| ν => "ν"

instance : Repr Colour := ⟨fun v _ => repr v⟩

@[simp]
def mono {V} (Ω : V → Colour) (s : List V) : Prop :=
  (∀ v ∈ s, Ω v = μ) ∨ (∀ v ∈ s, Ω v = ν)

end Colour