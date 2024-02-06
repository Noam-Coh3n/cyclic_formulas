import Mathlib.Logic.Function.Basic
import CyclicFormulas.Colour

inductive Label : Type
| prop     : Nat → Label
| nprop    : Nat → Label
| or       : Label
| and      : Label
| dim_atom : Nat → Label
| box_atom : Nat → Label

namespace Label

@[simp]
def lit : Label → Prop
| prop _  => True
| nprop _ => True
| _       => False

@[simp]
theorem lit_prop : lit <| prop n := trivial

@[simp]
theorem lit_nprop : lit <| nprop n := trivial

@[simp]
def prg : Label → Prop
| dim_atom _ => True
| box_atom _ => True
| _          => False

@[simp]
theorem not_prg_prop : ¬ prg (prop n) := not_false

@[simp]
theorem prg_dim (h : ℓ = dim_atom n) : prg ℓ := h ▸ trivial

@[simp]
theorem prg_box (h : ℓ = box_atom n) : prg ℓ := h ▸ trivial

@[simp]
def col_admissible : Label → Colour → Prop
| .dim_atom _, .ν => False
| .box_atom _, .μ => False
| _, _           => True

end Label