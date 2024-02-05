import CyclicFormulas.C2CF

namespace Colour

@[simp]
protected def dual : Colour → Colour
| o => o
| μ => ν
| ν => μ

end Colour

namespace Label

@[simp]
protected def dual : Label → Label
| prop p     => nprop p
| nprop p    => prop p
| or         => and
| and        => or
| dim_atom A => box_atom A
| box_atom A => dim_atom A

@[simp]
theorem dual_involutive : Function.Involutive Label.dual := by
  intro ℓ
  cases ℓ <;> rfl

theorem dual_admissible : ∀ ℓ c ,
  col_admissible ℓ c ↔ col_admissible (.dual ℓ) (.dual c) := by
    intro ℓ c
    cases ℓ <;> cases c <;> rfl


theorem dual_prg : ∀ ℓ, prg ℓ ↔ prg (.dual ℓ) := by
  intro ℓ
  cases ℓ <;> rfl

theorem dual_lit : ∀ ℓ, lit ℓ ↔ lit (.dual ℓ) := by
  intro ℓ
  cases ℓ <;> rfl

end Label

namespace C2CF

open Label

protected def dual (𝔾 : C2CF) : C2CF where
  toGraph := 𝔾
  L       := .dual ∘ 𝔾.L
  Ω       := .dual ∘ 𝔾.Ω
  vI      := 𝔾.vI

  lit_no_succ v := 𝔾.lit_no_succ v ∘ (dual_lit (𝔾.L v)).mpr

  succ v := 𝔾.succ v

  prg_succ_unique v p := 𝔾.prg_succ_unique v <| (dual_prg (𝔾.L v)).mpr p

  colouring v := by
    repeat rw [Function.comp_apply]
    apply (dual_admissible ..).mp
    exact 𝔾.colouring v

  -- cycles_mono v C := (𝔾.cycles_mono v C).elim
  --   (fun h => Or.inr (congrArg Colour.dual <| h . .))
  --   (fun h => Or.inl (congrArg Colour.dual <| h . .))

end C2CF