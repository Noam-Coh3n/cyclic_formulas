import CyclicFormulas.Dual
import CyclicFormulas.Formula
import CyclicFormulas.Erase

-- set_option pp.all false
-- set_option pp.beta true
-- set_option pp.coercions false

-- set_option maxHeartbeats 0

open Sum
open C2CP
open C2CF

@[simp]
def G_p (n : Nat) : C2CF where
  V       := Fin 1
  E _ _   := False
  L _     := .prop n
  Ω _     := .o
  vI      := 0
  count   := Equiv.refl _

  lit_no_succ _ _ _       := not_false
  succ _                  := none
  prg_succ_unique _ _ _   := False.elim
  colouring               := (forall_const _).mpr trivial

  -- cycles_mono _
  -- | .base a     => False.elim a
  -- | .cons _ a _ => False.elim a

@[simp]
def G_np (n : Nat) : C2CF :=
  .dual (G_p n)

open Sum3

@[simp]
def G_or (Gφ Gψ : C2CF) : C2CF where
  V := Fin 1 ⊕ Gφ ⊕ Gψ

  E
  | in₀ _, in₁ w => w = Gφ.vI
  | in₀ _, in₂ w => w = Gψ.vI
  | in₁ v, in₁ w => Gφ.E v w
  | in₂ v, in₂ w => Gψ.E v w
  | _, _         => False

  L
  | in₀ _ => Label.or
  | in₁ x => Gφ.L x
  | in₂ y => Gψ.L y

  Ω
  | in₀ _ => Colour.o
  | in₁ x => Gφ.Ω x
  | in₂ y => Gψ.Ω y

  vI := in₀ 0

  lit_no_succ := by
    rintro (z | ⟨vl | vr⟩) p (z' | ⟨wl | wr⟩)
    <;> simp_all
    . apply Gφ.lit_no_succ vl p
    . apply Gψ.lit_no_succ vr p

  count := equivFinCardSum (Equiv.refl <| Fin 1) <| equivFinCardSum Gφ.count Gψ.count

  E_dec
  | in₀ _, in₁ _ => decEq ..
  | in₀ _, in₂ _ => decEq ..
  | in₁ _, in₁ _ => Gφ.E_dec ..
  | in₂ _, in₂ _ => Gψ.E_dec ..
  | in₀ _, in₀ _ => isFalse not_false
  | in₁ _, in₀ _ => isFalse not_false
  | in₁ _, in₂ _ => isFalse not_false
  | in₂ _, in₀ _ => isFalse not_false
  | in₂ _, in₁ _ => isFalse not_false

  succ
  | in₀ _ => none
  | in₁ v => .map in₁ <| Gφ.succ v
  | in₂ v => .map in₂ <| Gψ.succ v

  prg_succ_unique
  | in₁ v, p, in₁ w => fun a => (congr_arg _ (Gφ.prg_succ_unique v p w a)).trans Option.map_coe
  | in₂ v, p, in₂ w => fun a => (congr_arg _ (Gψ.prg_succ_unique v p w a)).trans Option.map_coe
  | in₁ _, _, in₀ _ => False.elim
  | in₂ _, _, in₀ _ => False.elim
  | in₁ _, _, in₂ _ => False.elim
  | in₂ _, _, in₁ _ => False.elim

  colouring
  | in₀ _ => trivial
  | in₁ v => Gφ.colouring v
  | in₂ v => Gψ.colouring v

@[simp]
def G_and (Gφ Gψ : C2CF) : C2CF := .dual (G_or (.dual Gφ) (.dual Gψ))

@[simp]
def G_dim (Hα : C2CP) (Gφ : C2CF) : C2CF := sorry

@[simp]
def G_box (Hα : C2CP) (Gφ : C2CF) : C2CF := .dual (G_dim Hα (.dual Gφ))

@[simp]
def H_A (n : Nat) : C2CP where
  V := Bool
  E := (. && !.)
  L := (bif . then .dim_atom n else .prop 0)
  Ω _ := .o
  vI := true
  vF := false

  count := boolEquivFin
  succ := (bif . then some false else none)

@[simp]
def H_comp (Hα Hβ : C2CP) : C2CP := sorry


def H_union (Hα Hβ : C2CP) : C2CP where
  V := erase (in₂ Hβ.vF : Fin 1 ⊕ Hα ⊕ Hβ)

  E
  | ⟨in₀ _, _⟩, ⟨in₁ w, _⟩ => w = Hα.vI
  | ⟨in₀ _, _⟩, ⟨in₂ w, _⟩ => w = Hβ.vI
  | ⟨in₁ v, _⟩, ⟨in₁ w, _⟩ => Hα.E v w
  | ⟨in₂ v, _⟩, ⟨in₂ w, _⟩ => Hβ.E v w
  | ⟨in₂ v, _⟩, ⟨in₁ w, _⟩ => Hβ.E v Hβ.vF ∧ w = Hα.vF
  | _, _ => False

  E_dec
  | ⟨in₀ _, _⟩, ⟨in₀ _, _⟩ => decidableFalse
  | ⟨in₀ _, _⟩, ⟨in₁ w, _⟩ => decEq ..
  | ⟨in₀ _, _⟩, ⟨in₂ w, _⟩ => decEq ..
  | ⟨in₁ _, _⟩, ⟨in₀ _, _⟩ => decidableFalse
  | ⟨in₁ v, _⟩, ⟨in₁ w, _⟩ => Hα.E_dec ..
  | ⟨in₁ _, _⟩, ⟨in₂ _, _⟩ => decidableFalse
  | ⟨in₂ _, _⟩, ⟨in₀ _, _⟩ => decidableFalse
  | ⟨in₂ v, _⟩, ⟨in₁ w, _⟩ => @And.decidable (Hβ.E v Hβ.vF) (w = Hα.vF) (Hβ.E_dec v Hβ.vF) (decEq w Hα.vF)
  | ⟨in₂ v, _⟩, ⟨in₂ w, _⟩ => Hβ.E_dec ..

  L
  | ⟨in₀ _, _⟩ => .or
  | ⟨in₁ v, _⟩ => Hα.L v
  | ⟨in₂ v, _⟩ => Hβ.L v

  Ω
  | ⟨in₀ _, _⟩ => .o
  | ⟨in₁ v, _⟩ => Hα.Ω v
  | ⟨in₂ v, _⟩ => Hβ.Ω v

  succ
  | ⟨in₀ _, _⟩ => none
  | ⟨in₁ v, _⟩ => (fun x => ⟨in₁ x, by simp⟩) <$> Hα.succ v
  | ⟨in₂ v, _⟩ => match Hβ.succ v with
    | none => none
    | some w => dite (Hβ.vF ≠ w)
      (some ⟨in₂ w, by simp [.]⟩)
      (fun _ => some ⟨in₁ Hα.vF, by simp⟩)

  vI := ⟨in₀ 0, inr_ne_inl⟩
  vF := ⟨in₁ Hα.vF, by simp [in₂, in₁, ne_eq, inr.injEq, not_false_eq_true]⟩

  count := sorry

  -- count := Equiv.trans (@FinEnum.equiv (erase (in₂ Hβ.vF : Fin 1 ⊕ Hα ⊕ Hβ)) <| @FinEnum.Subtype.finEnum _ (FinEnum.ofEquiv _ (equivFinCardSum3 (Equiv.refl <| Fin 1) Hα.count Hβ.count)) (in₂ Hβ.vF ≠ .) _) (Equiv.cast (congr_arg Fin (@cardFinTypeEnum (erase _) instFintypeErase finEnumErase)))

  -- count := (@eraseEquivFin (Fin 1 ⊕ Hα ⊕ Hβ) (in₂ Hβ.vF) (Fintype.card (erase (in₂ Hβ.vF))) _ (inl 0) (inl_ne_inr) (Equiv.trans (equivFinCardSum3 (Equiv.refl (Fin 1)) Hα.count Hβ.count) (Equiv.cast (congr_arg Fin _))))
  -- count := equivFinCardSum3 (Equiv.refl <| Fin 1) (Hα.count) <|
  --     (eraseEquivFin Hβ.i_ne_f
  --       (Equiv.trans (Hβ.count) <| Equiv.cast
  --         (congr_arg _ ((Nat.succ_pred Fintype.card_ne_zero).symm)))
  --     ).trans <| Equiv.cast <| congr_arg Fin (by simp; rfl)trans <| Equiv.cast <| congr_arg Fin (by simp; rfl)



def H_star (Hα : C2CP) : C2CP where
  V := Fin 1 ⊕ Hα

  E
  | inl _,  _     => False
  | inr v, inl _ => v = Hα.vF
  | inr v, inr w => (v = Hα.vF ∧ w = Hα.vI) ∨ Hα.E v w

  E_dec
  | inl _,  _     => decidableFalse
  | inr v, inl _ => decEq ..
  | inr v, inr w => Or.decidable

  L
  | inl _ => .prop 0
  | inr v => if v = Hα.vF then .or else Hα.L v

  Ω
  | inl _ => .o
  | inr v => if Hα.connect v Hα.vF then .μ else Hα.Ω v

  vI := inr Hα.vF
  vF := inl 0
  i_ne_f := inr_ne_inl

  count := equivFinCardSum (Equiv.refl <| Fin 1) Hα.count

  lit_no_succ
  | inl _, _, _ => not_false
  | inr v, p, w => by
    by_contra a
    cases w
    . simp_all only [Label.lit, ite_true]
    . simp at a
      apply @by_cases (v = Hα.vF) <;> intros <;> simp_all [Hα.lit_no_succ]

  succ
  | inl _ => none
  | inr v => inr <$> Hα.succ v

  prg_succ_unique
  | inr v, p, inl w => by intro; simp_all only [Label.prg, ite_true]
  | inr v, p, inr w => if v_eq_f : v = Hα.vF
    then by simp_all
    else by simp_all [Hα.prg_succ_unique v _ w]

  colouring := sorry -- Need indhyp here

@[simp]
def H_test (Gφ : C2CF) : C2CP where
  V := Bool ⊕ Gφ

  E
  | inl v, inl w => v && !w
  | inl v, inr w => v && w = Gφ.vI
  | inr _, inl _ => False
  | inr v, inr w => Gφ.E v w

  E_dec
  | inl _, inl _ => decEq ..
  | inl _, inr _ => decEq ..
  | inr _, inl _ => decidableFalse
  | inr v, inr w => Gφ.E_dec v w

  L
  | inl true  => .and
  | inl false => .prop 0
  | inr v     => Gφ.L v

  Ω
  | inl _ => .o
  | inr v => Gφ.Ω v

  vI := inl true
  vF := inl false
  i_ne_f := Function.Injective.ne inl_injective Bool.noConfusion

  count := equivFinCardSum boolEquivFin Gφ.count

  lit_no_succ := by simp_all [Gφ.lit_no_succ]

  succ
  | inl true  => some <|.inl false
  | inl false => none
  | inr v     => inr <$> Gφ.succ v

  prg_succ_unique
  | inr v, p, inr w => fun a => (congr_arg _ (Gφ.prg_succ_unique v p w a)).trans Option.map_coe
  | inr _, _, inl _ => False.elim

  colouring
  | .inl true => trivial
  | .inl false => trivial
  | .inr v => Gφ.colouring v

mutual
  def ToC2CP : Program → C2CP
  | .atom n    => H_A n
  | .comp α β  => H_comp  (ToC2CP α) (ToC2CP β)
  | .union α β => sorry -- H_union (ToC2CP α) (ToC2CP β)
  | .star α    => H_star  (ToC2CP α)
  | .test φ    => H_test  (ToC2CF φ)

  def ToC2CF : Formula → C2CF
  | .prop  n => G_p n
  | .nprop n => G_np n
  | .or  φ ψ => G_or  (ToC2CF φ) (ToC2CF ψ)
  | .and φ ψ => G_and (ToC2CF φ) (ToC2CF ψ)
  | .dim α φ => G_dim (ToC2CP α) (ToC2CF φ)
  | .box α φ => G_box (ToC2CP α) (ToC2CF φ)
end
-- termination_by
--   ToC2CP π => sizeOf π
--   ToC2CF φ => sizeOf φ