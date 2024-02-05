import CyclicFormulas.Dual
import CyclicFormulas.Formula

-- set_option pp.all false
set_option pp.beta true

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

@[simp]
def H_union (Hα Hβ : C2CP) : C2CP :=
  -- let r := Sum.elim_rel Eq (. = Hα.vF ∧ . = Hβ.vF) (. = Hβ.vF ∧ . = Hα.vF) Eq
  -- let s : Setoid _ := ⟨r, ⟨(by aesop), (by aesop), (by aesop)⟩⟩
  -- let dr : DecidableRel s.r := instDecidableElimRel
  -- let r : Hα ⊕ Hβ → Hα ⊕ Hβ → Prop := contract (inl Hα.vF) (inr Hβ.vF)
  let s : Setoid (Hα ⊕ Hβ) := contractSetoid (inl Hα.vF) (inr Hβ.vF)
{
  V := Fin 1 ⊕ Quotient s

  E := Sum.elim_rel
    ∅
    (fun _ => Quot.lift (Sum.elim (Eq Hα.vI) (Eq Hβ.vI)) (by simp [i_ne_f]))
    ∅
    <| Quot.lift₂ (Sum.elim_rel Hα.E (Hα.E . Hα.vF ∧ . = Hβ.vF)
                   (Hβ.E . Hβ.vF ∧ . = Hα.vF) Hβ.E) (by simp) (by aesop)


  L := Sum.elim (fun _ => .or) <| Quot.lift (Sum.elim Hα.L Hβ.L) (by simp)

  Ω := Sum.elim (fun _ => .o) <| Quot.lift (Sum.elim Hα.Ω Hβ.Ω) (by simp)

  -- count := equivFinCardSum (Equiv.refl <| Fin 1) <| contractDistinctEquivFin inl_ne_inr <| equivFinCardSum Hα.count Hβ.count
  count := sorry

  vI := inl 0
  vF := inr ⟦inl Hα.vF⟧
  LΩf := by simp [Quotient.mk]

  -- succ := Sum.elim (fun _ => none) <| Quot.lift (Sum.elim (fun x => if x = Hα.vF then none else Hα.succ x)) _
  lit_no_succ := sorry
  prg_succ_unique := sorry
  colouring := sorry
}


@[simp]
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
  @[simp]
  def ToC2CP : Program → C2CP
  | .atom n    => H_A n
  | .comp α β  => H_comp  (ToC2CP α) (ToC2CP β)
  | .union α β => H_union (ToC2CP α) (ToC2CP β)
  | .star α    => H_star  (ToC2CP α)
  | .test φ    => H_test  (ToC2CF φ)

  @[simp]
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