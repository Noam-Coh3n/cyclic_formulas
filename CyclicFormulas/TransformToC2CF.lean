import CyclicFormulas.Dual
import CyclicFormulas.Formula
import CyclicFormulas.Erase
import Mathlib.Init.Data.Subtype.Basic
import Mathlib.Logic.Unique


-- set_option pp.all false
-- set_option pp.beta true
-- set_option pp.coercions false


open Sum
open C2CP
open C2CF

def G_p (n : Nat) : C2CF where
  V       := Fin 1
  E _ _   := False
  L _     := .prop n
  Ω _     := .o
  vI      := 0

  lit_no_succ _ _ _       := not_false
  succ _                  := none
  prg_succ_unique _ _ _   := False.elim
  colouring               := (forall_const _).mpr trivial

def G_np (n : Nat) : C2CF :=
  .dual (G_p n)

open Sum3

def G_or (Gφ Gψ : C2CF) : C2CF where
  V := Fin 1 ⊕ Gφ ⊕ Gψ
  V_fin := FinEnum.sum

  E
  | in₀ _, in₁ w => w = Gφ.vI
  | in₀ _, in₂ w => w = Gψ.vI
  | in₁ v, in₁ w => Gφ.E v w
  | in₂ v, in₂ w => Gψ.E v w
  | _, _         => False

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

  L
  | in₀ _ => Label.or
  | in₁ x => Gφ.L x
  | in₂ y => Gψ.L y

  Ω
  | in₀ _ => Colour.o
  | in₁ x => Gφ.Ω x
  | in₂ y => Gψ.Ω y

  vI := inl default

  lit_no_succ := by
    rintro (z | ⟨vl | vr⟩) p (z' | ⟨wl | wr⟩)
    <;> simp_all
    . apply Gφ.lit_no_succ vl p
    . apply Gψ.lit_no_succ vr p

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

def G_and (Gφ Gψ : C2CF) : C2CF := .dual (G_or (.dual Gφ) (.dual Gψ))

def G_dim (Hα : C2CP) (Gφ : C2CF) : C2CF where
  V := {v : Hα ⊕ Gφ // v ≠ inl Hα.vF}
  V_fin := FinEnum.Subtype.finEnum (. ≠ inl Hα.vF)

  E
  | ⟨inr v, _⟩, ⟨inr w, _⟩ => Gφ.E v w
  | ⟨inl v, _⟩, ⟨inl w, _⟩ => Hα.E v w
  | ⟨inl v, _⟩, ⟨inr w, _⟩ => Hα.E v Hα.vF ∧ w = Gφ.vI
  | ⟨inr _, _⟩, ⟨inl _, _⟩ => False

  E_dec
  | ⟨inr _, _⟩, ⟨inr _, _⟩ => Gφ.E_dec ..
  | ⟨inl _, _⟩, ⟨inl _, _⟩ => Hα.E_dec ..
  | ⟨inl _, _⟩, ⟨inr _, _⟩ => And.decidable
  | ⟨inr _, _⟩, ⟨inl _, _⟩ => decidableFalse

  L
  | ⟨inr v, _⟩ => Gφ.L v
  | ⟨inl v, _⟩ => Hα.L v

  Ω
  | ⟨inr v, _⟩ => Gφ.Ω v
  | ⟨inl v, _⟩ => Hα.Ω v

  vI := ⟨inl Hα.vI, Function.Injective.ne inl_injective Hα.i_ne_f⟩

  succ
  | ⟨inr v, _⟩ => (⟨inr ., inr_ne_inl⟩) <$> Gφ.succ v
  | ⟨inl v, _⟩ => match Hα.succ v with
    | none => none
    | some w => dite (w ≠ Hα.vF)
      (some ⟨inl w, by simp [.]⟩)
      (fun _ => some ⟨inr Gφ.vI, inr_ne_inl⟩)

  lit_no_succ
  | ⟨inr _, _⟩, p, ⟨inr _, _⟩ => Gφ.lit_no_succ _ p _
  | ⟨inl _, _⟩, p, ⟨inl _, _⟩ => Hα.lit_no_succ _ p _
  | ⟨inl _, _⟩, p, ⟨inr _, _⟩ => not_and_of_not_left _ (Hα.lit_no_succ _ p _)
  | ⟨inr _, _⟩, _, ⟨inl _, _⟩ => not_false

  colouring
  | ⟨inr v, _⟩ => Gφ.colouring v
  | ⟨inl v, _⟩ => Hα.colouring v

  prg_succ_unique
  | ⟨inr _, _⟩, p, ⟨inr _, _⟩ => (by simp [Gφ.prg_succ_unique _ p _ .])
  | ⟨inl _, _⟩, p, ⟨inl w, _⟩ => have := Hα.prg_succ_unique _ p w; by aesop
  | ⟨inl _, _⟩, p, ⟨inr _, _⟩ => have := Hα.prg_succ_unique _ p; by aesop
  | ⟨inr _, _⟩, _, ⟨inl _, _⟩ => False.elim

def G_box (Hα : C2CP) (Gφ : C2CF) : C2CF := .dual (G_dim Hα (.dual Gφ))

def H_A (n : Nat) : C2CP where
  V := Bool
  E := (. && !.)
  L := (bif . then .dim_atom n else .prop 0)
  Ω _ := .o
  vI := true
  vF := false
  i_ne_f := Bool.noConfusion
  LΩf := by simp only [cond_false, and_self]

  colouring := by simp
  succ := (bif . then some false else none)
  lit_no_succ := by simp
  prg_succ_unique := by simp

def H_comp (Hα Hβ : C2CP) : C2CP := ⟨
  G_dim Hα Hβ.toC2CF,
  ⟨inr Hβ.vF, inr_ne_inl⟩,
  by simp only [G_dim, ne_eq, Option.map_eq_map, LΩf, and_self],
  Subtype.ne_of_val_ne inl_ne_inr
⟩

def H_union (Hα Hβ : C2CP) : C2CP where
  V := {x : Fin 1 ⊕ Hα ⊕ Hβ // x ≠ in₂ Hβ.vF}
  V_fin := FinEnum.Subtype.finEnum (. ≠ in₂ Hβ.vF)

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
    | some w => dite (w ≠ Hβ.vF)
      (some ⟨in₂ w, by simp [.]⟩)
      (fun _ => some ⟨in₁ Hα.vF, by simp⟩)

  vI := ⟨in₀ 0, inl_ne_inr⟩
  vF := ⟨in₁ Hα.vF, by simp [in₂, in₁, ne_eq, inr.injEq, not_false_eq_true]⟩

  i_ne_f := @Subtype.ne_of_val_ne _ _ ⟨_, _⟩ _ inl_ne_inr

  lit_no_succ
  | ⟨in₁ v, _⟩, p, ⟨in₁ w, _⟩ => Hα.lit_no_succ v p w
  | ⟨in₂ v, _⟩, p, ⟨in₂ w, _⟩ => Hβ.lit_no_succ v p w
  | ⟨in₂ _, _⟩, p, ⟨in₁ _, _⟩ => not_and_of_not_left _ (Hβ.lit_no_succ _ p _)
  | ⟨in₁ _, _⟩, _, ⟨in₀ _, _⟩ => not_false
  | ⟨in₁ _, _⟩, _, ⟨in₂ _, _⟩ => not_false
  | ⟨in₂ _, _⟩, _, ⟨in₀ _, _⟩ => not_false

  LΩf := Hα.LΩf

  colouring
  | ⟨in₀ _, _⟩ => trivial
  | ⟨in₁ v, _⟩ => Hα.colouring v
  | ⟨in₂ v, _⟩ => Hβ.colouring v

  prg_succ_unique
  | ⟨in₁ _, _⟩, p, ⟨in₁ _, _⟩ => (by simp [Hα.prg_succ_unique _ p _ .])
  | ⟨in₂ _, _⟩, p, ⟨in₂ w, _⟩ => by have := Hβ.prg_succ_unique _ p w; aesop
  | ⟨in₂ _, _⟩, p, ⟨in₁ _, _⟩ => by have := Hβ.prg_succ_unique _ p; aesop
  | ⟨in₁ _, _⟩, _, ⟨in₀ _, _⟩ => False.elim
  | ⟨in₁ _, _⟩, _, ⟨in₂ _, _⟩ => False.elim
  | ⟨in₂ _, _⟩, _, ⟨in₀ _, _⟩ => False.elim

def H_star (Hα : C2CP) : C2CP where
  V := Fin 1 ⊕ Hα
  V_fin := FinEnum.sum

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
  LΩf := by simp only [and_self]

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

def H_test (Gφ : C2CF) : C2CP where
  V := Bool ⊕ Gφ
  V_fin := FinEnum.sum

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
  LΩf := by simp only [and_self]

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
  | .union α β => H_union (ToC2CP α) (ToC2CP β)
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