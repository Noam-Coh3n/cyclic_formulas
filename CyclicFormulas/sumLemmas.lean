import Std.Data.Sum.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.FinEnum

-- set_option pp.beta true

@[simp]
def const {α β : Type} (b : β) : α → β := fun _ => b

@[simp]
def const₂ {α β γ : Type} (c : γ) : α → β → γ := fun _ _ => c

namespace Sum

  instance instDecidablePredElim [dp : DecidablePred p] [dq : DecidablePred q]
    : DecidablePred (Sum.elim p q) := (Sum.casesOn . dp dq)

  @[simp]
  protected def elim_rel
    (raa : α → α → Prop)
    (rab : α → β → Prop)
    (rba : β → α → Prop)
    (rbb : β → β → Prop) :
      α ⊕ β → α ⊕ β → Prop :=
    Sum.elim  (fun a => Sum.elim (raa a) (rab a))
              (fun b => Sum.elim (rba b) (rbb b))

  instance instDecidableElimRel
    {rab : α → β → Prop}
    {rba : β → α → Prop}
    [daa : DecidableRel raa]
    [dab : ∀ (a : α) (b : β), Decidable (rab a b)]
    [dba : ∀ (b : β) (a : α), Decidable (rba b a)]
    [dbb : DecidableRel rbb] :
      DecidableRel (Sum.elim_rel raa rab rba rbb)
    | inl _, inl _ => daa ..
    | inl _, inr _ => dab ..
    | inr _, inl _ => dba ..
    | inr _, inr _ => dbb ..

  instance instDecidableLiftRel [DecidableRel r] [DecidableRel s] :
    DecidableRel (Sum.LiftRel r s)
    | inl _, inl _ => decidable_of_iff' _ liftRel_inl_inl
    | inr _, inr _ => decidable_of_iff' _ liftRel_inr_inr
    | inl _, inr _ => isFalse not_liftRel_inl_inr
    | inr _, inl _ => isFalse not_liftRel_inr_inl

  def equivFinSum (A : α ≃ Fin n) (B : β ≃ Fin m) : α ⊕ β ≃ Fin (n + m) :=
    (Equiv.sumCongr A B).trans finSumFinEquiv

  def equivFinCardSum [Fintype α] [Fintype β]
    (A : α ≃ Fin (Fintype.card α)) (B : β ≃ Fin (Fintype.card β)) :
      α ⊕ β ≃ Fin (Fintype.card (α ⊕ β)) :=
    (equivFinSum A B).trans (finCongr Fintype.card_sum.symm)

end Sum

def boolEquivFin : Bool ≃ Fin 2 :=
  (FinEnum.ofList [true, false] (by simp)).2

@[simp]
instance instUnionRelation {α β : Type _}: Union (α → β → Prop) where
  union r s x y := r x y ∨ s x y

@[simp]
instance instUnionPredicate {α : Type _}: Union (α → Prop) where
  union p q x := p x ∨ q x

@[simp]
instance instInterPredicate {α : Type _}: Inter (α → Prop) where
  inter p q x := p x ∧ q x

@[simp]
instance instSingletonPred : Singleton α (α → Prop) := ⟨(Eq .)⟩

@[simp]
instance instInsertPred : Insert α (α → Prop) := ⟨fun a p => Eq a ∪ p⟩

@[simp]
instance instEmptyPred {α : Type} : EmptyCollection (α → Prop)
  := ⟨fun _ => False⟩

@[simp]
instance instEmptyRel {α β : Type} : EmptyCollection (α → β → Prop)
  := ⟨fun _ _ => False⟩

@[simp]
instance instDecSingletonPred {a : α} [DecidableEq α] : DecidablePred {a} := decEq a

@[simp]
instance instDecInsertPred {a : α} [DecidableEq α] [DecidablePred p] :
  DecidablePred (insert a p) := fun _ => Or.decidable

@[simp]
instance instDecEmptyPred :
  DecidablePred (∅ : α → Prop) := const decidableFalse

-- @[simp]
-- instance instDecRelEmpty :
--   DecidableRel (∅ : α → α → Prop) := const₂ decidableFalse

@[simp]
instance instDecPredEmptyRel :
  (a : α) → DecidablePred ((∅ : α → β → Prop) a) := const₂ decidableFalse

-- @[simp]
-- instance instDecEmptyRel :
--   (a : α) → (b : β) → Decidable (∅ ) := const₂ decidableFalse

instance Quotient.fintype' [Fintype α] (s : Setoid α) [DecidableRel s.r]
  : Fintype (Quotient s) := .ofSurjective .mk'' (Quot.inductionOn . (⟨., rfl⟩))

@[simp]
def contract (a b : α) : α → α → Prop :=
  fun x y => (x = y) ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)

@[simp, refl]
theorem contract.refl (x : α) : contract a b x x := by simp

@[simp]
theorem contract.rfl : contract a b x x := by simp

@[simp, symm]
theorem contract.symm : contract a b x y → contract a b y x := by
  rintro (_ | _ | _) <;> simp_all

@[simp, symm]
theorem contract.trans : contract a b x y → contract a b y z → contract a b x z
  := by rintro (_ | _ | _) (_ | _ | _) <;> simp_all

@[simp, simps]
def contractSetoid (a b : α) : Setoid α := ⟨contract a b, ⟨.refl, .symm, .trans⟩⟩

instance [DecidableEq α] {a b : α} :
  DecidableRel (contractSetoid a b).r := fun _ _ => Or.decidable

theorem contractDistinctEquiv [A : Fintype α] [DecidableEq α] (hd : a ≠ b) :
  Quotient (contractSetoid a b) ≃ A.elems.erase b := ⟨
    Quot.lift (fun x => dite (x = b)
      (fun _ => ⟨a, Finset.mem_erase_of_ne_of_mem hd <| A.complete a⟩)
      (⟨x, Finset.mem_erase_of_ne_of_mem . <| A.complete x⟩)) (by aesop),
    fun x => Quot.mk _ x.val,
    Quot.ind (fun x => if h : x = b
      then by apply Quot.sound; simp_all [dite_true]
      else by simp_all only [contractSetoid, dite_false]),
    by simp_all [Function.RightInverse, Function.LeftInverse]
  ⟩

theorem fintypeEquivElems [A : Fintype α] : A.elems ≃ α :=
  ⟨(.), (⟨., A.complete _⟩), fun _ => rfl, fun _ => rfl⟩

theorem cardContractDistinct {a b : α} [Fintype α] [DecidableEq α] (hd : a ≠ b):
  Fintype.card (Quotient (contractSetoid a b)) = (Fintype.card α) - 1 :=
    sorry

theorem contractDistinctEquivFin {α : Type} [A : Fintype α] [DecidableEq α] {a b : α} (hd : a ≠ b) (f : α ≃ Fin (Fintype.card α)) :
  Quotient (contractSetoid a b) ≃ Fin (Fintype.card (Quotient (contractSetoid a b))) :=
    have g : A.elems.erase b ≃ _ :=
      Equiv.ofLeftInverse' (Function.Embedding.subtype _) (fun x => if h : x = b
        then ⟨a, Finset.mem_erase_of_ne_of_mem hd <| A.complete a⟩
        else ⟨x, Finset.mem_erase_of_ne_of_mem h <| A.complete x⟩)
      (fun ⟨x, p⟩ => have h : x ≠ b := (Finset.mem_erase.mp p).left; by simp [h])
    ((contractDistinctEquiv hd).trans g).trans sorry

