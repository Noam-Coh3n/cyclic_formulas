import Mathlib.Data.FinEnum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin

instance FinEnumBool : FinEnum Bool := FinEnum.ofList [true, false] (by simp)

instance instUnionRelation {α β : Type _}: Union (α → β → Prop) where
  union r s x y := r x y ∨ s x y

instance instUnionPredicate {α : Type _}: Union (α → Prop) where
  union p q x := p x ∨ q x

instance instInterPredicate {α : Type _}: Inter (α → Prop) where
  inter p q x := p x ∧ q x

instance instSingletonPred : Singleton α (α → Prop) := ⟨(Eq .)⟩

instance instInsertPred : Insert α (α → Prop) := ⟨fun a p => Eq a ∪ p⟩

instance instEmptyPred {α : Type} : EmptyCollection (α → Prop)
  := ⟨fun _ => False⟩

instance instEmptyRel {α β : Type} : EmptyCollection (α → β → Prop)
  := ⟨fun _ _ => False⟩

instance instDecSingletonPred {a : α} [DecidableEq α] : DecidablePred {a} := decEq a

instance instDecInsertPred {a : α} [DecidableEq α] [DecidablePred p] :
  DecidablePred (insert a p) := fun _ => Or.decidable

instance instDecEmptyPred :
  DecidablePred (∅ : α → Prop) := fun _ => decidableFalse

instance instDecPredEmptyRel :
  (a : α) → DecidablePred ((∅ : α → β → Prop) a) := fun _ _ => decidableFalse
