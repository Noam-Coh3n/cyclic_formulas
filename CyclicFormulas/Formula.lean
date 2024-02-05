import Mathlib.Logic.Relation

mutual
  inductive Formula : Type
  | prop  : Nat → Formula
  | nprop : Nat → Formula
  | or    : Formula → Formula → Formula
  | and   : Formula → Formula → Formula
  | dim   : Program → Formula → Formula
  | box   : Program → Formula → Formula

  inductive Program : Type
  | atom  : Nat → Program
  | comp  : Program → Program → Program
  | union : Program → Program → Program
  | star  : Program → Program
  | test  : Formula → Program
end

structure Model where
  S : Type
  V : Nat → S → Prop
  R : Nat → S → S → Prop

instance : CoeSort Model Type := ⟨Model.S⟩

-- namespace Union

-- instance instUnionRelation {α β : Type _}: Union (α → β → Prop) where
--   union r s x y := r x y ∨ s x y

-- instance instUnionPredicate {α : Type _}: Union (α → Prop) where
--   union p q x := p x ∨ q x

-- instance instInterPredicate {α : Type _}: Inter (α → Prop) where
--   inter p q x := p x ∧ q x

-- end Union

-- mutual
--   -- Need s here, see https://github.com/leanprover/lean4/issues/2883 (bug)
--   def rel {𝔐 : Model} : Program → 𝔐.S → 𝔐.S → Prop
--   | .atom  n,     s   => 𝔐.R n s
--   | .comp  π₁ π₂, s   => Relation.Comp (rel π₁) (rel π₂) s
--   | .union π₁ π₂, s   => (rel π₁ ∪ rel π₂) s
--   | .star  π,     s   => Relation.ReflTransGen (rel π) s
--   | .test  φ,     s   => Eq s ∩ truth φ

--   def truth {𝔐 : Model} : Formula → 𝔐.S → Prop
--   | .prop  n => 𝔐.V n
--   | .nprop n => Not ∘ 𝔐.V n
--   | .or  φ ψ => truth φ ∪ truth ψ
--   | .and φ ψ => truth φ ∩ truth ψ
--   | .dim π φ => fun s => ∃ t, rel π s t ∧ truth φ t
--   | .box π φ => fun s => ∀ t, rel π s t → truth φ t
-- end