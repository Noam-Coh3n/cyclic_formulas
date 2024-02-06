import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.FinEnum

def erase {α : Type} (a : α) : Type := {x // a ≠ x}

instance decidableNot [Decidable p] : Decidable (¬ p) :=
  dite p (isFalse ∘ not_not_intro) isTrue

instance decidableNe [DecidableEq α] : Decidable ((a : α) ≠ b) :=
  decidableNot

instance decidablePredNe [DecidableEq α] : DecidablePred (Ne (a : α)) :=
  fun _ => decidableNe

instance instFintypeErase [Fintype α] [DecidableEq α] :
  Fintype (erase (a : α)) := Subtype.fintype (Ne a)


theorem equivSubtypes (h : ∀ x, p x ↔ q x): Subtype p ≃ Subtype q :=
  Equiv.subtypeEquiv (Equiv.refl _) (by simp_all)

theorem rangeErase {a : α} (f : α ≃ Fin (n+1)) :
  ↑(Set.range (fun (x : erase a) => f x.val)) ≃ erase (f a) :=
    equivSubtypes fun y => ⟨
    (match . with | ⟨⟨ev, ep⟩, prf⟩ => by aesop),
    (fun _ => ⟨⟨f.symm y, by_contra (fun _ => by simp_all)⟩, by simp⟩)
    ⟩

@[simps]
theorem permFin (m : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  let f := fun k => if k = m
    then Fin.last n
  else if k = Fin.last n
    then m
  else k
  ⟨f, f, fun _ => by aesop, fun _ => by aesop⟩

theorem permFinIdem {m x : Fin (n + 1)}: (permFin m) ((permFin m) x) = x :=
  by aesop

theorem permM {m : Fin (n + 1)} : (permFin m) m = Fin.last n :=
  by aesop

theorem permLast {m : Fin (n + 1)} :
  (permFin m) (Fin.last n) = m := by aesop

theorem finEraseLast: erase (Fin.last n) ≃ Fin (n) := ⟨
  fun ⟨m, _⟩ => Fin.castLT m (Fin.val_lt_last (by aesop)),
  fun ⟨m, LTn⟩ => ⟨m, by_contra <|
     fun a => by
     have h₁:= (Fin.veq_of_eq (not_ne_iff.mp a))
     have h₂ : n = m := (Eq.trans (by simp) h₁).trans (by simp [Nat.lt_succ_of_lt LTn])
     apply ne_of_lt LTn; exact h₂.symm⟩,
  fun _ => by aesop,
  fun _ => by aesop
⟩

theorem eraseEquivFin [DecidableEq α] {b : α} (d : b ≠ a) (f : α ≃ Fin (n+1)) :
  erase a ≃ Fin n := sorry

-- theorem eraseEquivFin [DecidableEq α] {b : α} (d : b ≠ a) (f : α ≃ Fin (n+1)) :
--   erase a ≃ Fin n := ((Equiv.ofLeftInverse' (fun (x : erase a) => f x.val)
--   (fun k => dite (a = f.invFun k)
--     (fun _ => ⟨b, d.symm⟩)
--     (⟨f.invFun k, .⟩))
--   fun ⟨x, p⟩ => by aesop).trans
--   (rangeErase f)).trans <| (Equiv.subtypeEquiv (permFin (f a)) (fun y =>
--     not_iff_not.mpr (Iff.intro
--       (by simp [.])
--       (fun yl => Eq.trans (yl ▸ permLast.symm) permFinIdem)))).trans
--     finEraseLast


lemma cardErase [Fintype α] [DecidableEq α] {a : α} :
  Fintype.card (erase a) = Fintype.card α - 1 := by simp [erase]

instance finEnumErase [FinEnum α] : FinEnum (erase (a : α)) :=
  FinEnum.Subtype.finEnum (Ne a)