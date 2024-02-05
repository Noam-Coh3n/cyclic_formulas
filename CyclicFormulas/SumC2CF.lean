import CyclicFormulas.C2CF

open Sum Graph Colour

variable {G₁ G₂ : Graph}

@[simp]
def walk_toLeft : (G₁ ⊎ G₂).Walk (.inl s) (.inl t) → G₁.Walk s t
| .base h   => .base (liftRel_inl_inl.mp h)
| .cons (inl v) h r => .cons v (liftRel_inl_inl.mp h) (walk_toLeft r)

@[simp]
def walk_toRight : (G₁ ⊎ G₂).Walk (.inr s) (.inr t) → G₂.Walk s t
| .base h   => .base (liftRel_inr_inr.mp h)
| .cons (inr v) h r => .cons v (liftRel_inr_inr.mp h) (walk_toRight r)

theorem walk_toLeft_cong : ∀ (W : (G₁ ⊎ G₂).Walk (inl s) (inl t)),
                             (walk_toLeft W).support.map inl = W.support
| .base h => rfl
| .cons (inl v) h r => by
  simp [List.map, Walk.support, walk_toLeft, walk_toLeft_cong r]

theorem walk_toRight_cong : ∀ W : (G₁ ⊎ G₂).Walk (inr s) (inr t),
                              (walk_toRight W).support.map inr = W.support
| .base h => rfl
| .cons (inr v) h r => by
  simp [List.map, Walk.support, walk_toRight, walk_toRight_cong r]

-- Disjoint union of 𝔾₁ and 𝔾₂. Initial node is the one from 𝔾₁
def C2CF.Sum (𝔾₁ 𝔾₂ : C2CF) : C2CF where
  toGraph := 𝔾₁ ⊎ 𝔾₂
  L   := Sum.elim 𝔾₁.L 𝔾₂.L
  Ω   := Sum.elim 𝔾₁.Ω 𝔾₂.Ω
  vI  := inl 𝔾₁.vI

  lit_no_succ
  | inl _, _, inr _ => not_liftRel_inl_inr
  | inr _, _, inl _ => not_liftRel_inr_inl
  | inl v, l, inl w => liftRel_inl_inl.mp.mt (𝔾₁.lit_no_succ v l w)
  | inr v, l, inr w => liftRel_inr_inr.mp.mt (𝔾₂.lit_no_succ v l w)

  succ
  | inl v => inl <$> 𝔾₁.succ v
  | inr v => inr <$> 𝔾₂.succ v


  prg_succ_unique
    | inl v, p, inl w => fun a => (congr_arg _ (𝔾₁.prg_succ_unique v p w (liftRel_inl_inl.mp a))).trans Option.map_coe
    | inr v, p, inr w => fun a => (congr_arg _ (𝔾₂.prg_succ_unique v p w (liftRel_inr_inr.mp a))).trans Option.map_coe
    | inl _, _, inr _ => False.elim ∘ not_liftRel_inl_inr
    | inr _, _, inl _ => False.elim ∘ not_liftRel_inr_inl

  colouring
  | inl v => 𝔾₁.colouring v
  | inr v => 𝔾₂.colouring v

  -- cycles_mono v C := by
  --   rcases v with vl | vr
  --   . let C' := walk_toLeft C
  --     have : mono 𝔾₁.Ω (C'.support) := 𝔾₁.cycles_mono vl C'
  --     simp_all [← walk_toLeft_cong C, mono]
  --   . let C' := walk_toRight C
  --     have : mono 𝔾₂.Ω (C'.support) := 𝔾₂.cycles_mono vr C'
  --     simp_all [← walk_toRight_cong C, mono]
