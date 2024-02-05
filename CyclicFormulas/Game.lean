-- import CyclicFormulas.C2CF
-- import CyclicFormulas.Formula

-- structure Game where
--   𝔐 : Model
--   𝔾 : C2CF
--   decS   : DecidableEq 𝔐.S
--   decV   : DecidableEq 𝔾.V
--   decAdj : DecidableRel 𝔾.Adj
--   decR   : ∀n, DecidableRel (𝔐.R n)

-- instance {ℰ : Game} : DecidableEq ℰ.𝔾.V := ℰ.decV
-- instance {ℰ : Game} : DecidableEq ℰ.𝔐.S := ℰ.decS
-- instance {ℰ : Game} : DecidableRel ℰ.𝔾.Adj := ℰ.decAdj
-- instance {ℰ : Game} : DecidableRel (ℰ.𝔐.R n) := ℰ.decR n

-- @[simp]
-- abbrev Pos (ℰ : Game) : Type := ℰ.𝔾.V × ℰ.𝔐

-- open Label

-- @[simp]
-- def valid : Pos ℰ → Pos ℰ → Bool
-- | (v,s), (w,t) => match ℓ : ℰ.𝔾.L v with
--   | prop  _    => False
--   | nprop _    => False
--   | .and       => ℰ.𝔾.Adj v w && Decidable.decide (s = t)
--   | .or        => ℰ.𝔾.Adj v w ∧ s = t
--   | dim_atom n => w = ℰ.𝔾.prg_succ v (prg_dim ℓ) ∧ ℰ.𝔐.R n s t
--   | box_atom n => w = ℰ.𝔾.prg_succ v (prg_box ℓ) ∧ ℰ.𝔐.R n s t

-- -- let ℓ := ℰ.𝔾.L v
-- --   if Label.lit ℓ
-- --     then False
-- --   else if p : Label.prg ℓ
-- --     then w = ℰ.𝔾.prg_succ v p ∧ ℰ.𝔐.R s t
-- --   else
-- --     ℰ.𝔾.Adj v w ∧ s = t

-- @[simp]
-- abbrev Strat (ℰ : Game) : Type :=
--   {σ : Pos ℰ → Option (Pos ℰ) // ∀p, Option.all (valid p) (σ p)}

-- structure iGame extends Game where
--   pos : Pos toGame
--   log : List (Pos toGame) := []

-- namespace iGame

-- instance : Coe iGame Game := ⟨toGame⟩

-- @[simp]
-- def init (ℰ : Game) (s : ℰ.𝔐) : iGame where
--   toGame := ℰ
--   pos    := (ℰ.𝔾.vI, s)

-- @[simp]
-- def step (ℰ : iGame) (σ : Strat ℰ) : iGame :=
--   if let some move := σ.val ℰ.pos then
--     ⟨ℰ, move, move :: ℰ.log⟩
--   else
--     ℰ

-- end iGame