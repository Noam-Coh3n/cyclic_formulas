-- import CyclicFormulas.Graph
-- import Mathlib.Data.List.Rotate
-- import Mathlib.Topology.LocallyFinite

-- open Function

-- namespace Graph

-- variable (G G' G'' : Graph)

-- /-- A walk is a sequence of adjacent vertices.  For vertices `u v : G`,
-- the type `walk u v` consists of all walks starting at `u` and ending at `v`.

-- We say that a walk *visits* the vertices it contains.  The set of vertices a
-- walk visits is `Graph.Walk.support`.

-- See `Graph.Walk.nil'` and `Graph.Walk.cons'` for patterns that
-- can be useful in definitions since they make the vertices explicit. -/
-- inductive Walk : G → G → Type
--   | nil {u : G} : Walk u u
--   | cons {u v w : G} (h : G.E u v) (p : Walk v w) : Walk u w
--   deriving DecidableEq
-- #align simple_graph.walk Graph.Walk

-- attribute [refl] Walk.nil

-- @[simps]
-- instance Walk.instInhabited (v : G) : Inhabited (G.Walk v v) := ⟨Walk.nil⟩
-- #align simple_graph.walk.inhabited Graph.Walk.instInhabited

-- /-- The one-edge walk associated to a pair of adjacent vertices. -/
-- @[match_pattern, reducible]
-- def Adj.toWalk {G : Graph} {u v : G} (h : G.E u v) : G.Walk u v :=
--   Walk.cons h Walk.nil
-- #align simple_graph.adj.to_walk Graph.Adj.toWalk

-- namespace Walk

-- variable {G}

-- /-- Pattern to get `Walk.nil` with the vertex as an explicit argument. -/
-- @[match_pattern]
-- abbrev nil' (u : G) : G.Walk u u := Walk.nil
-- #align simple_graph.walk.nil' Graph.Walk.nil'

-- /-- Pattern to get `Walk.cons` with the vertices as explicit arguments. -/
-- @[match_pattern]
-- abbrev cons' (u v w : G) (h : G.E u v) (p : G.Walk v w) : G.Walk u w := Walk.cons h p
-- #align simple_graph.walk.cons' Graph.Walk.cons'

-- /-- Change the endpoints of a walk using equalities. This is helpful for relaxing
-- definitional equality constraints and to be able to state otherwise difficult-to-state
-- lemmas. While this is a simple wrapper around `Eq.rec`, it gives a canonical way to write it.

-- The simp-normal form is for the `copy` to be pushed outward. That way calculations can
-- occur within the "copy context." -/
-- protected def copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : G.Walk u' v' :=
--   hu ▸ hv ▸ p
-- #align simple_graph.walk.copy Graph.Walk.copy

-- @[simp]
-- theorem copy_rfl_rfl {u v} (p : G.Walk u v) : p.copy rfl rfl = p := rfl
-- #align simple_graph.walk.copy_rfl_rfl Graph.Walk.copy_rfl_rfl

-- @[simp]
-- theorem copy_copy {u v u' v' u'' v''} (p : G.Walk u v)
--     (hu : u = u') (hv : v = v') (hu' : u' = u'') (hv' : v' = v'') :
--     (p.copy hu hv).copy hu' hv' = p.copy (hu.trans hu') (hv.trans hv') := by
--   subst_vars
--   rfl
-- #align simple_graph.walk.copy_copy Graph.Walk.copy_copy

-- @[simp]
-- theorem copy_nil {u u'} (hu : u = u') : (Walk.nil : G.Walk u u).copy hu hu = Walk.nil := by
--   subst_vars
--   rfl
-- #align simple_graph.walk.copy_nil Graph.Walk.copy_nil

-- theorem copy_cons {u v w u' w'} (h : G.E u v) (p : G.Walk v w) (hu : u = u') (hw : w = w') :
--     (Walk.cons h p).copy hu hw = Walk.cons (hu ▸ h) (p.copy rfl hw) := by
--   subst_vars
--   rfl
-- #align simple_graph.walk.copy_cons Graph.Walk.copy_cons

-- @[simp]
-- theorem cons_copy {u v w v' w'} (h : G.E u v) (p : G.Walk v' w') (hv : v' = v) (hw : w' = w) :
--     Walk.cons h (p.copy hv hw) = (Walk.cons (hv ▸ h) p).copy rfl hw := by
--   subst_vars
--   rfl
-- #align simple_graph.walk.cons_copy Graph.Walk.cons_copy

-- theorem exists_eq_cons_of_ne {u v : G} (hne : u ≠ v) :
--     ∀ (p : G.Walk u v), ∃ (w : G) (h : G.E u w) (p' : G.Walk w v), p = cons h p'
--   | nil => (hne rfl).elim
--   | cons h p' => ⟨_, h, p', rfl⟩
-- #align simple_graph.walk.exists_eq_cons_of_ne Graph.Walk.exists_eq_cons_of_ne

-- /-- The length of a walk is the number of edges/darts along it. -/
-- def length {u v : G} : G.Walk u v → ℕ
--   | nil => 0
--   | cons _ q => q.length.succ
-- #align simple_graph.walk.length Graph.Walk.length

-- /-- The concatenation of two compatible walks. -/
-- @[trans]
-- def append {u v w : G} : G.Walk u v → G.Walk v w → G.Walk u w
--   | nil, q => q
--   | cons h p, q => cons h (p.append q)
-- #align simple_graph.walk.append Graph.Walk.append

-- /-- The reversed version of `Graph.Walk.cons`, concatenating an edge to
-- the end of a walk. -/
-- def concat {u v w : G} (p : G.Walk u v) (h : G.E v w) : G.Walk u w := p.append (cons h nil)
-- #align simple_graph.walk.concat Graph.Walk.concat

-- theorem concat_eq_append {u v w : G} (p : G.Walk u v) (h : G.E v w) :
--     p.concat h = p.append (cons h nil) := rfl
-- #align simple_graph.walk.concat_eq_append Graph.Walk.concat_eq_append

-- /-- Get the `n`th vertex from a walk, where `n` is generally expected to be
-- between `0` and `p.length`, inclusive.
-- If `n` is greater than or equal to `p.length`, the result is the path's endpoint. -/
-- def getGert {u v : G} : G.Walk u v → ℕ → G
--   | nil, _ => u
--   | cons _ _, 0 => u
--   | cons _ q, n + 1 => q.getGert n
-- #align simple_graph.walk.get_vert Graph.Walk.getGert

-- @[simp]
-- theorem getGert_zero {u v} (w : G.Walk u v) : w.getGert 0 = u := by cases w <;> rfl
-- #align simple_graph.walk.get_vert_zero Graph.Walk.getGert_zero

-- theorem getGert_of_length_le {u v} (w : G.Walk u v) {i : ℕ} (hi : w.length ≤ i) :
--     w.getGert i = v := by
--   induction w generalizing i with
--   | nil => rfl
--   | cons _ _ ih =>
--     cases i
--     · cases hi
--     · exact ih (Nat.succ_le_succ_iff.1 hi)
-- #align simple_graph.walk.get_vert_of_length_le Graph.Walk.getGert_of_length_le

-- @[simp]
-- theorem getGert_length {u v} (w : G.Walk u v) : w.getGert w.length = v :=
--   w.getGert_of_length_le rfl.le
-- #align simple_graph.walk.get_vert_length Graph.Walk.getGert_length

-- theorem adj_getGert_succ {u v} (w : G.Walk u v) {i : ℕ} (hi : i < w.length) :
--     G.E (w.getGert i) (w.getGert (i + 1)) := by
--   induction w generalizing i with
--   | nil => cases hi
--   | cons hxy _ ih =>
--     cases i
--     · simp [getGert, hxy]
--     · exact ih (Nat.succ_lt_succ_iff.1 hi)
-- #align simple_graph.walk.adj_get_vert_succ Graph.Walk.adj_getGert_succ

-- @[simp]
-- theorem cons_append {u v w x : G} (h : G.E u v) (p : G.Walk v w) (q : G.Walk w x) :
--     (cons h p).append q = cons h (p.append q) := rfl
-- #align simple_graph.walk.cons_append Graph.Walk.cons_append

-- @[simp]
-- theorem cons_nil_append {u v w : G} (h : G.E u v) (p : G.Walk v w) :
--     (cons h nil).append p = cons h p := rfl
-- #align simple_graph.walk.cons_nil_append Graph.Walk.cons_nil_append

-- @[simp]
-- theorem append_nil {u v : G} (p : G.Walk u v) : p.append nil = p := by
--   induction p with
--   | nil => rfl
--   | cons _ _ ih => rw [cons_append, ih]
-- #align simple_graph.walk.append_nil Graph.Walk.append_nil

-- @[simp]
-- theorem nil_append {u v : G} (p : G.Walk u v) : nil.append p = p :=
--   rfl
-- #align simple_graph.walk.nil_append Graph.Walk.nil_append

-- theorem concat_nil {u v : G} (h : G.E u v) : nil.concat h = cons h nil := rfl
-- #align simple_graph.walk.concat_nil Graph.Walk.concat_nil

-- @[simp]
-- theorem length_nil {u : G} : (nil : G.Walk u u).length = 0 := rfl
-- #align simple_graph.walk.length_nil Graph.Walk.length_nil

-- @[simp]
-- theorem length_cons {u v w : G} (h : G.E u v) (p : G.Walk v w) :
--     (cons h p).length = p.length + 1 := rfl
-- #align simple_graph.walk.length_cons Graph.Walk.length_cons

-- @[simp]
-- theorem length_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
--     (p.copy hu hv).length = p.length := by
--   subst_vars
--   rfl
-- #align simple_graph.walk.length_copy Graph.Walk.length_copy

-- @[simp]
-- theorem length_append {u v w : G} (p : G.Walk u v) (q : G.Walk v w) :
--     (p.append q).length = p.length + q.length := by
--   induction p with
--   | nil => simp
--   | cons _ _ ih => simp [ih, add_comm, add_left_comm, add_assoc]
-- #align simple_graph.walk.length_append Graph.Walk.length_append

-- @[simp]
-- theorem length_concat {u v w : G} (p : G.Walk u v) (h : G.E v w) :
--     (p.concat h).length = p.length + 1 := length_append _ _
-- #align simple_graph.walk.length_concat Graph.Walk.length_concat


-- theorem eq_of_length_eq_zero {u v : G} : ∀ {p : G.Walk u v}, p.length = 0 → u = v
--   | nil, _ => rfl
-- #align simple_graph.walk.eq_of_length_eq_zero Graph.Walk.eq_of_length_eq_zero

-- @[simp]
-- theorem exists_length_eq_zero_iff {u v : G} : (∃ p : G.Walk u v, p.length = 0) ↔ u = v := by
--   constructor
--   · rintro ⟨p, hp⟩
--     exact eq_of_length_eq_zero hp
--   · rintro rfl
--     exact ⟨nil, rfl⟩

-- @[simp]
-- theorem length_eq_zero_iff {u : G} {p : G.Walk u u} : p.length = 0 ↔ p = nil := by cases p <;> simp

-- theorem concat_ne_nil {u v : G} (p : G.Walk u v) (h : G.E v u) : p.concat h ≠ nil := by
--   cases p <;> simp [concat]

-- /-- The `support` of a walk is the list of vertices it visits in order. -/
-- def support {u v : G} : G.Walk u v → List G
--   | nil => [u]
--   | cons _ p => u :: p.support

-- /-- The `darts` of a walk is the list of darts it visits in order. -/
-- def edges {u v : G} : G.Walk u v → List (G.Dart)
--   | nil => []
--   | cons h p => ⟨(_, _), h⟩ :: p.edges



-- @[simp]
-- theorem support_nil {u : G} : (nil : G.Walk u u).support = [u] := rfl
-- #align simple_graph.walk.support_nil Graph.Walk.support_nil

-- @[simp]
-- theorem support_cons {u v w : G} (h : G.E u v) (p : G.Walk v w) :
--     (cons h p).support = u :: p.support := rfl
-- #align simple_graph.walk.support_cons Graph.Walk.support_cons

-- @[simp]
-- theorem support_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
--     (p.copy hu hv).support = p.support := by
--   subst_vars
--   rfl
-- #align simple_graph.walk.support_copy Graph.Walk.support_copy

-- theorem support_append {u v w : G} (p : G.Walk u v) (p' : G.Walk v w) :
--     (p.append p').support = p.support ++ p'.support.tail := by
--   induction p <;> cases p' <;> simp [*]
-- #align simple_graph.walk.support_append Graph.Walk.support_append

-- @[simp]
-- theorem support_ne_nil {u v : G} (p : G.Walk u v) : p.support ≠ [] := by cases p <;> simp
-- #align simple_graph.walk.support_ne_nil Graph.Walk.support_ne_nil

-- theorem tail_support_append {u v w : G} (p : G.Walk u v) (p' : G.Walk v w) :
--     (p.append p').support.tail = p.support.tail ++ p'.support.tail := by
--   rw [support_append, List.tail_append_of_ne_nil _ _ (support_ne_nil _)]
-- #align simple_graph.walk.tail_support_append Graph.Walk.tail_support_append

-- theorem support_eq_cons {u v : G} (p : G.Walk u v) : p.support = u :: p.support.tail := by
--   cases p <;> simp
-- #align simple_graph.walk.support_eq_cons Graph.Walk.support_eq_cons

-- @[simp]
-- theorem start_mem_support {u v : G} (p : G.Walk u v) : u ∈ p.support := by cases p <;> simp
-- #align simple_graph.walk.start_mem_support Graph.Walk.start_mem_support

-- @[simp]
-- theorem end_mem_support {u v : G} (p : G.Walk u v) : v ∈ p.support := by induction p <;> simp [*]
-- #align simple_graph.walk.end_mem_support Graph.Walk.end_mem_support

-- @[simp]
-- theorem support_nonempty {u v : G} (p : G.Walk u v) : { w | w ∈ p.support }.Nonempty :=
--   ⟨u, by simp⟩
-- #align simple_graph.walk.support_nonempty Graph.Walk.support_nonempty

-- theorem mem_support_iff {u v w : G} (p : G.Walk u v) : w ∈ p.support ↔ w = u ∨ w ∈ p.support.tail :=
--   by cases p <;> simp
-- #align simple_graph.walk.mem_support_iff Graph.Walk.mem_support_iff

-- theorem mem_support_nil_iff {u v : G} : u ∈ (nil : G.Walk v v).support ↔ u = v := by simp
-- #align simple_graph.walk.mem_support_nil_iff Graph.Walk.mem_support_nil_iff

-- @[simp]
-- theorem mem_tail_support_append_iff {t u v w : G} (p : G.Walk u v) (p' : G.Walk v w) :
--     t ∈ (p.append p').support.tail ↔ t ∈ p.support.tail ∨ t ∈ p'.support.tail := by
--   rw [tail_support_append, List.mem_append]
-- #align simple_graph.walk.mem_tail_support_append_iff Graph.Walk.mem_tail_support_append_iff

-- @[simp]
-- theorem end_mem_tail_support_of_ne {u v : G} (h : u ≠ v) (p : G.Walk u v) : v ∈ p.support.tail := by
--   obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p
--   simp
-- #align simple_graph.walk.end_mem_tail_support_of_ne Graph.Walk.end_mem_tail_support_of_ne

-- @[simp, nolint unusedHavesSuffices]
-- theorem mem_support_append_iff {t u v w : G} (p : G.Walk u v) (p' : G.Walk v w) :
--     t ∈ (p.append p').support ↔ t ∈ p.support ∨ t ∈ p'.support := by
--   simp only [mem_support_iff, mem_tail_support_append_iff]
--   obtain rfl | h := eq_or_ne t v <;> obtain rfl | h' := eq_or_ne t u <;>
--     -- this `have` triggers the unusedHavesSuffices linter:
--     (try have := h'.symm) <;> simp [*]
-- #align simple_graph.walk.mem_support_append_iff Graph.Walk.mem_support_append_iff

-- @[simp]
-- theorem subset_support_append_left {G : Graph} {u v w : G}
--     (p : G.Walk u v) (q : G.Walk v w) : p.support ⊆ (p.append q).support := by
--   simp only [Walk.support_append, List.subset_append_left]

-- @[simp]
-- theorem subset_support_append_right {G : Graph} {u v w : G}
--     (p : G.Walk u v) (q : G.Walk v w) : q.support ⊆ (p.append q).support := by
--   intro h
--   simp (config := { contextual := true }) only [mem_support_append_iff, or_true_iff, imp_true_iff]
-- #align simple_graph.walk.subset_support_append_right Graph.Walk.subset_support_append_right

-- theorem coe_support {u v : G} (p : G.Walk u v) : (p.support : Multiset G) = {u} + p.support.tail :=
--   by cases p <;> rfl
-- #align simple_graph.walk.coe_support Graph.Walk.coe_support

-- theorem coe_support_append {u v w : G} (p : G.Walk u v) (p' : G.Walk v w) :
--     ((p.append p').support : Multiset G) = {u} + p.support.tail + p'.support.tail := by
--   rw [support_append, ← Multiset.coe_add, coe_support]
-- #align simple_graph.walk.coe_support_append Graph.Walk.coe_support_append

-- theorem coe_support_append' [DecidableEq G] {u v w : G} (p : G.Walk u v) (p' : G.Walk v w) :
--     ((p.append p').support : Multiset G) = p.support + p'.support - {v} := by
--   rw [support_append, ← Multiset.coe_add]
--   simp only [coe_support]
--   rw [add_comm ({v} : Multiset G)]
--   simp only [← add_assoc, add_tsub_cancel_right]
-- #align simple_graph.walk.coe_support_append' Graph.Walk.coe_support_append'

-- theorem chain_adj_support {u v w : G} (h : G.E u v) :
--     ∀ (p : G.Walk v w), List.Chain G.E u p.support
--   | nil => List.Chain.cons h List.Chain.nil
--   | cons h' p => List.Chain.cons h (chain_adj_support h' p)
-- #align simple_graph.walk.chain_adj_support Graph.Walk.chain_adj_support

-- theorem chain'_adj_support {u v : G} : ∀ (p : G.Walk u v), List.Chain' G.E p.support
--   | nil => List.Chain.nil
--   | cons h p => chain_adj_support h p
-- #align simple_graph.walk.chain'_adj_support Graph.Walk.chain'_adj_support

-- @[simp]
-- theorem edges_nil {u : G} : (nil : G.Walk u u).edges = [] := rfl
-- #align simple_graph.walk.edges_nil Graph.Walk.edges_nil

-- @[simp]
-- theorem edges_cons {u v w : G} (h : G.E u v) (p : G.Walk v w) :
--     (cons h p).edges = ⟨(u, v), h⟩ :: p.edges := rfl
-- #align simple_graph.walk.edges_cons Graph.Walk.edges_cons

-- @[simp]
-- theorem edges_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
--     (p.copy hu hv).edges = p.edges := by
--   subst_vars
--   rfl
-- #align simple_graph.walk.edges_copy Graph.Walk.edges_copy


-- @[simp]
-- theorem length_support {u v : G} (p : G.Walk u v) : p.support.length = p.length + 1 := by
--   induction p <;> simp [*]
-- #align simple_graph.walk.length_support Graph.Walk.length_support

-- /-- Predicate for the empty walk.

-- Solves the dependent type problem where `p = G.Walk.nil` typechecks
-- only if `p` has defeq endpoints. -/
-- inductive Nil : {v w : G} → G.Walk v w → Prop
--   | nil {u : G} : Nil (nil : G.Walk u u)

-- @[simp] lemma nil_nil : (nil : G.Walk u u).Nil := Nil.nil

-- @[simp] lemma not_nil_cons {h : G.E u v} {p : G.Walk v w} : ¬ (cons h p).Nil := fun.

-- instance (p : G.Walk v w) : Decidable p.Nil :=
--   match p with
--   | nil => isTrue .nil
--   | cons _ _ => isFalse fun.

-- protected lemma Nil.eq {p : G.Walk v w} : p.Nil → v = w | .nil => rfl

-- lemma not_nil_of_ne {p : G.Walk v w} : v ≠ w → ¬ p.Nil := mt Nil.eq

-- lemma nil_iff_support_eq {p : G.Walk v w} : p.Nil ↔ p.support = [v] := by
--   cases p <;> simp

-- lemma nil_iff_length_eq {p : G.Walk v w} : p.Nil ↔ p.length = 0 := by
--   cases p <;> simp

-- lemma not_nil_iff {p : G.Walk v w} :
--     ¬ p.Nil ↔ ∃ (u : G) (h : G.E v u) (q : G.Walk u w), p = cons h q := by
--   cases p <;> simp [*]

-- @[elab_as_elim]
-- def notNilRec {motive : {u w : G} → (p : G.Walk u w) → (h : ¬ p.Nil) → Sort*}
--     (cons : {u v w : G} → (h : G.E u v) → (q : G.Walk v w) → motive (cons h q) not_nil_cons)
--     (p : G.Walk u w) : (hp : ¬ p.Nil) → motive p hp :=
--   match p with
--   | nil => fun hp => absurd .nil hp
--   | .cons h q => fun _ => cons h q

-- /-- The second vertex along a non-nil walk. -/
-- def sndOfNotNil (p : G.Walk v w) (hp : ¬ p.Nil) : G :=
--   p.notNilRec (@fun _ u _ _ _ => u) hp

-- @[simp] lemma adj_sndOfNotNil {p : G.Walk v w} (hp : ¬ p.Nil) :
--     G.E v (p.sndOfNotNil hp) :=
--   p.notNilRec (fun h _ => h) hp

-- /-- The walk obtained by removing the first dart of a non-nil walk. -/
-- def tail (p : G.Walk x y) (hp : ¬ p.Nil) : G.Walk (p.sndOfNotNil hp) y :=
--   p.notNilRec (fun _ q => q) hp

-- /-- The first dart of a walk. -/
-- @[simps]
-- def firstDart (p : G.Walk v w) (hp : ¬ p.Nil) : G.Dart where
--   fst := v
--   snd := p.sndOfNotNil hp
--   is_adj := p.adj_sndOfNotNil hp

-- @[simp] lemma cons_tail_eq (p : G.Walk x y) (hp : ¬ p.Nil) :
--     cons (p.adj_sndOfNotNil hp) (p.tail hp) = p :=
--   p.notNilRec (fun _ _ => rfl) hp

-- @[simp] lemma cons_support_tail (p : G.Walk x y) (hp : ¬ p.Nil) :
--     x :: (p.tail hp).support = p.support := by
--   rw [← support_cons, cons_tail_eq]

-- @[simp] lemma length_tail_add_one {p : G.Walk x y} (hp : ¬ p.Nil) :
--     (p.tail hp).length + 1 = p.length := by
--   rw [← length_cons, cons_tail_eq]

-- @[simp] lemma nil_copy {p : G.Walk x y} (hx : x = x') (hy : y = y') :
--     (p.copy hx hy).Nil = p.Nil := by
--   subst_vars; rfl

-- /-! ### Trails, paths, circuits, cycles -/

-- /-- A *trail* is a walk with no repeating edges. -/
-- @[mk_iff isTrail_def]
-- structure IsTrail {u v : G} (p : G.Walk u v) : Prop where
--   edges_nodup : p.edges.Nodup
-- #align simple_graph.walk.is_trail Graph.Walk.IsTrail
-- #align simple_graph.walk.is_trail_def Graph.Walk.isTrail_def

-- /-- A *path* is a walk with no repeating vertices.
-- Use `simple_graph.walk.is_path.mk'` for a simpler constructor. -/
-- structure IsPath {u v : G} (p : G.Walk u v) extends IsTrail p : Prop where
--   support_nodup : p.support.Nodup
-- #align simple_graph.walk.is_path Graph.Walk.IsPath

-- -- porting note: used to use `extends to_trail : is_trail p` in structure
-- protected lemma IsPath.isTrail (h : IsPath p) : IsTrail p := h.toIsTrail
-- #align simple_graph.walk.is_path.to_trail Graph.Walk.IsPath.isTrail

-- /-- A *circuit* at `u : G` is a nonempty trail beginning and ending at `u`. -/
-- @[mk_iff isCircuit_def]
-- structure IsCircuit {u : G} (p : G.Walk u u) extends IsTrail p : Prop where
--   ne_nil : p ≠ nil
-- #align simple_graph.walk.is_circuit Graph.Walk.IsCircuit
-- #align simple_graph.walk.is_circuit_def Graph.Walk.isCircuit_def

-- -- porting note: used to use `extends to_trail : is_trail p` in structure
-- protected lemma IsCircuit.isTrail (h : IsCircuit p) : IsTrail p := h.toIsTrail
-- #align simple_graph.walk.is_circuit.to_trail Graph.Walk.IsCircuit.isTrail

-- /-- A *cycle* at `u : G` is a circuit at `u` whose only repeating vertex
-- is `u` (which appears exactly twice). -/
-- structure IsCycle {u : G} (p : G.Walk u u) extends IsCircuit p : Prop where
--   support_nodup : p.support.tail.Nodup
-- #align simple_graph.walk.is_cycle Graph.Walk.IsCycle

-- -- porting note: used to use `extends to_circuit : is_circuit p` in structure
-- protected lemma IsCycle.isCircuit (h : IsCycle p) : IsCircuit p := h.toIsCircuit
-- #align simple_graph.walk.is_cycle.to_circuit Graph.Walk.IsCycle.isCircuit

-- @[simp]
-- theorem isTrail_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
--     (p.copy hu hv).IsTrail ↔ p.IsTrail := by
--   subst_vars
--   rfl
-- #align simple_graph.walk.is_trail_copy Graph.Walk.isTrail_copy



-- @[simp]
-- theorem isPath_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
--     (p.copy hu hv).IsPath ↔ p.IsPath := by
--   subst_vars
--   rfl
-- #align simple_graph.walk.is_path_copy Graph.Walk.isPath_copy

-- @[simp]
-- theorem isCircuit_copy {u u'} (p : G.Walk u u) (hu : u = u') :
--     (p.copy hu hu).IsCircuit ↔ p.IsCircuit := by
--   subst_vars
--   rfl
-- #align simple_graph.walk.is_circuit_copy Graph.Walk.isCircuit_copy

-- theorem isCycle_def {u : G} (p : G.Walk u u) :
--     p.IsCycle ↔ p.IsTrail ∧ p ≠ nil ∧ p.support.tail.Nodup :=
--   Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩
-- #align simple_graph.walk.is_cycle_def Graph.Walk.isCycle_def

-- @[simp]
-- theorem isCycle_copy {u u'} (p : G.Walk u u) (hu : u = u') :
--     (p.copy hu hu).IsCycle ↔ p.IsCycle := by
--   subst_vars
--   rfl
-- #align simple_graph.walk.is_cycle_copy Graph.Walk.isCycle_copy

-- @[simp]
-- theorem IsTrail.nil {u : G} : (nil : G.Walk u u).IsTrail :=
--   ⟨by simp [edges]⟩
-- #align simple_graph.walk.is_trail.nil Graph.Walk.IsTrail.nil

-- theorem IsTrail.of_cons {u v w : G} {h : G.E u v} {p : G.Walk v w} :
--     (cons h p).IsTrail → p.IsTrail := by simp [isTrail_def]
-- #align simple_graph.walk.is_trail.of_cons Graph.Walk.IsTrail.of_cons

-- theorem IsPath.nil {u : G} : (nil : G.Walk u u).IsPath := by constructor <;> simp

-- @[simp]
-- theorem IsCycle.not_of_nil {u : G} : ¬(nil : G.Walk u u).IsCycle := fun h => h.ne_nil rfl
-- #align simple_graph.walk.is_cycle.not_of_nil Graph.Walk.IsCycle.not_of_nil



-- /-! ### About paths -/

-- theorem IsPath.length_lt [Fintype G] {u v : G} {p : G.Walk u v} (hp : p.IsPath) :
--     p.length < Fintype.card G := by
--   rw [Nat.lt_iff_add_one_le, ← length_support]
--   exact hp.support_nodup.length_le_card
-- #align simple_graph.walk.is_path.length_lt Graph.Walk.IsPath.length_lt


-- /-! ### Walk decompositions -/

-- section WalkDecomp

-- variable [DecidableEq G]

-- /-- Given a vertex in the support of a path, give the path up until (and including) that vertex. -/
-- def takeUntil {v w : G} : ∀ (p : G.Walk v w) (u : G), u ∈ p.support → G.Walk v u
--   | nil, u, h => by rw [mem_support_nil_iff.mp h]
--   | cons r p, u, h =>
--     if hx : v = u then
--       by subst u; exact Walk.nil
--     else
--       cons r (takeUntil p u <| by cases h; exact (hx rfl).elim; assumption)
-- #align simple_graph.walk.take_until Graph.Walk.takeUntil

-- /-- Given a vertex in the support of a path, give the path from (and including) that vertex to
-- the end. In other words, drop vertices from the front of a path until (and not including)
-- that vertex. -/
-- def dropUntil {v w : G} : ∀ (p : G.Walk v w) (u : G), u ∈ p.support → G.Walk u w
--   | nil, u, h => by rw [mem_support_nil_iff.mp h]
--   | cons r p, u, h =>
--     if hx : v = u then by
--       subst u
--       exact cons r p
--     else dropUntil p u <| by cases h; exact (hx rfl).elim; assumption
-- #align simple_graph.walk.drop_until Graph.Walk.dropUntil

-- /-- The `takeUntil` and `dropUntil` functions split a walk into two pieces.
-- The lemma `Graph.Walk.count_support_takeUntil_eq_one` specifies where this split occurs. -/
-- @[simp]
-- theorem take_spec {u v w : G} (p : G.Walk v w) (h : u ∈ p.support) :
--     (p.takeUntil u h).append (p.dropUntil u h) = p := by
--   induction p
--   · rw [mem_support_nil_iff] at h
--     subst u
--     rfl
--   · cases h
--     · simp!
--     · simp! only
--       split_ifs with h' <;> subst_vars <;> simp [*]
-- #align simple_graph.walk.take_spec Graph.Walk.take_spec

-- theorem mem_support_iff_exists_append {G : Graph} {u v w : G}
--     {p : G.Walk u v} : w ∈ p.support ↔ ∃ (q : G.Walk u w) (r : G.Walk w v), p = q.append r := by
--   classical
--   constructor
--   · exact fun h => ⟨_, _, (p.take_spec h).symm⟩
--   · rintro ⟨q, r, rfl⟩
--     simp only [mem_support_append_iff, end_mem_support, start_mem_support, or_self_iff]
-- #align simple_graph.walk.mem_support_iff_exists_append Graph.Walk.mem_support_iff_exists_append

-- @[simp]
-- theorem count_support_takeUntil_eq_one {u v w : G} (p : G.Walk v w) (h : u ∈ p.support) :
--     (p.takeUntil u h).support.count u = 1 := by
--   induction p
--   · rw [mem_support_nil_iff] at h
--     subst u
--     simp!
--   · cases h
--     · simp!
--     · simp! only
--       split_ifs with h' <;> rw [eq_comm] at h' <;> subst_vars <;> simp! [*, List.count_cons]
-- #align simple_graph.walk.count_support_take_until_eq_one Graph.Walk.count_support_takeUntil_eq_one


-- @[simp]
-- theorem takeUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
--     (h : u ∈ (p.copy hv hw).support) :
--     (p.copy hv hw).takeUntil u h = (p.takeUntil u (by subst_vars; exact h)).copy hv rfl := by
--   subst_vars
--   rfl
-- #align simple_graph.walk.take_until_copy Graph.Walk.takeUntil_copy

-- @[simp]
-- theorem dropUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
--     (h : u ∈ (p.copy hv hw).support) :
--     (p.copy hv hw).dropUntil u h = (p.dropUntil u (by subst_vars; exact h)).copy rfl hw := by
--   subst_vars
--   rfl
-- #align simple_graph.walk.drop_until_copy Graph.Walk.dropUntil_copy

-- theorem support_takeUntil_subset {u v w : G} (p : G.Walk v w) (h : u ∈ p.support) :
--     (p.takeUntil u h).support ⊆ p.support := fun x hx => by
--   rw [← take_spec p h, mem_support_append_iff]
--   exact Or.inl hx
-- #align simple_graph.walk.support_take_until_subset Graph.Walk.support_takeUntil_subset


-- theorem length_takeUntil_le {u v w : G} (p : G.Walk v w) (h : u ∈ p.support) :
--     (p.takeUntil u h).length ≤ p.length := by
--   have := congr_arg Walk.length (p.take_spec h)
--   rw [length_append] at this
--   exact Nat.le.intro this
-- #align simple_graph.walk.length_take_until_le Graph.Walk.length_takeUntil_le

-- /-- Rotate a loop walk such that it is centered at the given vertex. -/
-- def rotate {u v : G} (c : G.Walk v v) (h : u ∈ c.support) : G.Walk u u :=
--   (c.dropUntil u h).append (c.takeUntil u h)
-- #align simple_graph.walk.rotate Graph.Walk.rotate

-- @[simp]
-- theorem support_rotate {u v : G} (c : G.Walk v v) (h : u ∈ c.support) :
--     (c.rotate h).support.tail ~r c.support.tail := by
--   simp only [rotate, tail_support_append]
--   apply List.IsRotated.trans List.isRotated_append
--   rw [← tail_support_append, take_spec]
-- #align simple_graph.walk.support_rotate Graph.Walk.support_rotate

-- end WalkDecomp

-- end Walk


-- /-! ### Type of paths -/

-- /-- The type for paths between two vertices. -/
-- abbrev Path (u v : G) := { p : G.Walk u v // p.IsPath }
-- #align simple_graph.path Graph.Path

-- namespace Path

-- variable {G G'}

-- @[simp]
-- protected theorem isPath {u v : G} (p : G.Path u v) : (p : G.Walk u v).IsPath := p.property
-- #align simple_graph.path.is_path Graph.Path.isPath

-- @[simp]
-- protected theorem isTrail {u v : G} (p : G.Path u v) : (p : G.Walk u v).IsTrail :=
--   p.property.isTrail
-- #align simple_graph.path.is_trail Graph.Path.isTrail

-- /-- The length-0 path at a vertex. -/
-- @[refl, simps]
-- protected def nil {u : G} : G.Path u u :=
--   ⟨Walk.nil, Walk.IsPath.nil⟩
-- #align simple_graph.path.nil Graph.Path.nil

-- theorem count_support_eq_one [DecidableEq G] {u v w : G} {p : G.Path u v}
--     (hw : w ∈ (p : G.Walk u v).support) : (p : G.Walk u v).support.count w = 1 :=
--   List.count_eq_one_of_mem p.property.support_nodup hw
-- #align simple_graph.path.count_support_eq_one Graph.Path.count_support_eq_one

-- end Path


-- /-! ### Walks to paths -/

-- namespace Walk

-- variable {G} [DecidableEq G]

-- /-- Given a walk, produces a walk from it by bypassing subwalks between repeated vertices.
-- The result is a path, as shown in `Graph.Walk.bypass_isPath`.
-- This is packaged up in `Graph.Walk.toPath`. -/
-- def bypass {u v : G} : G.Walk u v → G.Walk u v
--   | nil => nil
--   | cons ha p =>
--     let p' := p.bypass
--     if hs : u ∈ p'.support then
--       p'.dropUntil u hs
--     else
--       cons ha p'
-- #align simple_graph.walk.bypass Graph.Walk.bypass

-- @[simp]
-- theorem bypass_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
--     (p.copy hu hv).bypass = p.bypass.copy hu hv := by
--   subst_vars
--   rfl
-- #align simple_graph.walk.bypass_copy Graph.Walk.bypass_copy

-- end Walk



-- def Reachable (u v : G) : Prop := Nonempty (G.Walk u v)

-- variable {G}

-- theorem reachable_iff_nonempty_univ {u v : G} :
--     G.Reachable u v ↔ (Set.univ : Set (G.Walk u v)).Nonempty :=
--   Set.nonempty_iff_univ_nonempty
-- #align simple_graph.reachable_iff_nonempty_univ Graph.reachable_iff_nonempty_univ

-- protected theorem Reachable.elim {p : Prop} {u v : G} (h : G.Reachable u v)
--     (hp : G.Walk u v → p) : p :=
--   Nonempty.elim h hp
-- #align simple_graph.reachable.elim Graph.Reachable.elim

-- protected theorem Walk.reachable {G : Graph} {u v : G} (p : G.Walk u v) : G.Reachable u v :=
--   ⟨p⟩
-- #align simple_graph.walk.reachable Graph.Walk.reachable

-- @[refl]
-- protected theorem Reachable.refl (u : G) : G.Reachable u u := ⟨Walk.nil⟩
-- #align simple_graph.reachable.refl Graph.Reachable.refl

-- protected theorem Reachable.rfl {u : G} : G.Reachable u u := Reachable.refl _
-- #align simple_graph.reachable.rfl Graph.Reachable.rfl

-- @[trans]
-- protected theorem Reachable.trans {u v w : G} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
--     G.Reachable u w :=
--   huv.elim fun puv => hvw.elim fun pvw => ⟨puv.append pvw⟩
-- #align simple_graph.reachable.trans Graph.Reachable.trans

-- theorem reachable_iff_reflTransGen (u v : G) :
--     G.Reachable u v ↔ Relation.ReflTransGen G.E u v := by
--   constructor
--   · rintro ⟨h⟩
--     induction h with
--     | nil => rfl
--     | cons h' _ ih => exact (Relation.ReflTransGen.single h').trans ih
--   · intro h
--     induction h with
--     | refl => rfl
--     | tail _ ha hr => exact Reachable.trans hr ⟨Walk.cons ha Walk.nil⟩
-- #align simple_graph.reachable_iff_refl_trans_gen Graph.reachable_iff_reflTransGen


-- /-! ### Walks of a given length -/

-- section WalkCounting

-- theorem set_walk_self_length_zero_eq (u : G) : {p : G.Walk u u | p.length = 0} = {Walk.nil} := by
--   ext p
--   simp
-- #align simple_graph.set_walk_self_length_zero_eq Graph.set_walk_self_length_zero_eq

-- theorem set_walk_length_zero_eq_of_ne {u v : G} (h : u ≠ v) :
--     {p : G.Walk u v | p.length = 0} = ∅ := by
--   ext p
--   simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false_iff]
--   exact fun h' => absurd (Walk.eq_of_length_eq_zero h') h
-- #align simple_graph.set_walk_length_zero_eq_of_ne Graph.set_walk_length_zero_eq_of_ne

-- theorem set_walk_length_succ_eq (u v : G) (n : ℕ) :
--     {p : G.Walk u v | p.length = n.succ} =
--       ⋃ (w : G) (h : G.E u w), Walk.cons h '' {p' : G.Walk w v | p'.length = n} := by
--   ext p
--   cases' p with _ _ w _ huw pwv
--   · simp [eq_comm]
--   · simp only [Nat.succ_eq_add_one, Set.mem_setOf_eq, Walk.length_cons, add_left_inj,
--       Set.mem_iUnion, Set.mem_image, exists_prop]
--     constructor
--     · rintro rfl
--       exact ⟨w, huw, pwv, rfl, rfl⟩
--     · rintro ⟨w, huw, pwv, rfl, rfl, rfl⟩
--       rfl
-- #align simple_graph.set_walk_length_succ_eq Graph.set_walk_length_succ_eq

-- variable (G) [DecidableEq G]

-- section LocallyFinite

-- variable [LocallyFinite G.E]

-- /-- The `Finset` of length-`n` walks from `u` to `v`.
-- This is used to give `{p : G.walk u v | p.length = n}` a `Fintype` instance, and it
-- can also be useful as a recursive description of this set when `G` is finite.

-- See `Graph.coe_finsetWalkLength_eq` for the relationship between this `Finset` and
-- the set of length-`n` walks. -/
-- def finsetWalkLength (n : ℕ) (u v : G) : Finset (G.Walk u v) :=
--   match n with
--   | 0 =>
--     if h : u = v then by
--       subst u
--       exact {Walk.nil}
--     else ∅
--   | n + 1 =>
--     Finset.univ.biUnion fun (w : G.neighborSet u) =>
--       (finsetWalkLength n w v).map ⟨fun p => Walk.cons w.property p, fun _ _ => by simp⟩
-- #align simple_graph.finset_walk_length Graph.finsetWalkLength

-- theorem coe_finsetWalkLength_eq (n : ℕ) (u v : G) :
--     (G.finsetWalkLength n u v : Set (G.Walk u v)) = {p : G.Walk u v | p.length = n} := by
--   induction' n with n ih generalizing u v
--   · obtain rfl | huv := eq_or_ne u v <;> simp [finsetWalkLength, set_walk_length_zero_eq_of_ne, *]
--   · simp only [finsetWalkLength, set_walk_length_succ_eq, Finset.coe_biUnion, Finset.mem_coe,
--       Finset.mem_univ, Set.iUnion_true]
--     ext p
--     simp only [mem_neighborSet, Finset.coe_map, Embedding.coeFn_mk, Set.iUnion_coe_set,
--       Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Set.mem_setOf_eq]
--     congr!
--     rename_i w _ q
--     have := Set.ext_iff.mp (ih w v) q
--     simp only [Finset.mem_coe, Set.mem_setOf_eq] at this
--     rw [← this]
-- #align simple_graph.coe_finset_walk_length_eq Graph.coe_finsetWalkLength_eq

-- variable {G}

-- theorem Walk.mem_finsetWalkLength_iff_length_eq {n : ℕ} {u v : G} (p : G.Walk u v) :
--     p ∈ G.finsetWalkLength n u v ↔ p.length = n :=
--   Set.ext_iff.mp (G.coe_finsetWalkLength_eq n u v) p
-- #align simple_graph.walk.mem_finset_walk_length_iff_length_eq Graph.Walk.mem_finsetWalkLength_iff_length_eq

-- variable (G)

-- instance fintypeSetWalkLength (u v : G) (n : ℕ) : Fintype {p : G.Walk u v | p.length = n} :=
--   Fintype.ofFinset (G.finsetWalkLength n u v) fun p => by
--     rw [← Finset.mem_coe, coe_finsetWalkLength_eq]
-- #align simple_graph.fintype_set_walk_length Graph.fintypeSetWalkLength

-- instance fintypeSubtypeWalkLength (u v : G) (n : ℕ) : Fintype {p : G.Walk u v // p.length = n} :=
--   fintypeSetWalkLength G u v n

-- theorem set_walk_length_toFinset_eq (n : ℕ) (u v : G) :
--     {p : G.Walk u v | p.length = n}.toFinset = G.finsetWalkLength n u v := by
--   ext p
--   simp [← coe_finsetWalkLength_eq]
-- #align simple_graph.set_walk_length_to_finset_eq Graph.set_walk_length_toFinset_eq

-- /- See `Graph.adjMatrix_pow_apply_eq_card_walk` for the cardinality in terms of the `n`th
-- power of the adjacency matrix. -/
-- theorem card_set_walk_length_eq (u v : G) (n : ℕ) :
--     Fintype.card {p : G.Walk u v | p.length = n} = (G.finsetWalkLength n u v).card :=
--   Fintype.card_ofFinset (G.finsetWalkLength n u v) fun p => by
--     rw [← Finset.mem_coe, coe_finsetWalkLength_eq]
-- #align simple_graph.card_set_walk_length_eq Graph.card_set_walk_length_eq

-- instance fintypeSetPathLength (u v : G) (n : ℕ) :
--     Fintype {p : G.Walk u v | p.IsPath ∧ p.length = n} :=
--   Fintype.ofFinset ((G.finsetWalkLength n u v).filter Walk.IsPath) <| by
--     simp [Walk.mem_finsetWalkLength_iff_length_eq, and_comm]
-- #align simple_graph.fintype_set_path_length Graph.fintypeSetPathLength

-- end LocallyFinite

-- section Finite

-- variable [Fintype G] [DecidableRel G.E]

-- theorem reachable_iff_exists_finsetWalkLength_nonempty (u v : G) :
--     G.Reachable u v ↔ ∃ n : Fin (Fintype.card G), (G.finsetWalkLength n u v).Nonempty := by
--   constructor
--   · intro r
--     refine r.elim_path fun p => ?_
--     refine ⟨⟨_, p.isPath.length_lt⟩, p, ?_⟩
--     simp [Walk.mem_finsetWalkLength_iff_length_eq]
--   · rintro ⟨_, p, _⟩
--     exact ⟨p⟩
-- #align simple_graph.reachable_iff_exists_finset_walk_length_nonempty Graph.reachable_iff_exists_finsetWalkLength_nonempty

-- instance : DecidableRel G.Reachable := fun u v =>
--   decidable_of_iff' _ (reachable_iff_exists_finsetWalkLength_nonempty G u v)

-- instance : Fintype G.ConnectedComponent :=
--   @Quotient.fintype _ _ G.reachableSetoid (inferInstance : DecidableRel G.Reachable)

-- instance : Decidable G.Preconnected :=
--   inferInstanceAs <| Decidable (∀ u v, G.Reachable u v)

-- instance : Decidable G.Connected := by
--   rw [connected_iff, ← Finset.univ_nonempty_iff]
--   infer_instance

-- end Finite

-- end WalkCounting

-- end Graph