import CyclicFormulas.Graph
import CyclicFormulas.Label

open Label Colour Graph

structure C2CF extends Graph where
  L  : V → Label
  Ω  : V → Colour

  vI : V

  succ            : V → Option V
  lit_no_succ     : ∀ v (_ : lit (L v)) w, ¬ E v w
  colouring       : ∀ v, col_admissible (L v) (Ω v)
  prg_succ_unique : ∀ v (_ : prg <| L v) w, E v w → succ v = some w
  -- cycles_mono     : ∀ v (C : toGraph.Walk v v), mono Ω C.support

structure C2CP extends C2CF where
  vF     : V
  LΩf    : L vF = .prop 0 ∧ Ω vF = .o
  i_ne_f : vI ≠ vF

attribute [simp] C2CP.LΩf

namespace C2CF

instance coeGraph : Coe C2CF Graph := ⟨toGraph⟩
instance coeType : CoeSort C2CF Type := ⟨(V .)⟩

instance : Nonempty (G : C2CF) := ⟨G.vI⟩

instance instFinEnumC2CF : FinEnum (G : C2CF) := G.V_fin

end C2CF

namespace C2CP

instance coeGraph : Coe C2CP Graph := ⟨(toC2CF .)⟩
instance coeType : CoeSort C2CP Type := ⟨(V .)⟩

@[simp]
lemma final_lit {H : C2CP} : lit <| H.L H.vF := of_eq_true (congr_arg _ H.LΩf.1)

@[simp]
lemma final_no_succ {H : C2CP} : ∀ x, ¬ H.E H.vF x :=
  H.lit_no_succ H.vF final_lit

end C2CP


