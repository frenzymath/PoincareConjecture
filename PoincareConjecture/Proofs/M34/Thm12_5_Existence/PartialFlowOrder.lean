import PoincareConjecture.Definitions.Ch12.StandardCap

set_option autoImplicit false

open Set

namespace PoincareConjecture.M34

variable {g0 : StandardInitialMetric}

def partialFlowData (F : PartialStandardCapFlow g0) (t : ℝ) :
    Σ g : RiemannianMetric 3 StandardCapSpace, LeviCivitaData g :=
  ⟨F.flow.metric t, F.flow.connection t⟩

def partialFlowLE (F G : PartialStandardCapFlow g0) : Prop :=
  F.lifetime ≤ G.lifetime ∧ EqOn (partialFlowData F) (partialFlowData G)
    (Ico 0 F.lifetime)

theorem partialFlowLE_refl (F : PartialStandardCapFlow g0) : partialFlowLE F F :=
  ⟨le_rfl, fun _ _ => rfl⟩

theorem partialFlowLE_trans {F G H : PartialStandardCapFlow g0}
    (hFG : partialFlowLE F G) (hGH : partialFlowLE G H) : partialFlowLE F H :=
  ⟨hFG.1.trans hGH.1, fun _ ht =>
    (hFG.2 ht).trans (hGH.2 ⟨ht.1, ht.2.trans_le hFG.1⟩)⟩

theorem partialFlowData_eq_of_chain {c : Set (PartialStandardCapFlow g0)}
    (hc : IsChain partialFlowLE c) {F G : PartialStandardCapFlow g0}
    (hF : F ∈ c) (hG : G ∈ c) {t : ℝ}
    (htF : t ∈ Ico 0 F.lifetime) (htG : t ∈ Ico 0 G.lifetime) :
    partialFlowData F t = partialFlowData G t := by
  rcases eq_or_ne F G with rfl | hne
  · rfl
  rcases hc hF hG hne with h | h
  · exact h.2 htF
  · exact (h.2 htG).symm

def partialFlowOfExtension {F : PartialStandardCapFlow g0} {T : ℝ}
    (E : PartialStandardCapFlowExtension F T) : PartialStandardCapFlow g0 where
  lifetime := T
  lifetime_pos := F.lifetime_pos.trans E.lifetime_gt
  flow := E.flow
  initial_metric := E.initial_metric
  initial_connection := E.initial_connection
  curvature_locally_bounded := E.curvature_locally_bounded

theorem partialFlowLE_extension {F : PartialStandardCapFlow g0} {T : ℝ}
    (E : PartialStandardCapFlowExtension F T) :
    partialFlowLE F (partialFlowOfExtension E) := by
  refine ⟨E.lifetime_gt.le, fun t ht => ?_⟩
  exact Sigma.mk.inj_iff.mpr
    ⟨(E.agrees_on_old_domain ht).symm, (E.agrees_on_connection t ht).symm⟩

end PoincareConjecture.M34
