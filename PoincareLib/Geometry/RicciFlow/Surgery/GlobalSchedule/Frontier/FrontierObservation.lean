import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Branch
import PoincareLib.Geometry.RicciFlow.Surgery.Control.Basic

/-!
# Observe the retained maximal ordinary tail

Morgan--Tian Section 17.2, pp. 409-410. The domain and final slab come from
the actual M33 restart. An epoch boundary changes only the observation;
it does not truncate the raw surgery flow.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.M51

/-- The actual flow is global, or has a positive excluded endpoint with its
maximal final ordinary slab. This is output data of the retained restart. -/
def MaximalTail (F : SurgeryFlowData.{u}) : Prop :=
  F.time_domain = Ici 0 ∨
    ∃ T : ℝ, 0 < T ∧ F.time_domain = Ico 0 T ∧
      Nonempty (RepairedPreterminalSlab F T)

/-- Keep the maximal-domain alternative of this literal M33 continuation. -/
theorem maximalTail_of_restart
    {F : SurgeryFlowData.{u}} {T : ℝ} {I : RepairedContinuationInput F T}
    (C : RepairedContinuationConclusion I) : MaximalTail C.extension.extended := by
  by_cases htop : C.end_time = ⊤
  · left
    rw [C.time_domain_eq, htop]
    ext t
    simp
  · right
    have hT : T < C.end_time.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal I.terminal_pos.le htop).mp C.extends_past
    refine ⟨C.end_time.toReal, I.terminal_pos.trans hT, ?_, ?_⟩
    · rw [C.time_domain_eq]
      ext t
      constructor
      · rintro ⟨ht, hend⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht htop).mp hend⟩
      · rintro ⟨ht, hend⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht htop).mpr hend⟩
    · obtain ⟨L, _⟩ := C.finite_end_slab htop
      exact ⟨L⟩

/-- At an excluded endpoint, recover the final slab of the same raw flow. -/
theorem MaximalTail.slab_of_domain_eq {F : SurgeryFlowData.{u}}
    (hF : MaximalTail F) {H : ℝ} (hH : 0 < H)
    (hJ : F.time_domain = Ico 0 H) : Nonempty (RepairedPreterminalSlab F H) := by
  rcases hF with hglobal | ⟨T, hT, hdomain, hslab⟩
  · have hmem : H ∈ F.time_domain := hglobal ▸ hH.le
    rw [hJ] at hmem
    exact (lt_irrefl H hmem.2).elim
  · have hTH : T = H := by
      apply le_antisymm
      · by_contra h
        have hmem : H ∈ F.time_domain := hdomain ▸ ⟨hH.le, lt_of_not_ge h⟩
        rw [hJ] at hmem
        exact lt_irrefl H hmem.2
      · by_contra h
        have hmem : T ∈ F.time_domain := hJ ▸ ⟨hT.le, lt_of_not_ge h⟩
        rw [hdomain] at hmem
        exact lt_irrefl T hmem.2
    simpa only [hTH] using hslab

/-- Advance the observation to the actual endpoint or B. Equality with the
old horizon is allowed when it is already a singular epoch boundary. -/
theorem MaximalTail.observeBefore {F : SurgeryFlowData.{u}}
    (hF : MaximalTail F) (O : SurgeryObservation F) {B : ℝ} (hB : O.H ≤ B) :
    ∃ O' : SurgeryObservation F,
      O.H ≤ O'.H ∧ O'.H ≤ B ∧ O'.standard_flow = O.standard_flow ∧
      (O'.H < B → F.time_domain = Ico 0 O'.H) ∧
      (F.time_domain = Ico 0 O'.H → Nonempty (RepairedPreterminalSlab F O'.H)) := by
  have hBpos : 0 < B := O.H_pos.trans_le hB
  rcases hF with hglobal | ⟨T, hT, hdomain, hslab⟩
  · let O' : SurgeryObservation F := {
      H := B
      H_pos := hBpos
      interval_subset := by rw [hglobal]; exact fun _ ht => ht.1
      standard_flow := O.standard_flow }
    exact ⟨O', hB, le_rfl, rfl, fun h => (lt_irrefl B h).elim,
      MaximalTail.slab_of_domain_eq (Or.inl hglobal) O'.H_pos⟩
  · have hOT : O.H ≤ T := by
      by_contra h
      have hmem := O.interval_subset ⟨hT.le, lt_of_not_ge h⟩
      rw [hdomain] at hmem
      exact lt_irrefl T hmem.2
    let O' : SurgeryObservation F := {
      H := min T B
      H_pos := lt_min hT hBpos
      interval_subset := by
        intro t ht
        rw [hdomain]
        exact ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
      standard_flow := O.standard_flow }
    refine ⟨O', le_min hOT hB, min_le_right _ _, rfl, ?_,
      MaximalTail.slab_of_domain_eq (Or.inr ⟨T, hT, hdomain, hslab⟩) O'.H_pos⟩
    intro hlt
    have hTB : T < B := (min_lt_iff.mp hlt).resolve_right (lt_irrefl B)
    change F.time_domain = Ico 0 (min T B)
    rw [min_eq_left hTB.le]
    exact hdomain

end PoincareMT.M51
