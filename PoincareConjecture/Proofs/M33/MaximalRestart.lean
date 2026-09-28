import PoincareConjecture.Definitions.M33BranchContinuation









set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.RepairedContinuationConclusion



theorem frontier_before
    {F : SurgeryFlowData.{u}} {T : ℝ} {I : RepairedContinuationInput F T}
    (C : RepairedContinuationConclusion I) {B : ℝ} (hB : T < B) :
    ∃ U : ℝ, T < U ∧ U ≤ B ∧
      Ico 0 U ⊆ C.extension.extended.time_domain ∧
      Disjoint C.extension.extended.surgery_times (Ioo T U) ∧
      (U < B → C.extension.extended.time_domain = Ico 0 U) ∧
      (C.extension.extended.time_domain = Ico 0 U →
        ∃ next : RepairedPreterminalSlab C.extension.extended U,
          next.start = T) := by
  have hT : 0 ≤ T := I.terminal_pos.le
  have hBpos : 0 < B := I.terminal_pos.trans hB
  have free (U : ℝ) (hU : Ico 0 U ⊆ C.extension.extended.time_domain) :
      Disjoint C.extension.extended.surgery_times (Ioo T U) := by
    apply Set.disjoint_left.mpr
    intro t hs ht
    exact C.no_later_surgery t (hU ⟨hT.trans ht.1.le, ht.2⟩) ht.1 hs
  by_cases h : C.end_time < ENNReal.ofReal B
  · have hfinite : C.end_time ≠ ⊤ := ne_top_of_lt h
    have hTU : T < C.end_time.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal hT hfinite).mp C.extends_past
    have hUB : C.end_time.toReal < B := ENNReal.toReal_lt_of_lt_ofReal h
    have hdomain : C.extension.extended.time_domain = Ico 0 C.end_time.toReal := by
      rw [C.time_domain_eq]
      ext t
      constructor
      · rintro ⟨ht, he⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht hfinite).mp he⟩
      · rintro ⟨ht, he⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht hfinite).mpr he⟩
    have hsubset : Ico 0 C.end_time.toReal ⊆ C.extension.extended.time_domain :=
      hdomain.symm.subset
    exact ⟨C.end_time.toReal, hTU, hUB.le, hsubset, free _ hsubset,
      fun _ => hdomain, fun _ => C.finite_end_slab hfinite⟩
  · have hend : ENNReal.ofReal B ≤ C.end_time := le_of_not_gt h
    have hsubset : Ico 0 B ⊆ C.extension.extended.time_domain := by
      intro t ht
      rw [C.time_domain_eq]
      exact ⟨ht.1, ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.1).mpr ht.2).trans_le hend⟩
    refine ⟨B, hB, le_rfl, hsubset, free B hsubset, fun hlt => (lt_irrefl B hlt).elim, ?_⟩
    intro hdomain
    have hexcluded : B ∉ C.extension.extended.time_domain := by
      rw [hdomain]
      exact fun ht => (lt_irrefl B ht.2)
    have hend_le : C.end_time ≤ ENNReal.ofReal B := by
      by_contra hnot
      apply hexcluded
      rw [C.time_domain_eq]
      exact ⟨hBpos.le, lt_of_not_ge hnot⟩
    have heq : C.end_time = ENNReal.ofReal B := le_antisymm hend_le hend
    have hfinite : C.end_time ≠ ⊤ := by rw [heq]; exact ENNReal.ofReal_ne_top
    have hreal : C.end_time.toReal = B := by rw [heq, ENNReal.toReal_ofReal hBpos.le]
    rw [← hreal]
    exact C.finite_end_slab hfinite

end PoincareConjecture.RepairedContinuationConclusion
