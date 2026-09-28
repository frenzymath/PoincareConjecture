import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeDilationMeasure
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.NormalizedDilation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem exists_dilated_integral_heat (J : V →L[ℝ] H) {a b T B : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hT : 0 ≤ T) (hBT : b * T ≤ B) (hB : 0 < B)
    (A : ℝ → V →L[ℝ] V) (hA : ContDiffOn ℝ ∞ A (Icc 0 B))
    (v : ℝ → V) (hv : MemLp v 2 (timeMeasure B)) (U : ℝ → H)
    (hU : ContinuousOn U (Icc 0 B))
    (hgraph : ∀ᵐ t ∂timeMeasure B, J (v t) = U t)
    (heq : ∀ t ∈ Icc 0 B, J.adjoint (U t) = J.adjoint (U 0) +
      ∫ r in (0 : ℝ)..t, A r (v r)) {s : ℝ} (hs : s ∈ Icc a b) :
    ∃ w : Lp V 2 (timeMeasure T),
      ContinuousOn (fun t => U (s * t)) (Icc 0 T) ∧
      (∀ᵐ t ∂timeMeasure T, J (w t) = U (s * t)) ∧
      ∀ t ∈ Icc 0 T, J.adjoint (U (s * t)) = J.adjoint (U 0) +
        ∫ r in (0 : ℝ)..t,
          normalizedDilationLp J ha.le hab hT hBT hB A hA s w r - w r +
            J.adjoint (J (w r)) := by
  have hspos : 0 < s := ha.trans_le hs.1
  have hsT : s * T ≤ B := (mul_le_mul_of_nonneg_right hs.2 hT).trans hBT
  have hvs := memLp_time_dilation hspos hsT hv
  let w := hvs.toLp (fun t => v (s * t))
  have hcoe : ∀ᵐ t ∂timeMeasure T, w t = v (s * t) := hvs.coeFn_toLp
  have htime (t : ℝ) (ht : t ∈ Icc 0 T) : s * t ∈ Icc 0 B :=
    dilationTime_mem ha.le hab hBT ⟨s, hs⟩ ⟨t, ht⟩
  refine ⟨w, hU.comp (continuous_const.mul continuous_id).continuousOn htime, ?_, ?_⟩
  · filter_upwards [hcoe, ae_time_dilation hspos hsT hgraph] with t ht hg
    rw [ht, hg]
  · intro t ht
    rw [heq (s * t) (htime t ht), ← integral_time_dilation (fun r => A r (v r)) s t]
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2) hcoe,
      ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2)
        (normalizedDilationLp_generator J ha.le hab hT hBT hB A hA hs w)] with r hr hg
    rw [hg, hr]

end PoincareConjecture.M35.Uniqueness.Heat
