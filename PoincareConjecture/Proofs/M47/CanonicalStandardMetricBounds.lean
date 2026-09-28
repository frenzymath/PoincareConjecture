import PoincareConjecture.Definitions.M34StandardCapExistence
import PoincareConjecture.Proofs.M04.TensorNormBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.M34.Standard.CalibratedMetricComparison









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.Proofs.M47



theorem exists_standard_slab_metric_bound {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta : theta < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ∈ Icc 0 theta, ∀ t ∈ Icc 0 theta,
      ∀ x : StandardCapSpace, ∀ w : TangentSpace (𝓡 3) x,
        (standard.flow.metric t).tangentNorm x w ≤
          Real.exp (K * |t - s|) * (standard.flow.metric s).tangentNorm x w := by
  have htime : theta < standard.flow.base.lifetime := by
    rwa [standard.lifetime_one]
  obtain ⟨B, hB, hbound⟩ := standard.flow.base.curvature_locally_bounded
    theta htheta0 htime
  let K := 3 * B + 1
  have hK : 0 < K := by dsimp only [K]; linarith
  have hsub : Icc 0 theta ⊆ Ico 0 standard.flow.base.lifetime :=
    fun _ hs => ⟨hs.1, hs.2.trans_lt htime⟩
  refine ⟨K, hK, ?_⟩
  intro s hs t ht x w
  apply standard.flow.base.flow.tangentNorm_le_exp_of_ricci_bound
    (convex_Icc 0 theta) hsub x w K _ hs ht
  intro tau htau
  have hinner : 0 ≤ (standard.flow.metric tau).inner x w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact ((standard.flow.metric tau).pos x w hw).le
  have hcurv : (standard.flow.connection tau).curvatureTensorNorm x ≤ B :=
    (le_abs_self _).trans (hbound tau htau x)
  have h := M04.abs_ricci_le_curvatureTensorNorm (standard.flow.connection tau) x w
  norm_num only [Nat.cast_ofNat] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) hinner)



theorem exists_standard_initial_distance_factor {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta : theta < 1) :
    ∃ Lambda : ℝ, 0 < Lambda ∧ ∀ s ∈ Icc 0 theta,
      ∀ x y : StandardCapSpace,
        g0.metric.edist x y ≤ ENNReal.ofReal Lambda * (standard.flow.metric s).edist x y := by
  obtain ⟨K, hK, hbound⟩ := exists_standard_slab_metric_bound standard htheta0 htheta
  let Lambda := Real.exp (K * theta)
  refine ⟨Lambda, Real.exp_pos _, ?_⟩
  intro s hs
  apply M34.edist_le_of_tangentNorm_le (standard.flow.metric s) g0.metric (Real.exp_pos _)
  intro x w
  have h := hbound s hs 0 ⟨le_rfl, htheta0⟩ x w
  have hinitial : standard.flow.metric 0 = g0.metric := standard.flow.base.initial_metric
  rw [hinitial] at h
  have hexponent : K * |(0 : ℝ) - s| ≤ K * theta := by
    rw [zero_sub, abs_neg, abs_of_nonneg hs.1]
    exact mul_le_mul_of_nonneg_left hs.2 hK.le
  exact h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexponent)
    (Real.sqrt_nonneg _))

end PoincareConjecture.Proofs.M47
