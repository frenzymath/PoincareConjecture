import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_ExponentialFrames
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_ExponentialBalls










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44.NormalizedCapExponential

local notation "E" => StandardCapSpace

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta R : ℝ}
  {Q : SurgeryCapClose g₀ S g tip scale eta}



theorem frame_tangentNorm (D : NormalizedCapExponential Q R) (v : E) :
    Q.normalizedMetric.tangentNorm tip (D.frame v) = ‖v‖ := by
  have hframe := D.frame_inner v v
  rw [Q.normalizedMetric.chartCoefficients_self] at hframe
  rw [RiemannianMetric.tangentNorm, hframe, real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg v)]



theorem radial_initial_derivative (D : NormalizedCapExponential Q R) (v : E) :
    HasDerivAt (fun t : ℝ => extChartAt (𝓡 3) tip (D.map (t • v))) (D.frame v) 0 := by
  have hd0 : HasFDerivAt (fun w => extChartAt (𝓡 3) tip (D.map w))
      D.frame.toContinuousLinearMap ((0 : ℝ) • v) := by
    simpa only [zero_smul] using D.initial_derivative
  have hd := hd0.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const v)
  simpa only [Function.comp_def, id_eq, one_smul, ContinuousLinearEquiv.coe_coe] using hd



private theorem radial_mem_unit_interval
    {v : E} (hv : v ∈ Metric.ball 0 R) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t • v ∈ Metric.ball 0 R := by
  have hvR : ‖v‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_lt (by simpa using hvR)




theorem exists_minimizing_parameter (D : NormalizedCapExponential Q R)
    (hcompact : IsCompact (closure (Q.normalizedMetric.ball tip R)))
    {q : S.carrier} (hq : q ∈ Q.normalizedMetric.ball tip R) :
    ∃ v : E, v ∈ Metric.ball 0 R ∧ D.map v = q ∧
      ENNReal.ofReal ‖v‖ = Q.normalizedMetric.edist tip q := by
  obtain ⟨epsilon, hepsilon, γ, hγ, hγ0, hγ1, hmin⟩ :=
    Q.normalizedMetric.exists_minimizing_geodesic_of_precompact_ball tip q D.radius_pos hcompact hq
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) (1 + epsilon) := by constructor <;> linarith
  let a := deriv (fun t => extChartAt (𝓡 3) tip (γ t)) 0
  have hγa : HasDerivAt (fun t => extChartAt (𝓡 3) tip (γ t)) a 0 :=
    (hγ.hasDerivAt_chart_at hzero tip
      (by simpa only [hγ0] using mem_extChartAt_source tip)).1
  have hnorm : ENNReal.ofReal (Q.normalizedMetric.tangentNorm tip a) =
      Q.normalizedMetric.edist tip q := hγ.initial_tangentNorm_eq_of_edist_segment
        hepsilon hγ0 hγa hmin
  let v := D.frame.symm a
  have hnormv : ENNReal.ofReal ‖v‖ = Q.normalizedMetric.edist tip q := by
    rw [← D.frame_tangentNorm v, D.frame.apply_symm_apply]
    exact hnorm
  have hv : v ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right]
    apply (ENNReal.ofReal_lt_ofReal_iff D.radius_pos).mp
    rw [hnormv]
    exact hq
  have hγunit : Q.normalizedMetric.IsGeodesicOn γ (Icc (0 : ℝ) 1) :=
    fun t ht => hγ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hDunit : Q.normalizedMetric.IsGeodesicOn (fun t : ℝ => D.map (t • v))
      (Icc (0 : ℝ) 1) := fun t ht => D.geodesic v hv t (radial_mem_unit_interval hv ht)
  have hDzero : D.map ((0 : ℝ) • v) = tip := by rw [zero_smul, D.map_zero]
  have hDderiv : HasDerivAt (fun t : ℝ => extChartAt (𝓡 3) tip (D.map (t • v))) a 0 := by
    simpa only [v, D.frame.apply_symm_apply] using D.radial_initial_derivative v
  have hend := RiemannianMetric.geodesic_endpoint_eq_of_initial_data
    hγunit hDunit hγ0 hDzero hγa hDderiv
  refine ⟨v, hv, ?_, hnormv⟩
  simpa only [one_smul] using hend.symm.trans hγ1




theorem image_ball (D : NormalizedCapExponential Q R)
    (hcompact : IsCompact (closure (Q.normalizedMetric.ball tip R)))
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    D.map '' Metric.ball 0 r = Q.normalizedMetric.ball tip r := by
  apply Subset.antisymm
  · rintro _ ⟨v, hv, rfl⟩
    have hd := D.distance_bound v ((Metric.ball_subset_ball hrR) hv) 1 (by simp)
    simp only [one_smul, ENNReal.ofReal_one, mul_one] at hd
    apply hd.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff hr).mpr
    simpa only [Metric.mem_ball, dist_zero_right] using hv
  · intro q hq
    have hqR : q ∈ Q.normalizedMetric.ball tip R :=
      hq.trans_le (ENNReal.ofReal_le_ofReal hrR)
    obtain ⟨v, _, hev, hnorm⟩ := D.exists_minimizing_parameter hcompact hqR
    refine ⟨v, ?_, hev⟩
    rw [Metric.mem_ball, dist_zero_right]
    apply (ENNReal.ofReal_lt_ofReal_iff hr).mp
    rw [hnorm]
    exact hq




theorem radial_edist_of_injOn (D : NormalizedCapExponential Q R)
    (hcompact : IsCompact (closure (Q.normalizedMetric.ball tip R)))
    (hinj : InjOn D.map (Metric.ball 0 R)) {v : E} (hv : v ∈ Metric.ball 0 R) :
    Q.normalizedMetric.edist tip (D.map v) = ENNReal.ofReal ‖v‖ := by
  have hmem : D.map v ∈ Q.normalizedMetric.ball tip R := by
    rw [← D.image_ball hcompact D.radius_pos le_rfl]
    exact mem_image_of_mem D.map hv
  obtain ⟨w, hw, hew, hnorm⟩ := D.exists_minimizing_parameter hcompact hmem
  exact hnorm.symm.trans (congrArg (fun z : E => ENNReal.ofReal ‖z‖) (hinj hw hv hew))

end PoincareConjecture.M44.NormalizedCapExponential
