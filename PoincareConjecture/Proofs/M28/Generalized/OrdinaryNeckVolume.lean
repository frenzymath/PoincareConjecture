import PoincareConjecture.Proofs.M28.Generalized.OrdinaryNeckVolumeGeometry
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckVolumeLower
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckCollar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

universe u

namespace PoincareConjecture.M28

open tube RiemannianMetric

private abbrev E := EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

private theorem ordinary_neck_center_domain (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ (1 / 200 : ℝ)) (q : UnitTwoSphere) :
    Metric.closedBall (0 : E) 1 ⊆ cylinderNeckChartDomain N q 0 := by
  have hinv := one_div_le_one_div_of_le N.epsilon_pos hsmall
  norm_num only [one_div, inv_div, inv_one, div_one] at hinv
  exact normalized_neck_unit_ball_subset_domain N hsmall
    (show (1 : ℝ) ≤ N.epsilon⁻¹ / 16 by linarith) q (by norm_num)




theorem ordinary_neck_center_chart_edist_le (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ (1 / 200 : ℝ)) (q : UnitTwoSphere) {x y : E}
    (hx : x ∈ Metric.closedBall 0 1) (hy : y ∈ Metric.closedBall 0 1) :
    g.edist (cylinderNeckChart N q 0 x) (cylinderNeckChart N q 0 y) ≤
      ENNReal.ofReal (4 * N.scale) * edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let c : ℝ≥0 := ⟨4 * N.scale, mul_nonneg (by norm_num) N.scale_pos.le⟩
  have hdomain := ordinary_neck_center_domain N hsmall q
  have hsmooth (z : E) (hz : z ∈ Metric.closedBall (0 : E) 1) :
      ContMDiffAt (𝓡 3) (𝓡 3) 1 (cylinderNeckChart N q 0) z :=
    ((contMDiffOn_cylinderNeckChart N q 0).contMDiffAt
      ((isOpen_cylinderNeckChartDomain N q 0).mem_nhds (hdomain hz))).of_le (by simp)
  have hbound (z : E) (hz : z ∈ Metric.closedBall (0 : E) 1) :
      ‖mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q 0) z‖ₑ ≤ c := by
    rw [← ofReal_norm, ENNReal.ofReal_le_coe]
    apply ContinuousLinearMap.opNorm_le_bound _ c.coe_nonneg
    intro v
    exact full_neck_chart_speed_upper N q 0 (hdomain hz) v
  have h := Poincare.riemannianEDist_le_mul_edist_of_convex
    (convex_closedBall (0 : E) 1) hsmooth hbound hx hy
  rw [← ENNReal.ofReal_coe_nnreal] at h
  exact h





theorem ordinary_neck_center_ball_volume_lower
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (N : EpsilonNeck g) (hsmall : N.epsilon ≤ (1 / 200 : ℝ))
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ N.scale / 8) :
    ENNReal.ofReal (normalizedNeckVolumeLowerConstant * δ ^ 3) ≤
      g.volumeMeasure (g.ball N.center δ) := by
  let q := (N.coordinate_inverse N.center).1
  let b := δ / (4 * N.scale)
  have hb : 0 < b := div_pos hδ (mul_pos (by norm_num) N.scale_pos)
  have hbsmall : b ≤ 1 / 32 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) N.scale_pos)).mpr
    linarith
  have hunit : Metric.ball (0 : E) b ⊆ Metric.closedBall 0 1 := by
    intro x hx
    have hxnorm : ‖x‖ < b := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hdomain := ordinary_neck_center_domain N hsmall q
  have hUe : Metric.ball (0 : E) b ⊆ (neckVolumeChart N q 0).source := by
    rw [neckVolumeChart_source]
    exact hunit.trans hdomain
  have heq := g.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity
    (neckVolumeChart N q 0) (neckVolumeChart_smooth N q 0)
    (neckVolumeChart_symm_smooth N q 0) measurableSet_ball hUe
  change g.volumeMeasure (cylinderNeckChart N q 0 '' Metric.ball (0 : E) b) =
    ∫⁻ x in Metric.ball (0 : E) b,
      ENNReal.ofReal (g.pullbackVolumeDensity (cylinderNeckChart N q 0) x) at heq
  have hvolume : ENNReal.ofReal (N.scale ^ 3 / 48) * volume (Metric.ball (0 : E) b) ≤
      g.volumeMeasure (cylinderNeckChart N q 0 '' Metric.ball (0 : E) b) := by
    rw [heq, ← setLIntegral_const]
    apply setLIntegral_mono' measurableSet_ball
    intro x hx
    exact ENNReal.ofReal_le_ofReal (ordinary_neck_chart_density_lower N q 0
      (hdomain (hunit hx))
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hunit hx))
  have hidentity : ENNReal.ofReal (N.scale ^ 3 / 48) * volume (Metric.ball (0 : E) b) =
      ENNReal.ofReal (normalizedNeckVolumeLowerConstant * δ ^ 3) := by
    rw [euclidean_ball_volume_eq 3 hb,
      ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg N.scale_pos.le 3) (by norm_num))]
    congr 1
    dsimp only [b, normalizedNeckVolumeLowerConstant]
    field_simp [N.scale_pos.ne']
  rw [hidentity] at hvolume
  have hcenter : cylinderNeckChart N q 0 0 = N.center := by
    rw [cylinderNeckChart_zero]
    have hc := N.central_sphere_subset N.center_on_central_sphere
    have hzero := (N.mem_central_sphere_iff_of_mem_carrier hc).mp N.center_on_central_sphere
    have hz : (q, (0 : ℝ)) = N.coordinate_inverse N.center := by
      apply Prod.ext
      · rfl
      · exact hzero.symm
    rw [hz]
    exact N.coordinate_map_coordinate_inverse hc
  have hcapture : cylinderNeckChart N q 0 '' Metric.ball (0 : E) b ⊆
      g.ball N.center δ := by
    rintro _ ⟨x, hx, rfl⟩
    have hxnorm : ‖x‖ < b := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    have hdist := ordinary_neck_center_chart_edist_le N hsmall q
      (by simp : (0 : E) ∈ Metric.closedBall 0 1) (hunit hx)
    rw [hcenter] at hdist
    apply hdist.trans_lt
    rw [edist_eq_enorm_sub, zero_sub, enorm_neg, ← ofReal_norm,
      ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) N.scale_pos.le)]
    apply (ENNReal.ofReal_lt_ofReal_iff hδ).mpr
    have h := (lt_div_iff₀ (mul_pos (by norm_num) N.scale_pos)).mp hxnorm
    nlinarith only [h]
  exact hvolume.trans (measure_mono hcapture)

end PoincareConjecture.M28
