import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Collars.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Boundary.Reparameterization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Control












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.NoncompactKappa.Positive



theorem exists_recentered_neck_threshold {epsilon : ℝ}
    (he : 0 < epsilon) (hesmall : epsilon ≤ 1 / 200) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ epsilon / 4 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g), N.epsilon ≤ delta →
        ∀ (q : UnitTwoSphere) (s a : ℝ), |s| ≤ (3 / 2) * epsilon⁻¹ →
          0 < a → (N.scale ^ 2 * N.connection.scalarCurvature
            (N.coordinate_map (q, s))) * a ^ 2 = 1 →
          ∃ Q : EpsilonNeck g,
            Q.epsilon = epsilon ∧ Q.connection = N.connection ∧
            Q.center = N.coordinate_map (q, s) ∧
            Q.carrier = N.region (s - a * epsilon⁻¹) (s + a * epsilon⁻¹) ∧
            Q.central_sphere = range (fun p : UnitTwoSphere => N.coordinate_map (p, s)) ∧
            Q.coordinate_map = N.coordinate_map ∘ RoundCylinderAffine.space a s ∧
            Q.coordinate_inverse = RoundCylinderAffine.inverseSpace a s ∘ N.coordinate_inverse := by
  obtain ⟨delta₀, hd₀, _, hcurv⟩ :=
    EpsilonNeck.exists_ambient_curvature_control.{u} (show 0 < epsilon / 8 by positivity)
  refine ⟨min delta₀ (epsilon / 4), lt_min hd₀ (by positivity), min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g N hN q s a hs ha hcal
  have hNe : N.epsilon ≤ epsilon / 4 := hN.trans (min_le_right _ _)
  have hNinv : 4 * epsilon⁻¹ ≤ N.epsilon⁻¹ := by
    have h := (inv_le_inv₀ (show 0 < epsilon / 4 by positivity) N.epsilon_pos).mpr hNe
    have hi : (epsilon / 4)⁻¹ = 4 * epsilon⁻¹ := by field_simp
    rwa [hi] at h
  have hL : 0 < epsilon⁻¹ := inv_pos.mpr he
  have hsN : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    obtain ⟨hl, hu⟩ := abs_le.mp hs
    constructor <;> linarith
  let c := N.scale ^ 2 * N.connection.scalarCurvature (N.coordinate_map (q, s))
  have hcsmall : |c - 1| < epsilon / 8 :=
    (hcurv N N.connection (hN.trans (min_le_left _ _)) q hsN).1
  have hc : 0 < c := by
    have h := (abs_lt.mp hcsmall).1
    linarith
  have hR : 0 < N.connection.scalarCurvature (N.coordinate_map (q, s)) :=
    (mul_pos_iff_of_pos_left (sq_pos_of_pos N.scale_pos)).mp hc
  have hacal : c * a ^ 2 = 1 := hcal
  have haSmall : a < 6 / 5 := by
    have hcmin : 4 / 5 < c := by linarith [(abs_lt.mp hcsmall).1]
    nlinarith [sq_nonneg (a - 6 / 5)]
  have hsubHalf : MapsTo (fun z : ℝ => a * z + s)
      (Ioo (-(2 * (epsilon / 4))⁻¹) (2 * (epsilon / 4))⁻¹)
      (Ioo (-(epsilon / 4)⁻¹) (epsilon / 4)⁻¹) := by
    have hi : (2 * (epsilon / 4))⁻¹ = 2 * epsilon⁻¹ := by field_simp; ring
    have hj : (epsilon / 4)⁻¹ = 4 * epsilon⁻¹ := by field_simp
    intro z hz
    rw [hi] at hz
    rw [hj]
    obtain ⟨hl, hu⟩ := abs_le.mp hs
    have hza := mul_lt_mul_of_pos_left hz.1 ha
    have haz := mul_lt_mul_of_pos_left hz.2 ha
    have haL := mul_lt_mul_of_pos_right haSmall hL
    constructor <;> nlinarith
  have hsub : MapsTo (fun z : ℝ => a * z + s)
      (Ioo (-epsilon⁻¹) epsilon⁻¹) (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    fun z hz => DeepHorn.neckInterval_subset N.epsilon_pos hNe
      (hsubHalf (DeepHorn.neckInterval_subset (by positivity) (by linarith) hz))
  let B : RoundCylinderTwoTensor := fun z v w =>
    N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w
  have hB : RoundCylinderClose (epsilon / 4) 0 B :=
    roundCylinderClose_mono N.epsilon_pos hNe (by norm_num) N.metric_comparison.close
  have hbilinear : ∀ (z : RoundCylinderSpace) (d e : ℝ) (v w : RoundCylinderTangent z),
      B z (d • v) (e • w) = d * e * B z v w := by
    intro z d e v w
    simp only [B, roundCylinderPullback, map_smul, smul_apply, smul_eq_mul]
    ring
  have hclose := RoundCylinderAffine.close_normalized_pullback_of_abs
    (show 0 < epsilon / 4 by positivity) (by linarith) hc
    (show |c - 1| ≤ (epsilon / 4) / 2 by linarith) ha hacal s B hB hbilinear hsubHalf
  have hclose' := roundCylinderClose_mono (show 0 < 2 * (epsilon / 4) by positivity)
    (show 2 * (epsilon / 4) ≤ epsilon by linarith) (by norm_num : (0 : ℝ) < 1) hclose
  have hscale : c * N.scale⁻¹ ^ 2 =
      N.connection.scalarCurvature (N.coordinate_map (q, s)) := by
    dsimp only [c]
    field_simp [N.scale_pos.ne']
  have hactual : RoundCylinderClose epsilon 0 (fun z v w =>
      N.connection.scalarCurvature (N.coordinate_map (q, s)) *
        RoundCylinderAffine.pullback a s (roundCylinderPullback g N.coordinate_map) z v w) := by
    convert hclose' using 1
    funext z v w
    dsimp only [RoundCylinderAffine.pullback, B]
    rw [← mul_assoc, hscale]
  have hchart := N.affine_pullback_close s hsub g
    (N.connection.scalarCurvature (N.coordinate_map (q, s))) hactual
  let Q := N.affineWithMetric ha s hsub g N.connection he (by linarith) q hR hchart
  refine ⟨Q, rfl, rfl, rfl, ?_, ?_, rfl, rfl⟩
  · rw [N.affineWithMetric_carrier]
    congr 1 <;> ring
  · exact N.affineWithMetric_central_sphere ha s hsub g N.connection he
      (by linarith) q hR hchart

end PoincareConjecture.NoncompactKappa.Positive
