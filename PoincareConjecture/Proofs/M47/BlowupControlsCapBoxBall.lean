import PoincareConjecture.Proofs.M47.BlowupControlsCapBoxChart
import PoincareConjecture.Proofs.M47.BlowupControlsCapBoxMeasure
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.ChartSegment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareConjecture.M47

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem capHalfBox_segment_subset (N : EpsilonNeck g) {z a : ℝ}
    (hz : -N.epsilon⁻¹ < z) (hright : z + 1 < N.epsilon⁻¹)
    (ha : 0 ≤ a) (haSmall : a ≤ 1 / 3) {p : E} (hp : p ∈ capHalfBox a) :
    segment ℝ 0 p ⊆ capBoxDomain N z := by
  rw [segment_eq_image_lineMap]
  rintro w ⟨t, ht, rfl⟩
  simpa only [AffineMap.lineMap_apply, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero,
    capBoxDomain, mem_inter_iff, mem_ofPred_eq] using
    capHalfBox_segment_domain N hz hright ha haSmall hp ht

theorem capHalfBox_image_edist_le (N : EpsilonNeck g) (q : UnitTwoSphere) {z a : ℝ}
    (hz : -N.epsilon⁻¹ < z) (hright : z + 1 < N.epsilon⁻¹)
    (ha : 0 ≤ a) (haSmall : a ≤ 1 / 3) {p : E} (hp : p ∈ capHalfBox a) :
    g.edist (N.coordinate_map (q, z)) (capBoxChart N q z p) ≤
      ENNReal.ofReal (2 * N.scale * ‖p‖) := by
  have hscale := N.scale_pos
  have hseg := capHalfBox_segment_subset N hz hright ha haSmall hp
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let K : ℝ≥0 := ⟨2 * N.scale, by positivity⟩
  have hdist : g.edist (centeredNeckLift N q z 0) (centeredNeckLift N q z p) ≤
      (K : ℝ≥0∞) * edist (0 : E) p := by
    apply Poincare.riemannianEDist_le_mul_edist_of_convex (I := 𝓡 3)
      (f := centeredNeckLift N q z) (convex_segment 0 p) ?_ ?_
      (left_mem_segment ℝ 0 p) (right_mem_segment ℝ 0 p)
    · intro w hw
      exact (centeredNeckLift_contMDiffAt N q z (hseg hw).1).of_le (by simp)
    · intro w hw
      let L : E →L[ℝ] TangentSpace (𝓡 3) (centeredNeckLift N q z w) :=
        mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N q z) w
      change ‖L‖ₑ ≤ (K : ℝ≥0∞)
      rw [← ofReal_norm, ENNReal.ofReal_le_coe]
      apply ContinuousLinearMap.opNorm_le_bound _ K.property
      intro v
      change g.tangentNorm (centeredNeckLift N q z w)
        (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N q z) w v) ≤ 2 * N.scale * ‖v‖
      exact (cap_box_neck_tangent_bounds N q z (hseg hw).1 (hseg hw).2.le v).2
  rw [centeredNeckLift_zero, edist_dist, dist_zero_left,
    ← ENNReal.ofReal_coe_nnreal] at hdist
  change g.edist (N.coordinate_map (q, z)) (centeredNeckLift N q z p) ≤
    ENNReal.ofReal (2 * N.scale) * ENNReal.ofReal ‖p‖ at hdist
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * N.scale)] at hdist
  exact hdist

theorem capHalfBox_image_subset_ball (N : EpsilonNeck g) (q : UnitTwoSphere) {z r : ℝ}
    (hz : -N.epsilon⁻¹ < z) (hright : z + 1 < N.epsilon⁻¹)
    (hr : 0 < r) (hrscale : r ≤ 2 * N.scale) :
    capBoxChart N q z '' capHalfBox (r / (6 * N.scale)) ⊆
      g.ball (N.coordinate_map (q, z)) r := by
  have hscale := N.scale_pos
  have ha : 0 ≤ r / (6 * N.scale) := by positivity
  have haSmall : r / (6 * N.scale) ≤ 1 / 3 := by
    apply (div_le_iff₀ (by positivity : 0 < 6 * N.scale)).mpr
    linarith
  rintro y ⟨p, hp, rfl⟩
  have hd := capHalfBox_image_edist_le N q hz hright ha haSmall hp
  have hn := capHalfBox_norm_le ha hp
  have hlen : 2 * N.scale * ‖p‖ < r := by
    have hmul := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 2 * N.scale)
    have hcancel : 2 * N.scale * (2 * (r / (6 * N.scale))) = 2 * r / 3 := by
      field_simp
      ring
    rw [hcancel] at hmul
    linarith
  exact hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hlen)

end PoincareConjecture.M47
