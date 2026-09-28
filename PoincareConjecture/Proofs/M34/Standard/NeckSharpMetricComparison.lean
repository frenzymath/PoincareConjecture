import PoincareConjecture.Proofs.M34.Standard.NeckHeightControl









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



theorem pullback_inner_comparison_sharp (he : N.epsilon ≤ 1 / 8)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : RoundCylinderTangent z) :
    (7 / 8 : ℝ) * EvolvingRoundCylinderMetric 0 z v v ≤
        N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v v ∧
      N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v v ≤
        (9 / 8 : ℝ) * EvolvingRoundCylinderMetric 0 z v v := by
  have herr := N.pullback_inner_error hz v
  have hmodel : 0 ≤ EvolvingRoundCylinderMetric 0 z v v := by
    unfold EvolvingRoundCylinderMetric
    let a : EuclideanSpace ℝ (Fin 3) := mfderiv (𝓡 2) (𝓡 3)
      (fun q : UnitTwoSphere => (q : EuclideanSpace ℝ (Fin 3))) z.1 v.1
    have hpos : 0 ≤ inner ℝ a a := real_inner_self_nonneg
    nlinarith [sq_nonneg v.2]
  have hsmall := mul_le_mul_of_nonneg_right he hmodel
  constructor <;> nlinarith [(abs_le.mp herr).1, (abs_le.mp herr).2]



theorem coordinate_inverse_axial_le_tangentNorm_sharp (he : N.epsilon ≤ 1 / 8)
    {x : M} (hx : x ∈ N.carrier) (v : TangentSpace (𝓡 3) x) :
    |(mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v).2| ≤
      ((5 / 4 : ℝ) / N.scale) * g.tangentNorm x v := by
  let z := N.coordinate_inverse x
  let w := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := (N.coordinate_inverse_mem x hx).2
  have hcomp := (N.pullback_inner_comparison_sharp he hz w).1
  have hmap : N.coordinate_map z = x := N.coordinate_map_inverse_eq hx
  have hd : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z w = v :=
    N.coordinate_map_inverse_mfderiv hx v
  have hpull : roundCylinderPullback g N.coordinate_map z w w = g.inner x v v := by
    unfold roundCylinderPullback
    rw [hd]
    change g.inner (N.coordinate_map z) v v = _
    rw [hmap]
  have haxial : w.2 ^ 2 ≤ EvolvingRoundCylinderMetric 0 z w w := by
    unfold EvolvingRoundCylinderMetric
    let a : EuclideanSpace ℝ (Fin 3) := mfderiv (𝓡 2) (𝓡 3)
      (fun q : UnitTwoSphere => (q : EuclideanSpace ℝ (Fin 3))) z.1 w.1
    have hpos : 0 ≤ inner ℝ a a := real_inner_self_nonneg
    nlinarith
  have hinner : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hnorm : g.tangentNorm x v ^ 2 = g.inner x v v := Real.sq_sqrt hinner
  have hproduct : 0 ≤ ((5 / 4 : ℝ) / N.scale) * g.tangentNorm x v := by
    exact mul_nonneg (div_nonneg (by norm_num) N.scale_pos.le) (Real.sqrt_nonneg _)
  have hsq : |w.2| ^ 2 ≤ (((5 / 4 : ℝ) / N.scale) * g.tangentNorm x v) ^ 2 := by
    rw [hpull] at hcomp
    rw [sq_abs, mul_pow, hnorm]
    have heq : ((5 / 4 : ℝ) / N.scale) ^ 2 = (25 / 16 : ℝ) * N.scale⁻¹ ^ 2 := by ring
    rw [heq]
    nlinarith [mul_nonneg (sq_nonneg N.scale⁻¹) hinner]
  exact (sq_le_sq₀ (abs_nonneg _) hproduct).mp hsq



theorem coordinate_map_axial_tangentNorm_le_sharp (he : N.epsilon ≤ 1 / 8)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a : ℝ) :
    g.tangentNorm (N.coordinate_map z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z (0, a)) ≤
      (5 / 4 : ℝ) * N.scale * |a| := by
  have hcomp := (N.pullback_inner_comparison_sharp he hz (0, a)).2
  have hmodel : EvolvingRoundCylinderMetric 0 z (0, a) (0, a) = a ^ 2 := by
    rw [← M34.roundCylinderMetricBilinear_apply, M34.roundCylinderMetricBilinear_apply_self]
    norm_num [Fin.sum_univ_succ]
  rw [hmodel] at hcomp
  have hscaled := mul_le_mul_of_nonneg_left hcomp (sq_nonneg N.scale)
  have hcancel : N.scale ^ 2 * N.scale⁻¹ ^ 2 = 1 := by
    field_simp [N.scale_pos.ne']
  rw [← mul_assoc, hcancel, one_mul] at hscaled
  change Real.sqrt _ ≤ _
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) (abs_nonneg a), ?_⟩
  change roundCylinderPullback g N.coordinate_map z (0, a) (0, a) ≤ _
  rw [mul_pow, mul_pow, sq_abs]
  nlinarith [mul_nonneg (sq_nonneg N.scale) (sq_nonneg a)]

end PoincareConjecture.EpsilonNeck
