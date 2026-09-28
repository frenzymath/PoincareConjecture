import PoincareConjecture.Proofs.M36.SurgeryTransitionMetric
import PoincareConjecture.Proofs.M34.Standard.NeckMetricComparison










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates



theorem cap_box_model_metric_bounds {p : E}
    (hp : ‖cylinderHorizontalProjection p‖ ≤ 1) (v : E) :
    ‖v‖ ^ 2 ≤ cylinderModelField p v v ∧
      cylinderModelField p v v ≤ 2 * ‖v‖ ^ 2 := by
  have hsplit := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v v)
    cylinderHorizontalForm_add_vertical
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    smul_eq_mul] at hsplit
  change cylinderHorizontalForm v v + cylinderHeightCovector v * cylinderHeightCovector v =
    inner ℝ v v at hsplit
  rw [real_inner_self_eq_norm_sq] at hsplit
  have hH : 0 ≤ cylinderHorizontalForm v v := by
    rw [cylinderHorizontalForm_apply]
    exact real_inner_self_nonneg
  have hV : 0 ≤ cylinderHeightCovector v * cylinderHeightCovector v := mul_self_nonneg _
  have hnorm : ‖cylinderHorizontalProjection p‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (cylinderHorizontalProjection p)]
  have hden : 0 < (‖cylinderHorizontalProjection p‖ ^ 2 + 4) ^ 2 := by positivity
  have hcoeff : 1 ≤ cylinderSphereFactor (cylinderEuclideanEquiv p) ∧
      cylinderSphereFactor (cylinderEuclideanEquiv p) ≤ 2 := by
    change 1 ≤ 32 / (‖cylinderHorizontalProjection p‖ ^ 2 + 4) ^ 2 ∧
      32 / (‖cylinderHorizontalProjection p‖ ^ 2 + 4) ^ 2 ≤ 2
    constructor
    · apply (le_div_iff₀ hden).mpr
      nlinarith [sq_nonneg ‖cylinderHorizontalProjection p‖]
    · apply (div_le_iff₀ hden).mpr
      nlinarith [sq_nonneg ‖cylinderHorizontalProjection p‖]
  rw [cylinderModelField]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hcoeff.1 hH]
  · nlinarith [mul_le_mul_of_nonneg_right hcoeff.2 hH]



theorem cap_box_model_pullback (q : UnitTwoSphere) (s : ℝ) (p v w : E) :
    EvolvingRoundCylinderMetric 0 (centeredCylinderLift q s p)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (centeredCylinderLift q s) p v)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (centeredCylinderLift q s) p w) =
      cylinderModelField p v w := by
  let L : E →L[ℝ] V :=
    mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (centeredCylinderLift q s) p
  have heq : (M34.roundCylinderMetricBilinear (centeredCylinderLift q s p)).bilinearComp L L =
      cylinderModelField p := by
    apply euclideanThree_bilinear_ext
    intro i j
    exact centeredCylinderLift_basis_gram q s p i j
  exact congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v w) heq

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}



theorem cap_box_neck_tangent_bounds (N : EpsilonNeck g) (q : UnitTwoSphere) (s : ℝ)
    {p : E} (hp : p ∈ centeredNeckDomain N s)
    (hhorizontal : ‖cylinderHorizontalProjection p‖ ≤ 1) (v : E) :
    N.scale / 2 * ‖v‖ ≤ g.tangentNorm (centeredNeckLift N q s p)
        (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N q s) p v) ∧
      g.tangentNorm (centeredNeckLift N q s p)
        (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N q s) p v) ≤
        2 * N.scale * ‖v‖ := by
  let z := centeredCylinderLift q s p
  let w := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (centeredCylinderLift q s) p v
  have hnative := N.pullback_inner_comparison (z := z) hp w
  have hd : mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N q s) p v =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z w := by
    have h := mfderiv_comp p
      ((neck_coordinate_contMDiffAt N (z := z) ⟨mem_univ _, hp⟩).mdifferentiableAt
        (by simp)) ((centeredCylinderLift_contMDiff q s p).mdifferentiableAt (by simp))
    exact congrArg (fun D => D v) h
  let b := g.inner (centeredNeckLift N q s p)
    (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N q s) p v)
    (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N q s) p v)
  have hpull : roundCylinderPullback g N.coordinate_map z w w = b := by
    simp only [roundCylinderPullback, b, hd]
    rfl
  rw [hpull, cap_box_model_pullback] at hnative
  have hmodel := cap_box_model_metric_bounds hhorizontal v
  have hscale := N.scale_pos
  have hcancel : N.scale ^ 2 * (N.scale⁻¹ ^ 2 * b) = b := by
    field_simp [hscale.ne']
  have hlo : N.scale ^ 2 / 2 * ‖v‖ ^ 2 ≤ b := calc
    _ ≤ N.scale ^ 2 * ((1 / 2 : ℝ) * cylinderModelField p v v) := by
      nlinarith [mul_le_mul_of_nonneg_left hmodel.1 (sq_nonneg N.scale)]
    _ ≤ N.scale ^ 2 * (N.scale⁻¹ ^ 2 * b) :=
      mul_le_mul_of_nonneg_left hnative.1 (sq_nonneg N.scale)
    _ = b := hcancel
  have hhi : b ≤ 4 * N.scale ^ 2 * ‖v‖ ^ 2 := calc
    _ = N.scale ^ 2 * (N.scale⁻¹ ^ 2 * b) := hcancel.symm
    _ ≤ N.scale ^ 2 * (2 * cylinderModelField p v v) :=
      mul_le_mul_of_nonneg_left hnative.2 (sq_nonneg N.scale)
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_left hmodel.2 (sq_nonneg N.scale)]
  have hb : 0 ≤ b := (by positivity : 0 ≤ N.scale ^ 2 / 2 * ‖v‖ ^ 2).trans hlo
  change N.scale / 2 * ‖v‖ ≤ Real.sqrt b ∧ Real.sqrt b ≤ 2 * N.scale * ‖v‖
  have hsqrt := Real.sq_sqrt hb
  constructor
  · apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg b)).mp
    nlinarith [mul_nonneg (sq_nonneg N.scale) (sq_nonneg ‖v‖)]
  · apply (sq_le_sq₀ (Real.sqrt_nonneg b) (by positivity)).mp
    nlinarith

end PoincareConjecture.M47
