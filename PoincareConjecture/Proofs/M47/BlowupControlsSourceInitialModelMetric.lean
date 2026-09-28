import PoincareConjecture.Proofs.M47.BlowupControlsCapBoxMetric
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_EvolvingCylinderField









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M47

open M36 M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem source_initial_model_metric_bounds {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 0)
    {p : E} (hp : ‖cylinderHorizontalProjection p‖ ≤ 1) (v : E) :
    ‖v‖ ^ 2 ≤ evolvingCylinderModelField u p v v ∧
      evolvingCylinderModelField u p v v ≤ 4 * ‖v‖ ^ 2 := by
  have hstatic := cap_box_model_metric_bounds hp v
  have hsplit := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v v)
    cylinderHorizontalForm_add_vertical
  change cylinderHorizontalForm v v + cylinderHeightCovector v * cylinderHeightCovector v =
    inner ℝ v v at hsplit
  rw [real_inner_self_eq_norm_sq] at hsplit
  have hH : 0 ≤ cylinderHorizontalForm v v := by
    rw [cylinderHorizontalForm_apply]
    exact real_inner_self_nonneg
  have hV : 0 ≤ cylinderHeightCovector v * cylinderHeightCovector v := mul_self_nonneg _
  have hdifference : 0 ≤ cylinderModelField p v v -
      cylinderHeightCovector v * cylinderHeightCovector v := by
    linarith only [hstatic.1, hsplit, hH]
  change ‖v‖ ^ 2 ≤ (1 - u) * cylinderModelField p v v +
      u * (cylinderHeightCovector v * cylinderHeightCovector v) ∧
    (1 - u) * cylinderModelField p v v +
      u * (cylinderHeightCovector v * cylinderHeightCovector v) ≤ 4 * ‖v‖ ^ 2
  constructor
  · nlinarith only [hstatic.1, mul_nonneg (neg_nonneg.mpr hu.2) hdifference]
  · have hfactor : 0 ≤ 1 - u := by linarith only [hu.2]
    have hup := mul_le_mul_of_nonneg_left hstatic.2 hfactor
    have htime := mul_le_mul_of_nonneg_right hu.1 (sq_nonneg ‖v‖)
    nlinarith only [hup, htime, mul_nonpos_of_nonpos_of_nonneg hu.2 hV]



theorem source_initial_model_pullback (u : ℝ) (q : UnitTwoSphere) (s : ℝ)
    (p v w : E) :
    EvolvingRoundCylinderMetric u (centeredCylinderLift q s p)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (centeredCylinderLift q s) p v)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (centeredCylinderLift q s) p w) =
      evolvingCylinderModelField u p v w := by
  have hzero := cap_box_model_pullback q s p v w
  rw [centeredCylinderLift_mfderiv, centeredCylinderLift_mfderiv] at hzero ⊢
  simp only [EvolvingRoundCylinderMetric, evolvingCylinderModelField, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul] at hzero ⊢
  rw [← hzero]
  ring

end PoincareConjecture.M47
