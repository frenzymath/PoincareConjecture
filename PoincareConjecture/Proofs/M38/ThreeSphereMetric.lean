import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.InducedForm
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M38

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

noncomputable def threeSphereMetric : RiemannianMetric 3 UnitThreeSphere := by
  let g₄ : RiemannianMetric 4 (EuclideanSpace ℝ (Fin 4)) :=
    { riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin 4)) with
      contMDiff := (riemannianMetricVectorSpace
        (EuclideanSpace ℝ (Fin 4))).contMDiff.of_le le_top }
  let inclusion : UnitThreeSphere → EuclideanSpace ℝ (Fin 4) := Subtype.val
  let A (x : UnitThreeSphere) :
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    mfderiv (𝓡 3) (𝓡 4) inclusion x
  have hA (x : UnitThreeSphere) : Function.Injective (A x) := by
    change Function.Injective (mvfderiv (𝓡 3) inclusion x)
    exact injective_mvfderiv_subtypeVal_sphere x
  refine {
    inner := Poincare.Gluing.inducedForm g₄ inclusion
    symm := ?_
    pos := ?_
    isVonNBounded := ?_
    contMDiff := ?_ }
  · intro x v w
    change inner ℝ (A x v) (A x w) = inner ℝ (A x w) (A x v)
    exact real_inner_comm _ _
  · intro x v hv
    change 0 < inner ℝ (A x v) (A x v)
    apply real_inner_self_pos.mpr
    intro hz
    exact hv ((hA x) (hz.trans (map_zero (A x)).symm))
  · intro x
    change Bornology.IsVonNBounded ℝ
      {v : EuclideanSpace ℝ (Fin 3) | inner ℝ (A x v) (A x v) < 1}
    let B : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) := A x
    obtain ⟨K, _, hK⟩ :=
      (LinearMap.injective_iff_antilipschitz B.toLinearMap).mp (hA x)
    apply (NormedSpace.isVonNBounded_iff ℝ).mpr
    apply (hK.isBounded_preimage (Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin 4)))
      (r := 1))).subset
    intro v hv
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right,
      ContinuousLinearMap.coe_coe, B]
    simp only [Set.mem_setOf_eq, real_inner_self_eq_norm_sq] at hv
    nlinarith [norm_nonneg (A x v)]
  · intro x
    exact Poincare.Gluing.inducedForm_contMDiffAt g₄ (contMDiff_coe_sphere x)

theorem threeSphereMetric_inner (x : UnitThreeSphere) (v w : TangentSpace (𝓡 3) x) :
    threeSphereMetric.inner x v w = inner ℝ
      (mfderiv (𝓡 3) (𝓡 4) (Subtype.val : UnitThreeSphere → EuclideanSpace ℝ (Fin 4)) x v)
      (mfderiv (𝓡 3) (𝓡 4) (Subtype.val : UnitThreeSphere → EuclideanSpace ℝ (Fin 4)) x w) := rfl

end PoincareConjecture.M38
