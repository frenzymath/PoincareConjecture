import PoincareConjecture.Proofs.M47.BlowupControlsCapNormalDerivative
import PoincareConjecture.Proofs.M47.BlowupControlsCapInverseDerivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Euclidean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem cap_frameGram_contDiff (g : RiemannianMetric n V) (L : V →L[ℝ] V) :
    ContDiff ℝ ∞ (fun y : V => M04.frameGramOperator g y L) := by
  apply contDiff_clm_apply_iff.mpr
  intro v
  apply (contDiff_piLp 2).mpr
  intro i
  have heq : (fun y : V => (M04.frameGramOperator g y L v) i) =
      fun y : V => g.inner y (L v) (L (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
    funext y
    have h := cap_frameGram_inner g y L v (EuclideanSpace.basisFun (Fin n) ℝ i)
    convert! h using 1
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]
  rw [heq]
  exact ((contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).clm_apply
    contDiff_const).clm_apply contDiff_const

theorem cap_frameInverse_contDiff (g : RiemannianMetric n V) (e : V ≃L[ℝ] V) :
    ContDiff ℝ ∞ (fun y : V => (M04.frameGramOperator g y e.toContinuousLinearMap).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (M04.frameGramOperator_isInvertible g x e).contDiffAt_map_inverse.comp x
    (cap_frameGram_contDiff g e.toContinuousLinearMap).contDiffAt

theorem cap_frameGram_fderiv_normal
    {g0 g1 : RiemannianMetric n V} (D0 : LeviCivitaData g0)
    (e : V ≃L[ℝ] V) (x : V)
    (hzero : ∀ u v : V, D0.euclideanConnection u v x = 0) (u v w : V) :
    let H : CovariantTensorEvaluation n V 2 :=
      fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
    inner ℝ (fderiv ℝ (fun y => M04.frameGramOperator g1 y e.toContinuousLinearMap) x u v) w =
      D0.covariantTensorDerivative H x ![u, e v, e w] := by
  let A : V → V →L[ℝ] V := fun y => M04.frameGramOperator g1 y e.toContinuousLinearMap
  have hA : DifferentiableAt ℝ A x :=
    (cap_frameGram_contDiff g1 e.toContinuousLinearMap).differentiable (by simp) x
  have hd := HasFDerivAt.inner ℝ (hA.hasFDerivAt.clm_apply (hasFDerivAt_const v x))
    (hasFDerivAt_const w x)
  have heq : (fun y => inner ℝ (A y v) w) = fun y => g1.inner y (e v) (e w) := by
    funext y
    exact cap_frameGram_inner g1 y e.toContinuousLinearMap v w
  have h := congrArg (fun L : V →L[ℝ] ℝ => L u) hd.fderiv
  simp only [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply, add_apply, zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply, inner_zero_right] at h
  rw [heq] at h
  exact h.symm.trans (cap_metric_fderiv_normal D0 x hzero u (e v) (e w))

end PoincareConjecture.M47
