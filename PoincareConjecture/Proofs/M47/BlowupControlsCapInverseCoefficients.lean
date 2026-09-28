import PoincareConjecture.Proofs.M47.BlowupControlsCapGramDerivative









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M47

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem cap_frameInverseGram_contDiff (g : RiemannianMetric n V)
    (e : V ≃L[ℝ] V) (i j : Fin n) :
    ContDiff ℝ ∞ (fun y : V => M04.frameInverseGram g y e.toContinuousLinearMap i j) := by
  change ContDiff ℝ ∞ (fun y : V =>
    inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
      ((M04.frameGramOperator g y e.toContinuousLinearMap).inverse
        (EuclideanSpace.basisFun (Fin n) ℝ j)))
  exact ContDiff.inner ℝ contDiff_const
    ((cap_frameInverse_contDiff g e).clm_apply contDiff_const)



theorem cap_frameInverseGram_fderiv (g : RiemannianMetric n V)
    (e : V ≃L[ℝ] V) (x u : V) (i j : Fin n) :
    let A : V → V →L[ℝ] V := fun y => M04.frameGramOperator g y e.toContinuousLinearMap
    let b := EuclideanSpace.basisFun (Fin n) ℝ
    fderiv ℝ (fun y => M04.frameInverseGram g y e.toContinuousLinearMap i j) x u =
      inner ℝ (b i) ((-((A x).inverse * (fderiv ℝ A x u) * (A x).inverse)) (b j)) := by
  let A : V → V →L[ℝ] V := fun y => M04.frameGramOperator g y e.toContinuousLinearMap
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hA : DifferentiableAt ℝ A x :=
    (cap_frameGram_contDiff g e.toContinuousLinearMap).differentiable (by simp) x
  have hAi : DifferentiableAt ℝ (fun y => (A y).inverse) x :=
    (cap_frameInverse_contDiff g e).differentiable (by simp) x
  have hv := hAi.hasFDerivAt.clm_apply (hasFDerivAt_const (b j) x)
  have hd := (innerSL ℝ (b i)).hasFDerivAt.comp x hv
  have h := congrArg (fun L : V →L[ℝ] ℝ => L u) hd.fderiv
  simp only [Function.comp_def, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    add_apply, zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply] at h
  rw [cap_inverse_fderiv_apply A hA (M04.frameGramOperator_isInvertible g x e) u] at h
  exact h

end PoincareConjecture.M47
