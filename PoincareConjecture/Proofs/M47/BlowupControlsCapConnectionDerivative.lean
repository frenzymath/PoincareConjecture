import PoincareConjecture.Proofs.M47.BlowupControlsCapConnectionCoefficients
import PoincareConjecture.Proofs.M47.BlowupControlsCapInverseCoefficients
import PoincareConjecture.Proofs.M47.BlowupControlsCapCurvatureDifference

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem cap_connectionDifference_fderiv_normal
    {g0 g1 : RiemannianMetric n V} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    (e : V ≃L[ℝ] V) (x : V)
    (hzero : ∀ a c : V, D0.euclideanConnection a c x = 0)
    (u v w : V) (i : Fin n) :
    let b := EuclideanSpace.basisFun (Fin n) ℝ
    let H : CovariantTensorEvaluation n V 2 :=
      fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
    let S := fun j y => D0.covariantTensorDerivative H y ![u, v, e (b j)] +
      D0.covariantTensorDerivative H y ![v, u, e (b j)] -
      D0.covariantTensorDerivative H y ![e (b j), u, v]
    inner ℝ (b i) (e.symm (fderiv ℝ
      (fun y => D1.euclideanConnection u v y - D0.euclideanConnection u v y) x w)) =
      (1 / 2 : ℝ) * ∑ j,
        (fderiv ℝ (fun y => M04.frameInverseGram g1 y e.toContinuousLinearMap i j) x w * S j x +
        M04.frameInverseGram g1 x e.toContinuousLinearMap i j *
          (D0.covariantTensorDerivative (D0.covariantTensorDerivative H) x
              ![w, u, v, e (b j)] +
            D0.covariantTensorDerivative (D0.covariantTensorDerivative H) x
              ![w, v, u, e (b j)] -
            D0.covariantTensorDerivative (D0.covariantTensorDerivative H) x
              ![w, e (b j), u, v])) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let H : CovariantTensorEvaluation n V 2 :=
    fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
  let S := fun j y => D0.covariantTensorDerivative H y ![u, v, e (b j)] +
    D0.covariantTensorDerivative H y ![v, u, e (b j)] -
    D0.covariantTensorDerivative H y ![e (b j), u, v]
  let C := fun j y => M04.frameInverseGram g1 y e.toContinuousLinearMap i j
  let B := fun y => D1.euclideanConnection u v y - D0.euclideanConnection u v y
  let phi : V →L[ℝ] ℝ := (innerSL ℝ (b i)).comp e.symm.toContinuousLinearMap
  have hH : IsSmoothCovariantTensor H := cap_metricDifference_smooth g0 g1
  have hH1 := M04.isSmoothCovariantTensor_covariantTensorDerivative D0 hH
  have hT (z : Fin 3 → V) :
      DifferentiableAt ℝ (fun y => D0.covariantTensorDerivative H y z) x :=
    (cap_tensorEvaluation_contDiff _ hH1 z).differentiable (by simp) x
  have hS (j : Fin n) : DifferentiableAt ℝ (S j) x :=
    ((hT ![u, v, e (b j)]).add (hT ![v, u, e (b j)])).sub (hT ![e (b j), u, v])
  have hC (j : Fin n) : DifferentiableAt ℝ (C j) x :=
    (cap_frameInverseGram_contDiff g1 e i j).differentiable (by simp) x
  have hB : DifferentiableAt ℝ B x :=
    ((D1.contDiffAt_euclideanConnection x u v).differentiableAt (by simp)).sub
      ((D0.contDiffAt_euclideanConnection x u v).differentiableAt (by simp))
  have hleft := congrArg (fun L : V →L[ℝ] ℝ => L w)
    (phi.hasFDerivAt.comp x hB.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => phi (B y)) x w = phi (fderiv ℝ B x w) at hleft
  have heq : (fun y => phi (B y)) = fun y => (1 / 2 : ℝ) * ∑ j, C j y * S j y := by
    funext y
    exact cap_connectionDifference_coefficients D0 D1 e y u v i
  have hsum := (HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (hC j).hasFDerivAt.mul (hS j).hasFDerivAt)).const_mul (1 / 2 : ℝ)
  have hright := congrArg (fun L : V →L[ℝ] ℝ => L w) hsum.fderiv
  simp only [Pi.mul_apply] at hright
  rw [← heq] at hright
  simp only [smul_apply, smul_eq_mul, sum_apply, add_apply] at hright
  have hSj (j : Fin n) : fderiv ℝ (S j) x w =
      D0.covariantTensorDerivative (D0.covariantTensorDerivative H) x ![w, u, v, e (b j)] +
      D0.covariantTensorDerivative (D0.covariantTensorDerivative H) x ![w, v, u, e (b j)] -
      D0.covariantTensorDerivative (D0.covariantTensorDerivative H) x ![w, e (b j), u, v] := by
    dsimp only [S]
    rw [fderiv_fun_sub ((hT ![u, v, e (b j)]).fun_add (hT ![v, u, e (b j)]))
        (hT ![e (b j), u, v]),
      fderiv_fun_add (hT ![u, v, e (b j)]) (hT ![v, u, e (b j)]), sub_apply, add_apply]
    rw [cap_secondCovariantTensorDerivative_normal D0 H hH x hzero ![u, v, e (b j)] w,
      cap_secondCovariantTensorDerivative_normal D0 H hH x hzero ![v, u, e (b j)] w,
      cap_secondCovariantTensorDerivative_normal D0 H hH x hzero ![e (b j), u, v] w]
    rfl
  have h := hleft.symm.trans hright
  simp only [hSj] at h
  refine h.trans ?_
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [C]
  ring

end PoincareConjecture.M47
