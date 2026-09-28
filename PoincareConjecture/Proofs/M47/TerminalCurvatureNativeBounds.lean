import PoincareConjecture.Proofs.M47.BlowupControlsCapNativeJets









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)



theorem terminalCurvature_native_metric_difference_bound
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (B : RoundCylinderTwoTensor)
    (hclose : RoundCylinderClose epsilon 0 B)
    (g1 : RiemannianMetric 3 E)
    (D0 : LeviCivitaData (M35.cylinderEuclideanMetric 0 (by norm_num)))
    (q : UnitTwoSphere) {U : Set E} (hU : IsOpen U)
    (hcoeff : ∀ x ∈ U, ∀ i j : Fin 3,
      g1.inner x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient B (chartAt E2 q) (M35.cylinderCoordinateEquiv x) i j)
    (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hx : M35.cylinderCoordinateEquiv.symm (0, s) ∈ U)
    (k : ℕ) (hk : k ≤ ⌊epsilon⁻¹⌋₊) :
    let H : CovariantTensorEvaluation 3 E 2 := fun y v =>
      g1.inner y (v 0) (v 1) - (M35.cylinderEuclideanMetric 0 (by norm_num)).inner y (v 0) (v 1)
    (M35.cylinderEuclideanMetric 0 (by norm_num)).tensorNorm
      (D0.iteratedCovariantTensorDerivative H k)
      (M35.cylinderCoordinateEquiv.symm (0, s)) ≤ epsilon := by
  let H : CovariantTensorEvaluation 3 E 2 := fun y v =>
    g1.inner y (v 0) (v 1) - (M35.cylinderEuclideanMetric 0 (by norm_num)).inner y (v 0) (v 1)
  let f : ℕ → ℝ := fun j => roundCylinderTensorNormSquared 0 (chartAt E2 q)
    (chartAt E2 q q, s)
    (roundCylinderIteratedDerivative 0 (chartAt E2 q) B j (chartAt E2 q q, s))
  have hnorm (j : ℕ) :
      ((M35.cylinderEuclideanMetric 0 (by norm_num)).tensorNorm
        (D0.iteratedCovariantTensorDerivative H j)
        (M35.cylinderCoordinateEquiv.symm (0, s))) ^ 2 = f j :=
    cap_native_metricDifference_norm_sq g1 D0 q B hU hcoeff s hx j
  have hnonneg (j : ℕ) : 0 ≤ f j := by rw [← hnorm j]; exact sq_nonneg _
  have hterm : f k ≤ roundCylinderJetErrorSquared 0 B ⌊epsilon⁻¹⌋₊ (q, s) := by
    change f k ≤ ∑ j ∈ Finset.range (⌊epsilon⁻¹⌋₊ + 1), f j
    exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_range.mpr (by omega))
  obtain ⟨bound, hbound, hjet⟩ := hclose.2
  have hsq :
      ((M35.cylinderEuclideanMetric 0 (by norm_num)).tensorNorm
        (D0.iteratedCovariantTensorDerivative H k)
        (M35.cylinderCoordinateEquiv.symm (0, s))) ^ 2 ≤ epsilon ^ 2 := by
    rw [hnorm]
    exact hterm.trans ((hjet (q, s) hs).trans hbound.le)
  have hn : 0 ≤ (M35.cylinderEuclideanMetric 0 (by norm_num)).tensorNorm
      (D0.iteratedCovariantTensorDerivative H k)
      (M35.cylinderCoordinateEquiv.symm (0, s)) := Real.sqrt_nonneg _
  exact (sq_le_sq₀ hn hepsilon.le).mp hsq



theorem terminalCurvature_native_two_derivative_bounds
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 2)
    (B : RoundCylinderTwoTensor) (hclose : RoundCylinderClose epsilon 0 B)
    (g1 : RiemannianMetric 3 E)
    (D0 : LeviCivitaData (M35.cylinderEuclideanMetric 0 (by norm_num)))
    (q : UnitTwoSphere) {U : Set E} (hU : IsOpen U)
    (hcoeff : ∀ x ∈ U, ∀ i j : Fin 3,
      g1.inner x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient B (chartAt E2 q) (M35.cylinderCoordinateEquiv x) i j)
    (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hx : M35.cylinderCoordinateEquiv.symm (0, s) ∈ U) :
    let H : CovariantTensorEvaluation 3 E 2 := fun y v =>
      g1.inner y (v 0) (v 1) - (M35.cylinderEuclideanMetric 0 (by norm_num)).inner y (v 0) (v 1)
    let g0 := M35.cylinderEuclideanMetric 0 (by norm_num)
    let x := M35.cylinderCoordinateEquiv.symm (0, s)
    g0.tensorNorm H x ≤ epsilon ∧
      g0.tensorNorm (D0.covariantTensorDerivative H) x ≤ epsilon ∧
      g0.tensorNorm (D0.covariantTensorDerivative (D0.covariantTensorDerivative H)) x ≤
        epsilon := by
  have horder : 2 ≤ ⌊epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    change (2 : ℝ) ≤ epsilon⁻¹
    rw [← one_div, le_div_iff₀ hepsilon]
    linarith only [hsmall]
  have hbound := terminalCurvature_native_metric_difference_bound
    hepsilon B hclose g1 D0 q hU hcoeff s hs hx
  exact ⟨hbound 0 (by omega), hbound 1 (by omega), hbound 2 horder⟩

end PoincareConjecture.M47
