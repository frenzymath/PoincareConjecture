import PoincareConjecture.Proofs.M47.BlowupControlsCapModelNative









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)



theorem cap_model_derivative_norm_le
    {epsilon u : ℝ} (hepsilon : 0 < epsilon) (hu : u < 1)
    (B : RoundCylinderTwoTensor) (hclose : RoundCylinderClose epsilon u B)
    (g1 : RiemannianMetric 3 E)
    (D0 : LeviCivitaData (M35.cylinderEuclideanMetric u hu))
    (q : UnitTwoSphere) {U : Set E} (hU : IsOpen U)
    (hcoeff : ∀ x ∈ U, ∀ i j : Fin 3,
      g1.inner x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient B (chartAt E2 q) (M35.cylinderCoordinateEquiv x) i j)
    (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hx : M35.cylinderCoordinateEquiv.symm (0, s) ∈ U)
    (k : ℕ) (hk : k ≤ ⌊epsilon⁻¹⌋₊) :
    let H : CovariantTensorEvaluation 3 E 2 := fun y v =>
      g1.inner y (v 0) (v 1) - (M35.cylinderEuclideanMetric u hu).inner y (v 0) (v 1)
    (M35.cylinderEuclideanMetric u hu).tensorNorm
      (D0.iteratedCovariantTensorDerivative H k)
      (M35.cylinderCoordinateEquiv.symm (0, s)) ≤ epsilon := by
  let H : CovariantTensorEvaluation 3 E 2 := fun y v =>
    g1.inner y (v 0) (v 1) - (M35.cylinderEuclideanMetric u hu).inner y (v 0) (v 1)
  have hn := cap_model_metricDifference_norm_sq u hu g1 D0 q B hU hcoeff s hx k
  have hterm := M35.roundCylinder_derivative_norm_le_jet hu B (q, s) hk
  obtain ⟨bound, hbound, hjet⟩ := hclose.2
  have hsq : ((M35.cylinderEuclideanMetric u hu).tensorNorm
      (D0.iteratedCovariantTensorDerivative H k)
      (M35.cylinderCoordinateEquiv.symm (0, s))) ^ 2 ≤ epsilon ^ 2 :=
    hn.le.trans (hterm.trans ((hjet (q, s) hs).trans hbound.le))
  have hnonneg : 0 ≤ (M35.cylinderEuclideanMetric u hu).tensorNorm
      (D0.iteratedCovariantTensorDerivative H k)
      (M35.cylinderCoordinateEquiv.symm (0, s)) := Real.sqrt_nonneg _
  exact (sq_le_sq₀ hnonneg hepsilon.le).mp hsq



theorem cap_model_twoDerivative_energy_le_jet
    (u : ℝ) (hu : u < 1) (B : RoundCylinderTwoTensor)
    (g1 : RiemannianMetric 3 E)
    (D0 : LeviCivitaData (M35.cylinderEuclideanMetric u hu))
    (q : UnitTwoSphere) {U : Set E} (hU : IsOpen U)
    (hcoeff : ∀ x ∈ U, ∀ i j : Fin 3,
      g1.inner x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient B (chartAt E2 q) (M35.cylinderCoordinateEquiv x) i j)
    (s : ℝ) (hx : M35.cylinderCoordinateEquiv.symm (0, s) ∈ U)
    (order : ℕ) (horder : 2 ≤ order) :
    let H : CovariantTensorEvaluation 3 E 2 := fun y v =>
      g1.inner y (v 0) (v 1) - (M35.cylinderEuclideanMetric u hu).inner y (v 0) (v 1)
    let g0 := M35.cylinderEuclideanMetric u hu
    let x := M35.cylinderCoordinateEquiv.symm (0, s)
    (g0.tensorNorm H x) ^ 2 + (g0.tensorNorm (D0.covariantTensorDerivative H) x) ^ 2 +
      (g0.tensorNorm (D0.covariantTensorDerivative (D0.covariantTensorDerivative H)) x) ^ 2 ≤
        roundCylinderJetErrorSquared u B order (q, s) := by
  let H : CovariantTensorEvaluation 3 E 2 := fun y v =>
    g1.inner y (v 0) (v 1) - (M35.cylinderEuclideanMetric u hu).inner y (v 0) (v 1)
  let f : ℕ → ℝ := fun j => roundCylinderTensorNormSquared u (chartAt E2 q)
    (chartAt E2 q q, s)
    (roundCylinderIteratedDerivative u (chartAt E2 q) B j (chartAt E2 q q, s))
  have hnorm (j : ℕ) : ((M35.cylinderEuclideanMetric u hu).tensorNorm
      (D0.iteratedCovariantTensorDerivative H j)
      (M35.cylinderCoordinateEquiv.symm (0, s))) ^ 2 = f j :=
    cap_model_metricDifference_norm_sq u hu g1 D0 q B hU hcoeff s hx j
  have hnonneg (j : ℕ) : 0 ≤ f j := by rw [← hnorm j]; exact sq_nonneg _
  have hsum : ∑ j ∈ Finset.range 3, f j ≤ ∑ j ∈ Finset.range (order + 1), f j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun j _ _ => hnonneg j)
  have hthree : f 0 + f 1 + f 2 ≤ roundCylinderJetErrorSquared u B order (q, s) := by
    change f 0 + f 1 + f 2 ≤ ∑ j ∈ Finset.range (order + 1), f j
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] using hsum
  dsimp only
  change ((M35.cylinderEuclideanMetric u hu).tensorNorm
      (D0.iteratedCovariantTensorDerivative H 0) _) ^ 2 +
    ((M35.cylinderEuclideanMetric u hu).tensorNorm
      (D0.iteratedCovariantTensorDerivative H 1) _) ^ 2 +
    ((M35.cylinderEuclideanMetric u hu).tensorNorm
      (D0.iteratedCovariantTensorDerivative H 2) _) ^ 2 ≤ _
  simpa only [hnorm] using hthree

end PoincareConjecture.M47
