import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.DefectTestCoefficient








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

theorem weighted_vector_heat_component_eq
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (X : V → V) (hX : ContDiff ℝ ∞ X) (φ : V → ℝ) (x : V) (k : Fin n) :
    φ x * (@Add.add V inferInstance
      (∑ a, fieldHessian D X x (g.orthonormalBasis x a) (g.orthonormalBasis x a))
      (RicciFlow.ricciSharp D x (X x))) k =
      ∑ l, ∑ i, ∑ j,
        (defectTestCoefficient g φ k l i j x *
          D.covariantTensorDerivative (killingDefectTensor D X) x ![e i, e j, e l] -
        (1 / 2 : ℝ) * (defectTestCoefficient g φ k l i j x *
          D.covariantTensorDerivative (killingDefectTensor D X) x ![e l, e i, e j])) := by
  rw [vector_heat_component_eq_defect_coordinates D X hX]
  simp only [Finset.mul_sum, mul_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [defectTestCoefficient]
  ring

theorem integrable_defectTest_derivative
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {H : V → (Fin 2 → V) → ℝ} (hH : IsSmoothCovariantTensor H)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (k l i j : Fin n) (u v w : V) :
    Integrable (fun x => defectTestCoefficient g φ k l i j x *
      D.covariantTensorDerivative H x ![u, v, w]) :=
  ((defectTestCoefficient_contDiff g hφ k l i j).continuous.mul
    (covariant_twoTensor_fixed_contDiff D hH u v w).continuous
      ).integrable_of_hasCompactSupport
        (defectTestCoefficient_hasCompactSupport g hc k l i j).mul_right

theorem integral_vector_heat_component_eq_defect_tests
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (X : V → V) (hX : ContDiff ℝ ∞ X)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (k : Fin n) :
    (∫ x, φ x * (@Add.add V inferInstance
      (∑ a, fieldHessian D X x (g.orthonormalBasis x a) (g.orthonormalBasis x a))
      (RicciFlow.ricciSharp D x (X x))) k) =
      ∑ l, ∑ i, ∑ j,
        ((∫ x, defectTestCoefficient g φ k l i j x *
          D.covariantTensorDerivative (killingDefectTensor D X) x ![e i, e j, e l]) -
        (1 / 2 : ℝ) * (∫ x, defectTestCoefficient g φ k l i j x *
          D.covariantTensorDerivative (killingDefectTensor D X) x ![e l, e i, e j])) := by
  let H : V → (Fin 2 → V) → ℝ := killingDefectTensor D X
  have hH : IsSmoothCovariantTensor H := isSmoothCovariantTensor_killingDefectTensor D X hX
  let L : Fin n → Fin n → Fin n → V → ℝ := fun l i j x =>
    defectTestCoefficient g φ k l i j x * D.covariantTensorDerivative H x ![e i, e j, e l]
  let R : Fin n → Fin n → Fin n → V → ℝ := fun l i j x =>
    defectTestCoefficient g φ k l i j x * D.covariantTensorDerivative H x ![e l, e i, e j]
  have hleft (l i j : Fin n) : Integrable (L l i j) :=
    integrable_defectTest_derivative D hH hφ hc k l i j (e i) (e j) (e l)
  have hright (l i j : Fin n) : Integrable (R l i j) :=
    integrable_defectTest_derivative D hH hφ hc k l i j (e l) (e i) (e j)
  have hterm (l i j : Fin n) : Integrable (fun x => L l i j x - (1 / 2 : ℝ) * R l i j x) :=
    (hleft l i j).sub ((hright l i j).const_mul (1 / 2 : ℝ))
  simp only [weighted_vector_heat_component_eq D X hX]
  change (∫ x, ∑ l, ∑ i, ∑ j, (L l i j x - (1 / 2 : ℝ) * R l i j x)) =
    ∑ l, ∑ i, ∑ j, ((∫ x, L l i j x) - (1 / 2 : ℝ) * ∫ x, R l i j x)
  rw [integral_finsetSum _ (fun l _ => integrable_finsetSum _
    (fun i _ => integrable_finsetSum _ (fun j _ => hterm l i j)))]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hterm l i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hterm l i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact (integral_sub (hleft l i j) ((hright l i j).const_mul (1 / 2 : ℝ))).trans
    (congrArg (fun z => (∫ x, L l i j x) - z) (integral_const_mul _ _))

end PoincareConjecture.M35.Uniqueness.Heat
