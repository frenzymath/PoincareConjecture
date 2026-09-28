import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.DefectTestIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

theorem exists_raw_vector_heat_test_bound
    {J I : Set ℝ} (F : RicciFlow n V J) (hI : IsCompact I) (hIJ : I ⊆ J)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (k : Fin n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ I, ∀ X : V → V, ContDiff ℝ ∞ X →
      ∀ δ : ℝ, 0 ≤ δ →
      (∀ x ∈ tsupport φ,
        ((F.metric t).tensorNorm (killingDefectTensor (F.connection t) X) x) ^ 2 ≤ δ ^ 2) →
      |∫ x, φ x * (@Add.add V inferInstance
        (∑ a, fieldHessian (F.connection t) X x
          ((F.metric t).orthonormalBasis x a) ((F.metric t).orthonormalBasis x a))
        (RicciFlow.ricciSharp (F.connection t) x (X x))) k| ≤ C * δ := by
  classical
  let a := fun l i j t => defectTestCoefficient (F.metric t) φ k l i j
  have ha (l i j : Fin n) : ContDiffOn ℝ ∞
      (Function.uncurry (a l i j)) (I ×ˢ univ) :=
    (defectTestCoefficient_family_contDiffOn F hφ k l i j).mono (prod_mono hIJ Subset.rfl)
  have has (l i j : Fin n) (t : ℝ) (_ht : t ∈ I) : ContDiff ℝ ∞ (a l i j t) :=
    defectTestCoefficient_contDiff (F.metric t) hφ k l i j
  have ha0 (l i j : Fin n) (t : ℝ) (_ht : t ∈ I) (x : V) (hx : x ∉ tsupport φ) :
      a l i j t x = 0 := defectTestCoefficient_zero_off (F.metric t) φ k l i j hx
  choose C₀ hC₀ h₀ using fun l i j : Fin n =>
    exists_raw_covariant_derivative_test_slab_bound F hI hIJ hc (a l i j)
      (ha l i j) (has l i j) (ha0 l i j) (e i) (e j) (e l)
  choose C₁ hC₁ h₁ using fun l i j : Fin n =>
    exists_raw_covariant_derivative_test_slab_bound F hI hIJ hc (a l i j)
      (ha l i j) (has l i j) (ha0 l i j) (e l) (e i) (e j)
  let C := ∑ l, ∑ i, ∑ j, (C₀ l i j + (1 / 2 : ℝ) * C₁ l i j)
  refine ⟨C, Finset.sum_nonneg (fun l _ => Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => add_nonneg (hC₀ l i j)
      (mul_nonneg (by norm_num) (hC₁ l i j))))), ?_⟩
  intro t ht X hX δ hδ hbound
  let H : V → (Fin 2 → V) → ℝ := killingDefectTensor (F.connection t) X
  have hH : IsSmoothCovariantTensor H :=
    isSmoothCovariantTensor_killingDefectTensor (F.connection t) X hX
  have hterm (l i j : Fin n) :
      |(∫ x, a l i j t x * (F.connection t).covariantTensorDerivative H x ![e i, e j, e l]) -
        (1 / 2 : ℝ) * (∫ x, a l i j t x *
          (F.connection t).covariantTensorDerivative H x ![e l, e i, e j])| ≤
      (C₀ l i j + (1 / 2 : ℝ) * C₁ l i j) * δ := by
    have hb₀ := h₀ l i j t ht H hH δ hδ hbound
    have hb₁ := h₁ l i j t ht H hH δ hδ hbound
    have htri := abs_sub
      (∫ x, a l i j t x * (F.connection t).covariantTensorDerivative H x ![e i, e j, e l])
      ((1 / 2 : ℝ) * (∫ x, a l i j t x *
        (F.connection t).covariantTensorDerivative H x ![e l, e i, e j]))
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at htri
    nlinarith only [hb₀, hb₁, htri]
  rw [integral_vector_heat_component_eq_defect_tests (F.connection t) X hX hφ hc]
  calc
    _ ≤ ∑ l, |∑ i, ∑ j,
        ((∫ x, a l i j t x * (F.connection t).covariantTensorDerivative H x ![e i, e j, e l]) -
        (1 / 2 : ℝ) * (∫ x, a l i j t x *
          (F.connection t).covariantTensorDerivative H x ![e l, e i, e j]))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, ∑ i, ∑ j, (C₀ l i j + (1 / 2 : ℝ) * C₁ l i j) * δ := by
      apply Finset.sum_le_sum
      intro l _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => hterm l i j))
    _ = C * δ := by simp only [C, Finset.sum_mul]

end PoincareConjecture.M35.Uniqueness.Heat
