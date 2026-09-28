import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.CoefficientBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory

set_option autoImplicit false

open scoped BigOperators Manifold ContDiff Bundle

namespace Poincare.Geometry.Curvature.Operator

variable {I : Type*} [Fintype I]

theorem sqrt_sum_sq_le_card_mul
    (f : I → I → I → I → ℝ) (K : ℝ)
    (hK : 0 ≤ K)
    (hcomp : ∀ i j k l, |f i j k l| ≤ K) :
    Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l, (f i j k l) ^ 2) ≤
      (Fintype.card I : ℝ) ^ 2 * K := by
  have hsq : ∀ i j k l, (f i j k l) ^ 2 ≤ K ^ 2 := by
    intro i j k l
    nlinarith [sq_abs (f i j k l), hcomp i j k l,
      abs_nonneg (f i j k l), hK]
  have hsum : (∑ i, ∑ j, ∑ k, ∑ l, (f i j k l) ^ 2) ≤
      (Fintype.card I : ℝ) ^ 4 * K ^ 2 := by
    calc
      (∑ i, ∑ j, ∑ k, ∑ l, (f i j k l) ^ 2) ≤
          ∑ i, ∑ j, ∑ k, ∑ l, K ^ 2 := by
            exact Finset.sum_le_sum fun i _ ↦
              Finset.sum_le_sum fun j _ ↦
                Finset.sum_le_sum fun k _ ↦
                  Finset.sum_le_sum fun l _ ↦ hsq i j k l
      _ = (Fintype.card I : ℝ) ^ 4 * K ^ 2 := by
        simp [Finset.card_univ, pow_succ, mul_assoc, mul_left_comm, mul_comm]
  have hcard : 0 ≤ (Fintype.card I : ℝ) ^ 2 * K := by positivity
  apply (Real.sqrt_le_iff).2
  constructor
  · exact hcard
  · nlinarith [hsum]

theorem curvature_tensor_norm_le_of_component_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M}
    (D : PoincareConjecture.LeviCivitaData g) (x : M) (K : ℝ)
    (hK : 0 ≤ K)
    (hcomp : ∀ i j k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      |D.curvatureTensor x (g.orthonormalBasis x i)
        (g.orthonormalBasis x j) (g.orthonormalBasis x k)
        (g.orthonormalBasis x l)| ≤ K) :
    D.curvatureTensorNorm x ≤
      (Fintype.card (Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) : ℝ) ^ 2 * K := by
  unfold PoincareConjecture.LeviCivitaData.curvatureTensorNorm
  exact sqrt_sum_sq_le_card_mul _ _ hK hcomp

end Poincare.Geometry.Curvature.Operator

namespace PoincareConjecture

open scoped Manifold ContDiff Bundle BigOperators

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

namespace LeviCivitaData

theorem abs_curvatureTensor_component_le_of_operator_bound
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M) (K : ℝ)
    (hK : 0 ≤ K) (hoperator : CurvatureOperatorBound D K x)
    (hcalculus : D.CurvatureTensorCalculus)
    (i j k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    |D.curvatureTensor x (g.orthonormalBasis x i)
      (g.orthonormalBasis x j) (g.orthonormalBasis x k)
      (g.orthonormalBasis x l)| ≤ K := by
  let b := g.orthonormalBasis x
  let R := fun i j k l ↦ D.curvatureTensor x (b i) (b j) (b k) (b l)
  have hsym := hcalculus.2.2.2.1
  have hlast : ∀ i j k l, R i j k l = -R i j l k := by
    intro i j k l
    exact (hsym x (b i) (b j) (b k) (b l)).1
  have hpair : ∀ i j k l, R i j k l = R k l i j := by
    intro i j k l
    exact (hsym x (b i) (b j) (b k) (b l)).2.1
  have hfirst : ∀ i j k l, R i j k l = -R j i k l := by
    intro i j k l
    rw [hpair i j k l, hlast k l i j, hpair k l j i]
  exact Poincare.Geometry.Curvature.Operator.abs_component_le_of_operator_bound
    R K hK hfirst hlast hpair hoperator i j k l

theorem curvatureTensorNorm_le_of_operator_bound
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M) (K : ℝ)
    (hK : 0 ≤ K) (hoperator : CurvatureOperatorBound D K x)
    (hcalculus : D.CurvatureTensorCalculus) :
    D.curvatureTensorNorm x ≤ (n : ℝ) ^ 2 * K := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n :=
    finrank_euclideanSpace_fin
  simpa only [Fintype.card_fin, hdim] using
    Poincare.Geometry.Curvature.Operator.curvature_tensor_norm_le_of_component_bound
      D x K hK (abs_curvatureTensor_component_le_of_operator_bound
        D x K hK hoperator hcalculus)

theorem per_slice_curvatureTensorNorm_bound
    {J : Set ℝ} (F : RicciFlow n M J) (t : ℝ) (K : ℝ)
    (hK : 0 ≤ K)
    (hoperator : ∀ x : M, CurvatureOperatorBound (F.connection t) K x)
    (hcalculus : (F.connection t).CurvatureTensorCalculus) :
    ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ (n : ℝ) ^ 2 * K := by
  intro x
  exact curvatureTensorNorm_le_of_operator_bound (F.connection t) x K hK
    (hoperator x) hcalculus

theorem per_slice_curvatureTensorNorm_bound_of_curvature_theory
    (hM04 : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} (F : RicciFlow n M J)
    (hoperator : ∀ t ∈ J, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : M, CurvatureOperatorBound (F.connection t) K x) :
    ∀ t ∈ J, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ C := by
  intro t ht
  obtain ⟨K, hK, hbound⟩ := hoperator t ht
  refine ⟨(n : ℝ) ^ 2 * K, mul_nonneg (sq_nonneg _) hK, ?_⟩
  exact per_slice_curvatureTensorNorm_bound F t K hK hbound
    (hM04.tensor_calculus n M (F.metric t) (F.connection t))

end LeviCivitaData
end PoincareConjecture
