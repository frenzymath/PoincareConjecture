import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem LeviCivitaData.curvatureTensorNorm_eq_zero_of_dimension_le_one
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (hn : n ≤ 1) (x : M) :
    D.curvatureTensorNorm x = 0 := by
  let b := g.orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n :=
    finrank_euclideanSpace_fin
  have hindex (k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) : k = l := by
    apply Fin.ext
    have hk := k.isLt
    have hl := l.isLt
    omega
  have hzero (i j k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      D.curvatureTensor x (b i) (b j) (b k) (b l) = 0 := by
    rw [hindex l k]
    exact D.curvatureTensor_zero_last x (b i) (b j) (b k)
  change Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
    (D.curvatureTensor x (b i) (b j) (b k) (b l)) ^ 2) = 0
  simp only [hzero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, Real.sqrt_zero]

theorem RicciFlow.curvatureTensorNorm_eq_zero_of_dimension_le_one
    {J : Set ℝ} (F : RicciFlow n M J) (hn : n ≤ 1) (t : ℝ) (x : M) :
    (F.connection t).curvatureTensorNorm x = 0 :=
  (F.connection t).curvatureTensorNorm_eq_zero_of_dimension_le_one hn x

theorem RicciFlow.curvatureTensorNorm_bound_zero_of_dimension_le_one
    {J : Set ℝ} (F : RicciFlow n M J) (hn : n ≤ 1) :
    ∀ t : ℝ, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ 0 := by
  intro t x
  exact le_of_eq (F.curvatureTensorNorm_eq_zero_of_dimension_le_one hn t x)

end PoincareConjecture
