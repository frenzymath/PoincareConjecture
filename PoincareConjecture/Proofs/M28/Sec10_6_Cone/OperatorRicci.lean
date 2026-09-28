import PoincareConjecture.Proofs.M04.PointwiseFlatness
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem sectional_nonneg_of_nonnegative_operator_m28
    (D : LeviCivitaData g) (x : M)
    (hD : D.NonnegativeCurvatureOperator x)
    (v w : TangentSpace (𝓡 n) x) :
    0 ≤ D.curvatureTensor x v w v w := by
  have hA : IsSkewCoefficient 2 ![![0, 1], ![-1, 0]] := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  have hh := D.curvatureOperator_nonneg_in_frame x hD ![v, w] _ hA
  norm_num [Fin.sum_univ_two] at hh
  have hfirst := M04.curvatureTensor_swap_first D x w v v w
  have hlast := M04.curvatureTensor_swap_last D x v w w v
  have hboth := M04.curvatureTensor_swap_first D x w v w v
  linarith

theorem nonnegativeRicci_at_of_nonnegativeOperator
    (D : LeviCivitaData g) (x : M)
    (hD : D.NonnegativeCurvatureOperator x) :
    ∀ v, 0 ≤ D.ricci x v v := by
  intro v
  exact M04.nonneg_ricci_of_nonnegativeSectionalAt D x
    (fun a b => D.sectional_nonneg_of_nonnegative_operator_m28 x hD a b) v

theorem nonnegativeRicci_of_nonnegativeOperator
    (D : LeviCivitaData g)
    (hD : ∀ x, D.NonnegativeCurvatureOperator x) :
    D.NonnegativeRicciCurvature := by
  intro x v
  exact D.nonnegativeRicci_at_of_nonnegativeOperator x (hD x) v

end PoincareConjecture.LeviCivitaData
