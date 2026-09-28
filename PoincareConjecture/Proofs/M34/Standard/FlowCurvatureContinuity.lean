import PoincareConjecture.Proofs.M04.FlowCurvatureEnergy










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.RicciFlow



theorem continuousOn_curvatureDerivativeNorm
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) (m : ℕ) :
    ContinuousOn (fun p : ℝ × M => (F.connection p.1).curvatureDerivativeNorm m p.2)
      (J ×ˢ univ) := by
  have hsq := (M04.contMDiffOn_flow_curvatureDerivativeEnergy F m).continuousOn
  apply hsq.sqrt.congr
  intro p _hp
  change (F.connection p.1).curvatureDerivativeNorm m p.2 =
    Real.sqrt (((F.connection p.1).curvatureDerivativeNorm m p.2) ^ 2)
  rw [Real.sqrt_sq_eq_abs]
  exact (abs_of_nonneg (Real.sqrt_nonneg _)).symm

end PoincareConjecture.RicciFlow
