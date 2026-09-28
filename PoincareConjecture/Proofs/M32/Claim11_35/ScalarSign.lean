import PoincareConjecture.Proofs.M04.ScalarEstimates











set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M32




theorem scalar_evolution_ge_half_sq_of_laplacian_bound
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (x : M)
    (h : |D.laplacian D.scalarCurvature x| ≤ (D.scalarCurvature x) ^ 2 / 6) :
    (D.scalarCurvature x) ^ 2 / 2 ≤
      D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x := by
  have htrace := D.scalarCurvature_sq_le x
  norm_num only [Nat.cast_ofNat] at htrace
  have hlow := (abs_le.mp h).1
  linarith

end PoincareConjecture.M32
