import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.ScalarTrace

/-!
# A scalar evolution margin from a small Laplacian

Morgan--Tian equation (3.7), printed p. 41, and Claim 11.35, pp. 289-291.
The Ricci trace inequality converts an actual small-Laplacian hypothesis
to a signed scalar evolution bound. The neck estimate discharging that
hypothesis and the time derivative identity are separate obligations.
Derivation: `claim11_35-scalar-laplacian-jets.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT.M32

/-- The three-dimensional trace inequality leaves a positive quadratic
margin in equation (3.7), p. 41, once the actual scalar Laplacian is small;
this is the algebraic step in Claim 11.35, printed p. 289. -/
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

end PoincareMT.M32
