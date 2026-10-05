import PoincareLib.Geometry.Riemannian.ScalarOperators.ConnectionIndependence

/-! Connection compatibility for the preserved Mapher M35 import. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

/- The source calls this theorem through dot notation with its two
  differentiability proofs explicit.  Keep that exact application shape while
  forwarding to the Horizon local-theory implementation. -/
namespace PoincareMT.LeviCivitaData
theorem horizon_mvfderiv_inner_explicit
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hY : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) =
      g.inner x (D.connection Y x (X x)) (Z x) +
        g.inner x (Y x) (D.connection Z x (X x)) :=
  PoincareMT.LeviCivitaData.localTheory_mvfderiv_inner D X Y Z hY hZ
end PoincareMT.LeviCivitaData
