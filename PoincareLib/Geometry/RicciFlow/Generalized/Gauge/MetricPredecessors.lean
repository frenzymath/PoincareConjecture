import PoincareLib.Geometry.Riemannian.Curvature.Calculus
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Statements/M12MetricPredecessors.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Declaration bodies are unchanged;
only imports and module placement differ. See
`references/ricci-flow/mapher/spacetime-port.json`. -/

/-!
# Narrow metric inputs for M12

Morgan-Tian Theorem 1.2, formula (1.1), and Definition 1.4, pp. 3-7.
These are the actual M03 connection and M04 tensor-calculus interfaces used
by the generalized equation construction. Compact Ricci-flow existence or
the full curvature-estimate package is not a substitute for these inputs.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- Connection existence, local regularity and tensor calculus on the
specified carrier universe. M12 consumes this at both `u` and `0`. -/
structure M12MetricPredecessors (n : ℕ) : Prop where
  connection_exists : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] (g : RiemannianMetric n M),
    Nonempty (LeviCivitaData g)
  connection_regular : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (U : Set M), IsOpen U →
    ∀ (Y : (x : M) → TangentSpace (𝓡 n) x),
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U →
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun x ↦ Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        x (D.connection Y x)) U
  curvature_calculus : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g), D.CurvatureTensorCalculus

end PoincareMT
