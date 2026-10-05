import PoincareLib.Geometry.Riemannian.Metric.LocalExtension
import PoincareLib.Geometry.Riemannian.Coordinates.Coefficients

/-!
# Static realization of a smooth immersive metric pullback

Positive definiteness follows from the actual injective differential.
The local extension retains the metric coefficients on a neighborhood;
it does not assert any temporal coherence of the chosen extension.
Source: Morgan-Tian Theorems 11.8 and 12.28, pp. 276-277, 323-324;
M34 included-cylinder geometric-readout derivation. This exposes the
general local step used privately in lower M07 Convergence/LocalRealization.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

set_option backward.isDefEq.respectTransparency false in
/-- A smooth metric pullback with injective differential is realized
by an actual Euclidean metric near each source point (Theorem 12.28). -/
theorem exists_local_immersive_pullback_realization
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (f : EuclideanSpace ℝ (Fin n) → M)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hi : ∀ x ∈ U, Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    ∃ (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (_D : LeviCivitaData g') (V : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
        ∀ x ∈ V, g'.euclideanCoefficients x = g.pullbackCoefficients f x := by
  apply exists_local_realization hU hp (g.pullbackCoefficients f)
  · intro x hx
    exact (g.contDiffAt_pullbackCoefficients
      ((hf x hx).contMDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  · intro x hx v w
    exact g.symm (f x) _ _
  · intro x hx v hv
    apply g.pos (f x)
    intro hzero
    apply hv
    apply hi x hx
    rw [map_zero]
    convert! hzero using 1

end PoincareMT.RiemannianMetric
