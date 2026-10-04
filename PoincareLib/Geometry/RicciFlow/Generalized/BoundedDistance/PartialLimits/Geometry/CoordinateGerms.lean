import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.Riemannian.Coordinates.Coefficients

/-!
# Pullback coefficients depend only on the coordinate germ

Equal map germs have the same value and manifold derivative, hence the
same actual metric coefficients. This permits different totalizations
of a captured chart in Morgan--Tian Proposition 5.14, pp. 90-91;
M28 derivation 76.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.RiemannianMetric

/-- Equality of coordinate germs identifies their actual pullback
coefficients at the tested point, without inferring regularity from the
totalized derivative (Proposition 5.14; derivation 76). -/
theorem pullbackCoefficients_eq_of_eventuallyEq
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {e f : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)} (h : e =ᶠ[𝓝 x] f) :
    g.pullbackCoefficients e x = g.pullbackCoefficients f x := by
  ext v w
  change g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w) = _
  rw [h.self_of_nhds, h.mfderiv_eq]
  rfl

end PoincareMT.RiemannianMetric
