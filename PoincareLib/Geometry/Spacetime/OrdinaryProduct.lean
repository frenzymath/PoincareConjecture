import PoincareLib.Geometry.Spacetime.GeometryTheory

/-!
# Ordinary-product realization

The ordinary-product part of the M11 conclusion already has the exact
frozen M12 representation.  This semantic module gives that selected record
a realization name without introducing a second, incompatible representation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

abbrev OrdinaryProductSpacetimeRealization {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) := OrdinaryProductSpacetimeConclusion g I

namespace OrdinaryProductSpacetimeRealization

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : ℝ → RiemannianMetric n M} {I : SpacetimeInterval}

/-- The realization is definitionally the record consumed by M12. -/
abbrev toConclusion (P : OrdinaryProductSpacetimeRealization g I) :
    OrdinaryProductSpacetimeConclusion g I := P

@[simp] theorem toConclusion_timeIntervals
    (P : OrdinaryProductSpacetimeRealization g I) :
    P.toConclusion.timeIntervals = P.timeIntervals := rfl

@[simp] theorem toConclusion_spacetime
    (P : OrdinaryProductSpacetimeRealization g I) :
    P.toConclusion.spacetime = P.spacetime := rfl

end OrdinaryProductSpacetimeRealization

end PoincareMT
