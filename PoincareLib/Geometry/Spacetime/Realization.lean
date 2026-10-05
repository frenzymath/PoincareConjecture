import PoincareLib.Geometry.Spacetime.Realization.Conclusion
import PoincareLib.Geometry.Spacetime.Realization.Assembly
import PoincareLib.Geometry.Spacetime.Realization.OrdinaryProduct.Assembly

/-!
# M11 spacetime realization

Mapher's current M11 result adds local-diffeomorphism data for the selected
interval system to the earlier Horizon conclusion.  The extension below
preserves the old conclusion as a literal projection, so M12 consumers keep
their existing types and selected spacetime witness.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

/-- Current Mapher M11, imported at the stronger source-equivalent interface.

The construction is ported under the semantic realization namespace.  All
downstream interfaces use the checked projection theorem below and retain the
original Horizon definitions.
-/
theorem generalizedSpacetimeRealization (n : ℕ) :
    GeneralizedSpacetimeRealizationTheory.{u} n := by
  refine {
    realize := ?_,
    ordinary_product := ?_,
    realize_with_interval := ?_ }
  · intro X _ _ _ A
    exact ⟨GeneralizedFlowCarrierConclusionWithInterval.toConclusion
      (Poincare.Spacetime.Realization.adaptedCarrierConclusion A)⟩
  · intro M _ _ _ _ _ _ g I hg
    exact ⟨Poincare.Spacetime.Realization.ordinaryProductConclusion g I hg⟩
  · intro X _ _ _ A
    exact ⟨Poincare.Spacetime.Realization.adaptedCarrierConclusion A⟩

/-- Projection of the stronger imported result to the frozen M12-facing M11
interface. -/
theorem generalizedSpacetimeGeometry (n : ℕ) :
    GeneralizedSpacetimeGeometryTheory.{u} n :=
  (generalizedSpacetimeRealization n).toGeometryTheory

end PoincareMT
