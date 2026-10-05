import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Theory
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.GeometricLongConvergence
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.ShortLimitStatementAssembly
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.Assembly.LongLimitStatementAssembly
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Predecessors

/-!
# Conditional M30 contract assembly

The geometric, short, and long branches are now composed once their explicit
analytic service inputs are supplied.  The service bundle is a Prop boundary;
it does not add an inhabitant to the frozen predecessor record or import the
branch-only M28 library. Morgan--Tian Theorems 11.1 and 11.8, pp. 267--279,
with the convergence interface of Definition 5.12, p. 90.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

/-- The analytic inputs needed by the checked M30 assemblies.  The fields are
the within-jet suppliers followed by the common short-lifetime and long-branch
certificate services (Theorems 11.1 and 11.8, pp. 267--279). -/
structure M30ContractServices : Prop where
  mixed : WithinFlowJetBoundsService.{0, 0}
  flow : WithinBilinearFlowService.{0}
  slice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0}
  short : M30ShortControlService.{u}
  long : M30LongContractService.{u}

/-- Compose the checked branch assemblies into the frozen M30 theory once the
explicit service bundle is available (Theorems 11.1 and 11.8, pp. 267--279). -/
theorem repairedControlledBlowupLimitTheory_of_services
    (P : M30ControlledBlowupPredecessors.{u})
    (services : M30ContractServices.{u}) :
    RepairedControlledBlowupLimitTheory.{u} := by
  have hgeometric : ∀ (S : GeneralizedBlowupSequence.{u}) (T₀ : ℝ≥0∞),
      M30GeometricLongControls S T₀ →
      Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval T₀)) := by
    intro S T₀ H
    exact exists_geometric_long_generalizedBlowupConvergence P services.mixed
      services.flow services.slice S H
  obtain ⟨epsilonShort, hshortPos, hshortLe, hshort⟩ :=
    exists_shortLimitStatement_of_controlService P services.mixed services.flow
      services.slice services.short
  obtain ⟨epsilonLong, hlongPos, hlongLe, hlong⟩ :=
    exists_longLimitStatement_of_controlService P services.mixed services.flow
      services.slice services.long
  let epsilon₀ : ℝ := min epsilonShort epsilonLong
  have hepsilon₀ : 0 < epsilon₀ := lt_min hshortPos hlongPos
  have hepsilon₀_le : epsilon₀ ≤ 1 / 400 :=
    (min_le_left _ _).trans hshortLe
  have hshort' : M30ShortLimitStatement.{u} epsilon₀ := by
    intro S epsilon C kappa r₀ mu hepsilon H
    exact hshort S epsilon C kappa r₀ mu
      (hepsilon.trans (min_le_left _ _)) H
  have hlong' : M30LongLimitStatement.{u} epsilon₀ := by
    intro S epsilon C kappa r₀ mu T₀ hepsilon H
    exact hlong S epsilon C kappa r₀ mu T₀
      (hepsilon.trans (min_le_right _ _)) H
  exact {
    geometric_long := hgeometric
    limits := ⟨epsilon₀, hepsilon₀, hepsilon₀_le, hshort', hlong'⟩ }

end PoincareMT.M30
