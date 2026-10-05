import PoincareLib.Topology.Manifold.Surgery.GroupEffects.Main
import PoincareLib.Topology.Manifold.Surgery.Children.Main
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Finite.Main
import PoincareLib.Geometry.RicciFlow.Surgery.Global.Assembly

/-!
# Poincare ancestry on the exact global flow

Apply M56's constructed Poincare branch to the actual M52 flow and raw M38
topology. The primitive flow view is definitionally the same flow; no local
group witness or all-event simple-connectivity premise is supplied here.
Source: Morgan--Tian Proposition 15.3, Corollary 15.4 and Definition 18.2,
pp. 357--359 and 419--420.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [CompactSpace M] [SimplyConnectedSpace M]
  {N : NormalizedInitialMetric (M := M)}

/-- Apply the supplied M56/M54/M55 services on the exact M52 flow view,
retaining their local data provenance. Source: Morgan--Tian Proposition
15.3 and Definition 18.2, pp. 357--358 and 419--420. -/
theorem m56PoincareAncestryFromTheories
    (G56 : RepairedAncestryTheory.{u})
    (G54 : RepairedGroupEffectsTheory.{u})
    (G55 : RepairedChildComponentsTheory.{u})
    (G : RepairedGlobalFlowData N)
    (L : RawLocalSurgeryTopologyData G.certificate.flow) :
    Nonempty {P : M56PoincareAncestryData (m52CoreFlowData G).flow L //
      M56PoincareProviderRealization G54 G55 P} :=
  G56.poincare G54 G55 N G L

/-- Supply the three earlier theorem services. The output type contains only
the actual flow, local topology and constructed ancestry, with no admitted
theorem constants in its type. Source: Morgan--Tian Corollary 15.4 and
Definition 18.2, pp. 358--359 and 419--420. -/
theorem m56PoincareAncestryFromMilestones
    (G : RepairedGlobalFlowData N)
    (L : RawLocalSurgeryTopologyData G.certificate.flow) :
    Nonempty (M56PoincareAncestryData (m52CoreFlowData G).flow L) := by
  obtain ⟨P, _hP⟩ := m56PoincareAncestryFromTheories
    repairedFiniteAncestry repairedGroupEffects repairedChildComponents G L
  exact ⟨P⟩

end PoincareMT
