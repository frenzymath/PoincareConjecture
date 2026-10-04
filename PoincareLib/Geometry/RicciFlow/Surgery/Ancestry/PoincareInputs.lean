import PoincareLib.Topology.Manifold.ThreeDimensional.ClosedSimplyConnected
import PoincareLib.Topology.Manifold.EmbeddedSphere.Separation
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.TransportTheory

/-!
# M57 input construction on literal M56 paths

Apply the reviewed Poincare input constructor without asking a caller to
supply event metrics, separation, retained regions, homology or point paths.
Source: Morgan--Tian Proposition 15.12 and the setup of Proposition 18.18,
pp. 365 and 430--431; the complete derivation is in
`reviews/contracts/2026-09-17-m57-poincare-inputs-round1.md`.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Select the produced primitive input on each literal ancestry path. -/
theorem m57PoincareInputsFromTheories
    (hM57 : RepairedTransportTheory.{u})
    (P02 : RepairedClosedTopologyProvider.{u})
    (G53 : RepairedSphereSeparationTheory.{u})
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    (L : RawLocalSurgeryTopologyData D.flow)
    (P : M56PoincareAncestryData D.flow L)
    (K : RepairedComparisonMapData D)
    (C : RepairedComparisonHomotopyData D K) :
    Nonempty (∀ (T : ℝ) (hT : T ∈ D.flow.time_domain)
      (x : (D.flow.slice T).carrier),
      RepairedAncestryTransportInput D P.witness
        (P.ancestry.path_for T hT x) K C) := by
  exact ⟨fun T hT x =>
    Classical.choice (hM57.poincare_inputs P02 G53 D L P K C T hT x)⟩

/-- Supply the existing M02, M53 and M57 milestones on the caller's actual
flow, raw local topology, ancestry, and comparison providers. -/
theorem m57PoincareInputsFromMilestones
    (repairedAncestryTransport : RepairedTransportTheory.{u})
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    (L : RawLocalSurgeryTopologyData D.flow)
    (P : M56PoincareAncestryData D.flow L)
    (K : RepairedComparisonMapData D)
    (C : RepairedComparisonHomotopyData D K) :
    Nonempty (∀ (T : ℝ) (hT : T ∈ D.flow.time_domain)
      (x : (D.flow.slice T).carrier),
      RepairedAncestryTransportInput D P.witness
        (P.ancestry.path_for T hT x) K C) := by
  refine m57PoincareInputsFromTheories repairedAncestryTransport
    ?_ repairedSphereSeparation D L P K C
  intro M _ _ _ _ _ _ _
  exact closedSimplyConnectedThreeManifoldTopology

end PoincareMT
