import PoincareConjecture.Proofs.M56.FiniteAncestry
import PoincareConjecture.Proofs.M56.EventWitness










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture



theorem m56PoincareConstructor (G54 : RepairedGroupEffectsTheory.{u})
    (G55 : RepairedChildComponentsTheory.{u})
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [CompactSpace M]
    [SimplyConnectedSpace M]
    (N : NormalizedInitialMetric (M := M)) (G : RepairedGlobalFlowData N)
    (L : RawLocalSurgeryTopologyData G.certificate.flow) :
    Nonempty {P : M56PoincareAncestryData G.certificate.flow L //
      M56PoincareProviderRealization G54 G55 P} := by
  classical
  let F := G.certificate.flow
  let : SimplyConnectedSpace (F.slice 0).carrier :=
    G.certificate.initial_identification.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  have hzero : M56PointGroups (F.slice 0) := fun _ => inferInstance
  have hconn : IsConnected (univ : Set (F.slice 0).carrier) := isConnected_univ
  let W := m56PoincareWitness G54 G55 L hzero
  let A := Classical.choice (m56FiniteAncestry G54 W hconn hzero
    (fun H _ => G.certificate.local_finite (Icc 0 H) isCompact_Icc))
  let P : M56PoincareAncestryData F L := {
    witness := W
    topology_source := fun _ _ _ => rfl
    ancestry := A
    component_simply_connected := fun t ht C =>
      m56SelectedComponent_simplyConnected C (m56RawPointGroups G54 L hzero t ht) }
  refine ⟨⟨P, ?_⟩⟩
  constructor
  · intro T hT hpost
    rfl
  · intro T hT hpost hEffects
    rfl

end PoincareConjecture
