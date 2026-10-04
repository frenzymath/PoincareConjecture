import PoincareLib.Topology.Manifold.NeckCap.Models
import PoincareLib.Topology.Manifold.Surgery.Event.Incident.IncidentSphericalRegion
import PoincareLib.Topology.Manifold.Surgery.Event.Spherical.SphericalModelRegions

/-!
# Elementary canonical regions and the actual incident component

The event identification transports a late model chart back to the original
discarded component closure. Finite capping then constructs the standard
geometry and an assembly onto the literal capped component.
Source: Morgan--Tian Proposition 15.3, printed pp. 357-358.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (x : eventDiscardedOpen F T hT) (t : Ico (F.event T hT).tMinus T)

/-- A chart near the exact late image of the component closure supplies
the comparison for capping the original event component. -/
theorem spherical_incident_assembly_of_late_chart
    (e : OpenPartialHomeomorph (F.slice t.val).carrier sphereCarrier.{u}.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hsource : (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ e.source) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    Nonempty (SurgeryPositiveSpaceform A) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3)
      (F.slice t.val).carrier sphereCarrier.{u}.carrier ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := he
    contMDiffOn_invFun := hi }
  let c := ((F.event T hT).pre_identify t).toPartialDiffeomorph.trans d
  apply spherical_incident_assembly_of_component_chart F T hT P x
    c.toOpenPartialHomeomorph c.contMDiffOn_toFun c.contMDiffOn_invFun
  intro y hy
  exact ⟨mem_univ _, hsource ⟨y, hy, rfl⟩⟩

/-- Containment of the actual late component closure in a smooth sphere
component produces a sphere spaceform and an actual capped assembly. -/
theorem spherical_incident_assembly_of_closed_sphere
    {U : Set (F.slice t.val).carrier}
    (C : ClosedComponentCertificate .threeSphere U)
    (hsource : (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ U) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    Nonempty (SurgeryPositiveSpaceform A) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  let : LocallyConnectedSpace (F.slice t.val).carrier :=
    ChartedSpace.locallyConnectedSpace StandardCapSpace _
  have hU : IsOpen U := by
    obtain ⟨y, rfl⟩ := C.component
    exact isOpen_connectedComponent
  let d := regionPartialDiffeomorph (closedSphereRegionEquivalence C.smooth_model)
    hU isOpen_univ
  exact spherical_incident_assembly_of_late_chart F T hT P x t
    d.toOpenPartialHomeomorph d.contMDiffOn_toFun d.contMDiffOn_invFun hsource

/-- A Euclidean canonical cap containing the actual late closure supplies
the full filling and assembly, without assuming a standard capped model. -/
theorem spherical_incident_assembly_of_euclidean_cap
    (C : CapCertificate (F.metric t.val)) (hkind : C.model_kind = .euclidean)
    (hsource : (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ C.carrier) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    Nonempty (SurgeryPositiveSpaceform A) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  have H : CapModelEquivalence .euclidean C.puncture C.carrier := hkind ▸ C.model_equivalence
  obtain ⟨e, heq, he, hi⟩ := exists_spherical_chart_of_euclidean_region
    (euclideanCapRegionEquivalence H) C.carrier_open isOpen_univ
  apply spherical_incident_assembly_of_late_chart F T hT P x t e he hi
  rwa [heq]

/-- The actual tube coordinates suffice even when the compact discarded
region is a proper subset of the tube carrier. -/
theorem spherical_incident_assembly_of_tube
    {U : Set (F.slice t.val).carrier} (hU : IsOpen U) (C : OpenCylinderModel U)
    (hsource : (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ U) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    Nonempty (SurgeryPositiveSpaceform A) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  have hV : IsOpen {y : euclideanCarrier.{u}.carrier | 1 < ‖y.down‖} :=
    isOpen_lt continuous_const continuous_uliftDown.norm
  obtain ⟨e, heq, he, hi⟩ := exists_spherical_chart_of_euclidean_region
    (cylinderExteriorEquivalence C) hU hV
  apply spherical_incident_assembly_of_late_chart F T hT P x t e he hi
  rwa [heq]

end PoincareMT.M38
