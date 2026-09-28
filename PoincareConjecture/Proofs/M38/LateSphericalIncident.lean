import PoincareConjecture.Proofs.M38.IncidentSphericalRegion
import PoincareConjecture.Proofs.M38.SphericalModelRegions










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (x : eventDiscardedOpen F T hT) (t : Ico (F.event T hT).tMinus T)



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

end PoincareConjecture.M38
