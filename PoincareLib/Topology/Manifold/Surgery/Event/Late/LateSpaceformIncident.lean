import PoincareLib.Topology.Manifold.Surgery.Event.Spaceform.SpaceformIncidentAssembly
import PoincareLib.Topology.Manifold.Surgery.Event.Late.LateSphericalIncident
import PoincareLib.Topology.Manifold.Surgery.Event.Round.RoundComponentSpaceforms

/-!
# Closed projective and round certificates in incident capping

The certificate classifies its own containing component. Its smooth region
coordinates and the exact late closure containment feed the finite-capping
comparison, which classifies the actual capped event component separately.
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

/-- Carry an actual late comparison back through the event identification
before applying spaceform sphere filling and finite capping. -/
theorem spaceform_incident_assembly_of_late_chart
    (Q : GeneralizedSliceCarrier.{u}) (S : SurgeryPositiveSpaceform Q)
    (e : OpenPartialHomeomorph (F.slice t.val).carrier Q.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hsource : (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ e.source) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    Nonempty (SurgeryPositiveSpaceform A) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) (F.slice t.val).carrier Q.carrier ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := he
    contMDiffOn_invFun := hi }
  let c := ((F.event T hT).pre_identify t).toPartialDiffeomorph.trans d
  apply spaceform_incident_assembly_of_component_chart F T hT P x Q S
    c.toOpenPartialHomeomorph c.contMDiffOn_toFun c.contMDiffOn_invFun
  intro y hy
  exact ⟨mem_univ _, hsource ⟨y, hy, rfl⟩⟩

/-- A closed projective containing certificate supplies all model geometry
needed to classify and assemble the actual capped incident component. -/
theorem spaceform_incident_assembly_of_closed_projective
    {U : Set (F.slice t.val).carrier}
    (C : ClosedComponentCertificate .realProjectiveThree U)
    (hsource : (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ U) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    Nonempty (SurgeryPositiveSpaceform A) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  obtain ⟨y, hU⟩ := C.component
  have C' : ClosedComponentCertificate .realProjectiveThree (connectedComponent y) := hU ▸ C
  let Q := componentCarrier (F.slice t.val) y
  let S := projectiveSpaceformOnComponent (F.slice t.val) y C'
  let d := regionPartialDiffeomorph (reverseRegions (componentRegionEquivalence (F.slice t.val) y))
    (componentOpen (F.slice t.val) y).isOpen isOpen_univ
  apply spaceform_incident_assembly_of_late_chart F T hT P x t Q S
    d.toOpenPartialHomeomorph d.contMDiffOn_toFun d.contMDiffOn_invFun
  exact hsource.trans hU.subset

/-- The singular round certificate's stored curvature-one model and maps
produce an assembly on the actual capped component of any contained region. -/
theorem spaceform_incident_assembly_of_round_component
    (C : SingularRoundComponent (F.metric t.val) F.parameters.epsilon)
    (hsource : (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ C.carrier) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    Nonempty (SurgeryPositiveSpaceform A) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  let Q := componentCarrier (F.slice t.val) C.basepoint
  let S := roundSpaceformOnComponent (F.slice t.val) C C.basepoint C.component_eq
  let d := regionPartialDiffeomorph
    (reverseRegions (componentRegionEquivalence (F.slice t.val) C.basepoint))
    (componentOpen (F.slice t.val) C.basepoint).isOpen isOpen_univ
  apply spaceform_incident_assembly_of_late_chart F T hT P x t Q S
    d.toOpenPartialHomeomorph d.contMDiffOn_toFun d.contMDiffOn_invFun
  exact hsource.trans C.component_eq.subset

/-- Both topological alternatives of a singular C-component give the
actual incident assembly, using their existing smooth closed certificates. -/
theorem spaceform_incident_assembly_of_c_component
    (C : SingularCComponent (F.metric t.val) (F.connection t.val) F.parameters.C)
    (hsource : (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ C.carrier) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    Nonempty (SurgeryPositiveSpaceform A) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  rcases C.topology with hs | hp
  · exact spherical_incident_assembly_of_closed_sphere F T hT P x t
      (Classical.choice hs) hsource
  · exact spaceform_incident_assembly_of_closed_projective F T hT P x t
      (Classical.choice hp) hsource

end PoincareMT.M38
