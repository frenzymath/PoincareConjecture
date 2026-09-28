import PoincareConjecture.Proofs.M38.SpaceformIncidentAssembly
import PoincareConjecture.Proofs.M38.LateSphericalIncident
import PoincareConjecture.Proofs.M38.RoundComponentSpaceforms










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (x : eventDiscardedOpen F T hT) (t : Ico (F.event T hT).tMinus T)



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

end PoincareConjecture.M38
