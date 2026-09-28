import PoincareConjecture.Proofs.M38.ProjectiveCapRegion
import PoincareConjecture.Proofs.M38.LateSpaceformIncident










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (x : eventDiscardedOpen F T hT) (t : Ico (F.event T hT).tMinus T)



theorem spaceform_incident_assembly_of_projective_cap
    (C : CapCertificate (F.metric t.val)) (hkind : C.model_kind = .puncturedProjective)
    (hsource : (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ C.carrier) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    Nonempty (SurgeryPositiveSpaceform A) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  let d := regionPartialDiffeomorph (projectiveCapRegionEquivalence (F.slice t.val) C hkind)
    C.carrier_open isClosed_singleton.isOpen_compl
  exact spaceform_incident_assembly_of_late_chart F T hT P x t projectiveCarrier
    projectiveSpaceform d.toOpenPartialHomeomorph d.contMDiffOn_toFun d.contMDiffOn_invFun hsource



theorem spaceform_incident_assembly_of_cap
    (C : CapCertificate (F.metric t.val))
    (hsource : (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ C.carrier) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    Nonempty (SurgeryPositiveSpaceform A) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  cases hkind : C.model_kind with
  | euclidean =>
      exact spherical_incident_assembly_of_euclidean_cap F T hT P x t C hkind hsource
  | puncturedProjective =>
      exact spaceform_incident_assembly_of_projective_cap F T hT P x t C hkind hsource




theorem spaceform_incident_assembly_of_cap_comparison
    (C : CapCertificate (F.metric t.val)) {U : Set (F.slice t.val).carrier}
    (hU : IsOpen U)
    (E : SurgeryRegionEquivalence (F.slice t.val) (F.slice t.val) U C.carrier)
    (hsource : (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ U) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    Nonempty (SurgeryPositiveSpaceform A) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  cases hkind : C.model_kind with
  | euclidean =>
      have C' : CapModelEquivalence .euclidean C.puncture C.carrier :=
        hkind ▸ C.model_equivalence
      obtain ⟨e, hes, he, hi⟩ := exists_spherical_chart_of_euclidean_region
        (composeRegions E (euclideanCapRegionEquivalence C')) hU isOpen_univ
      exact spherical_incident_assembly_of_late_chart F T hT P x t e he hi
        (hsource.trans hes.symm.subset)
  | puncturedProjective =>
      let d := regionPartialDiffeomorph
        (composeRegions E (projectiveCapRegionEquivalence (F.slice t.val) C hkind))
        hU isClosed_singleton.isOpen_compl
      exact spaceform_incident_assembly_of_late_chart F T hT P x t projectiveCarrier
        projectiveSpaceform d.toOpenPartialHomeomorph d.contMDiffOn_toFun
        d.contMDiffOn_invFun hsource

end PoincareConjecture.M38
