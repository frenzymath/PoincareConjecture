import PoincareConjecture.Proofs.M38.SphereBundleIncidentAssembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (x : eventDiscardedOpen F T hT) (t : Ico (F.event T hT).tMinus T)

theorem sphereBundle_incident_assembly_of_late_chart
    (Q : GeneralizedSliceCarrier.{u}) [CompactSpace Q.carrier] (B : SurgerySphereBundle Q)
    (e : OpenPartialHomeomorph (F.slice t.val).carrier Q.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hsource : (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ e.source) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    (Nonempty (SurgerySphereBundle A) ∨ Nonempty (SurgeryPositiveSpaceform A)) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) (F.slice t.val).carrier Q.carrier ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := he
    contMDiffOn_invFun := hi }
  let c := ((F.event T hT).pre_identify t).toPartialDiffeomorph.trans d
  apply sphereBundle_incident_assembly_of_component_chart F T hT P x Q B
    c.toOpenPartialHomeomorph c.contMDiffOn_toFun c.contMDiffOn_invFun
  intro y hy
  exact ⟨mem_univ _, hsource ⟨y, hy, rfl⟩⟩

theorem sphereBundle_incident_assembly_of_fibration
    {X : Set (F.slice t.val).carrier}
    (C : SphereBundleCircleCertificate (F.metric t.val) X)
    (hsource : (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ C.carrier) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    (Nonempty (SurgerySphereBundle A) ∨ Nonempty (SurgeryPositiveSpaceform A)) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  obtain ⟨y, hC⟩ := C.component
  let Q := componentCarrier (F.slice t.val) y
  have hc : IsCompact (connectedComponent y) := hC ▸ C.compact
  let : CompactSpace Q.carrier := isCompact_iff_compactSpace.mp hc
  let B := bundleOnComponent (F.slice t.val) C y hC
  let d := regionPartialDiffeomorph (reverseRegions (componentRegionEquivalence (F.slice t.val) y))
    (componentOpen (F.slice t.val) y).isOpen isOpen_univ
  apply sphereBundle_incident_assembly_of_late_chart F T hT P x t Q B
    d.toOpenPartialHomeomorph d.contMDiffOn_toFun d.contMDiffOn_invFun
  exact hsource.trans hC.subset

end PoincareConjecture.M38
