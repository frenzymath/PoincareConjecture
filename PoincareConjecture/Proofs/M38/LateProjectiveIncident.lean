import PoincareConjecture.Proofs.M38.ProjectiveIncidentAssembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

attribute [local instance] SmoothClosedComponentModel.model_topology
  SmoothClosedComponentModel.model_charted SmoothClosedComponentModel.model_manifold

theorem projectiveDouble_incident_assembly_of_closed_double
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
    (x : eventDiscardedOpen F T hT) (t : Ico (F.event T hT).tMinus T)
    {U : Set (F.slice t.val).carrier}
    (C : ClosedComponentCertificate .realProjectiveThreeConnectedSum U)
    (hsource : (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ U) :
    ∃ n : ℕ, ∃ D : Fin n → GeneralizedSliceCarrier.{u},
      (∀ j, IsCompact (univ : Set (D j).carrier)) ∧
      (∀ j, IsConnected (univ : Set (D j).carrier)) ∧
      (∀ j, Nonempty (SurgerySphereBundle (D j)) ∨ Nonempty (SurgeryPositiveSpaceform (D j))) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly D
        (componentCarrier (cappedDiscardedCarrier F T hT P)
          (cappedOldInclusion F T hT P x))) := by
  obtain ⟨y, hU⟩ := C.component
  have C' : ClosedComponentCertificate .realProjectiveThreeConnectedSum (connectedComponent y) :=
    hU ▸ C
  let Q := closedComponentModelCarrier (F.slice t.val) y C'.smooth_model
  let d₀ := regionPartialDiffeomorph
    (reverseRegions (componentRegionEquivalence (F.slice t.val) y))
    (componentOpen (F.slice t.val) y).isOpen isOpen_univ
  let d₁ := componentClosedModelDiffeomorph (F.slice t.val) y C'.smooth_model
  let d := d₀.trans d₁.toPartialDiffeomorph
  let e := ((F.event T hT).pre_identify t).toPartialDiffeomorph.trans d
  apply projectiveDouble_incident_assembly_of_component_chart F T hT P x Q
    C'.smooth_model.standard_smooth.some e.toOpenPartialHomeomorph
    e.contMDiffOn_toFun e.contMDiffOn_invFun
  intro z hz
  exact ⟨mem_univ _, hU.subset (hsource ⟨z, hz, rfl⟩), mem_univ _⟩

end PoincareConjecture.M38
