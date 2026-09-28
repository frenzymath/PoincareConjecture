import PoincareConjecture.Proofs.M38.UnattachedGeometry
import PoincareConjecture.Proofs.M38.WholeComponentAssembly
import PoincareConjecture.Proofs.M38.CappedCanonicalRegions











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)




theorem exists_unattached_component_assemblies
    (N : RepairedNeckCapTopologyTheory.{u}) (hF : SurgeryFlowAdmissible F)
    (hepsilon : F.parameters.epsilon ≤ N.epsilon₀) :
    ∀ x : eventDiscardedOpen F T hT,
      (∀ i, ConnectedComponents.mk (P i).attachmentPoint ≠ ConnectedComponents.mk x) →
      ∃ n : ℕ, ∃ D : Fin n → GeneralizedSliceCarrier.{u},
        (∀ j, IsCompact (univ : Set (D j).carrier)) ∧
        (∀ j, IsConnected (univ : Set (D j).carrier)) ∧
        (∀ j, Nonempty (SurgerySphereBundle (D j)) ∨
          Nonempty (SurgeryPositiveSpaceform (D j))) ∧
        Nonempty (SmoothFiniteConnectedSumAssembly D
          (componentCarrier (cappedDiscardedCarrier F T hT P)
            (cappedOldInclusion F T hT P x))) := by
  obtain ⟨t, _, _, htcompact, hcontrol⟩ := exists_nonempty_late_slice F hF T hT
  let : CompactSpace (F.slice t.val).carrier := isCompact_univ_iff.mp htcompact
  intro x hunattached
  let d := (unattachedAmbientComponentDiffeomorph F T hT P x hunattached).symm.trans
    (componentDiffeomorph ((F.event T hT).pre_identify t) x.val)
  have hcanonical (y : (F.slice t.val).carrier)
      (hy : y ∈ connectedComponent ((F.event T hT).pre_identify t x.val)) :
      SurgeryCanonicalControl F t.val y F.parameters.epsilon F.parameters.C := by
    have hyback : ((F.event T hT).pre_identify t).symm y ∈ connectedComponent x.val :=
      ((componentDiffeomorph ((F.event T hT).pre_identify t) x.val).symm ⟨y, hy⟩).property
    rw [← unattached_component_eq_ambient F T hT P x hunattached] at hyback
    have hnot := connectedComponentIn_subset (F.event T hT).retained_preᶜ x.val hyback
    simpa only [Diffeomorph.apply_symm_apply] using
      hcontrol (((F.event T hT).pre_identify t).symm y)
        (fun h => hnot (interior_subset h))
  obtain ⟨n, D, hc, hn, hs, ⟨S⟩⟩ := whole_canonical_component_assembly N F t.val
    ((F.event T hT).pre_identify t x.val) isClosed_connectedComponent.isCompact
    hcanonical hepsilon
  exact ⟨n, D, hc, hn, hs, exists_transportAssembly S d.symm⟩



theorem exists_zeroCap_discarded_assembly
    (N : RepairedNeckCapTopologyTheory.{u}) (hF : SurgeryFlowAdmissible F)
    (hcount : (F.event T hT).cap_count = 0)
    (hepsilon : F.parameters.epsilon ≤ N.epsilon₀) :
    ∃ n : ℕ, ∃ D : Fin n → GeneralizedSliceCarrier.{u},
      (∀ j, IsCompact (univ : Set (D j).carrier)) ∧
      (∀ j, IsConnected (univ : Set (D j).carrier)) ∧
      (∀ j, Nonempty (SurgerySphereBundle (D j)) ∨
        Nonempty (SurgeryPositiveSpaceform (D j))) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly D (cappedDiscardedCarrier F T hT P)) := by
  apply exists_classifiedAssembly_of_components (cappedDiscardedCarrier F T hT P)
    (cappedDiscardedCarrier_compact F T hT P)
  intro q
  obtain ⟨x, hx⟩ := capped_component_representative F T hT P (ConnectedComponents.mk q)
  have hcarrier : componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x) =
      componentCarrier (cappedDiscardedCarrier F T hT P) q := by
    apply congrArg (openCarrier (cappedDiscardedCarrier F T hT P))
    apply TopologicalSpace.Opens.ext
    exact ConnectedComponents.coe_eq_coe.mp hx
  rw [← hcarrier]
  apply exists_unattached_component_assemblies F T hT P N hF hepsilon x
  intro i
  have hi := i.isLt
  omega

end PoincareConjecture.M38
