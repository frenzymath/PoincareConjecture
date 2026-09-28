import PoincareConjecture.Proofs.M38.UnattachedComponents
import PoincareConjecture.Proofs.M38.ComponentTransport
import PoincareConjecture.Proofs.M38.WholeComponentGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

noncomputable def unattachedAmbientOldDiffeomorph
    (x : eventDiscardedOpen F T hT)
    (hunattached : ∀ i,
      ConnectedComponents.mk (P i).attachmentPoint ≠ ConnectedComponents.mk x) :
    Diffeomorph (𝓡 3) (𝓡 3)
      (componentCarrier (F.slice (F.event T hT).tMinus) x.val).carrier
      (componentCarrier (openCarrier (F.slice (F.event T hT).tMinus)
        (eventDiscardedOpen F T hT)) x).carrier ∞ := by
  let A := F.slice (F.event T hT).tMinus
  let O := openCarrier A (eventDiscardedOpen F T hT)
  have heq := unattached_component_eq_ambient F T hT P x hunattached
  have hsub : connectedComponent x.val ⊆ (F.event T hT).retained_preᶜ := by
    rw [← heq]
    exact connectedComponentIn_subset _ _
  let forward : (componentCarrier A x.val).carrier → (componentCarrier O x).carrier :=
    fun y => ⟨⟨y.val, hsub y.property⟩, by
      have hy : y.val ∈ connectedComponent x.val := y.property
      rw [← heq, connectedComponentIn_eq_image
        (show x.val ∈ (F.event T hT).retained_preᶜ from x.property)] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have he : z = (⟨y.val, hsub y.property⟩ : eventDiscardedOpen F T hT) :=
        Subtype.ext hzy
      exact he ▸ hz⟩
  let inverse : (componentCarrier O x).carrier → (componentCarrier A x.val).carrier :=
    fun y => ⟨y.val.val, by
      change y.val.val ∈ connectedComponent x.val
      rw [← heq, connectedComponentIn_eq_image
        (show x.val ∈ (F.event T hT).retained_preᶜ from x.property)]
      exact ⟨y.val, y.property, rfl⟩⟩
  refine {
    toEquiv := {
      toFun := forward
      invFun := inverse
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun y => Subtype.ext (Subtype.ext rfl) }
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff (componentOpen O x) forward).mp
    apply (ContMDiff.subtypeVal_comp_iff (eventDiscardedOpen F T hT)
      (Subtype.val ∘ forward)).mp
    exact contMDiff_subtype_val (U := componentOpen A x.val)
  · apply (ContMDiff.subtypeVal_comp_iff (componentOpen A x.val) inverse).mp
    exact (contMDiff_subtype_val (U := eventDiscardedOpen F T hT)).comp
      (contMDiff_subtype_val (U := componentOpen O x))

noncomputable def unattachedAmbientComponentDiffeomorph
    (x : eventDiscardedOpen F T hT)
    (hunattached : ∀ i,
      ConnectedComponents.mk (P i).attachmentPoint ≠ ConnectedComponents.mk x) :
    Diffeomorph (𝓡 3) (𝓡 3)
      (componentCarrier (F.slice (F.event T hT).tMinus) x.val).carrier
      (componentCarrier (cappedDiscardedCarrier F T hT P)
        (cappedOldInclusion F T hT P x)).carrier ∞ :=
  (unattachedAmbientOldDiffeomorph F T hT P x hunattached).trans
    (unattachedComponentDiffeomorph F T hT P x hunattached)

theorem exists_unattached_component_geometry
    (N : RepairedNeckCapTopologyTheory.{u}) (hF : SurgeryFlowAdmissible F)
    (hepsilon : F.parameters.epsilon ≤ N.epsilon₀) :
    ∃ t : Set.Ico (F.event T hT).tMinus T,
      (F.event T hT).disappearing_start < t.val ∧ t.val ∈ F.time_domain ∧
      ∀ x : eventDiscardedOpen F T hT,
        (∀ i, ConnectedComponents.mk (P i).attachmentPoint ≠ ConnectedComponents.mk x) →
        Nonempty (SurgerySphereBundle (componentCarrier (cappedDiscardedCarrier F T hT P)
          (cappedOldInclusion F T hT P x))) ∨
        Nonempty (SurgeryPositiveSpaceform (componentCarrier (cappedDiscardedCarrier F T hT P)
          (cappedOldInclusion F T hT P x))) ∨
        Nonempty (ClosedComponentCertificate .realProjectiveThreeConnectedSum
          (connectedComponent ((F.event T hT).pre_identify t x.val))) := by
  classical
  obtain ⟨t, htlate, htdomain, htcompact, hcontrol⟩ := exists_nonempty_late_slice F hF T hT
  let : CompactSpace (F.slice t.val).carrier := isCompact_univ_iff.mp htcompact
  refine ⟨t, htlate, htdomain, ?_⟩
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
  rcases whole_canonical_component_geometry N F t.val
      ((F.event T hT).pre_identify t x.val) isClosed_connectedComponent.isCompact
      hcanonical hepsilon with hbundle | hspace | hdouble
  · exact Or.inl ⟨surgeryBundleAlongDiffeomorph (Classical.choice hbundle) d⟩
  · let S := Classical.choice hspace
    exact Or.inr (Or.inl ⟨spaceformAlongDiffeomorph
      (componentCarrier (cappedDiscardedCarrier F T hT P) (cappedOldInclusion F T hT P x))
      S.metric S.connection d
      (componentCarrier_compact _ (cappedDiscardedCarrier_compact F T hT P) _)
      (componentCarrier_connected _ _) S.round⟩)
  · exact Or.inr (Or.inr hdouble)

end PoincareConjecture.M38
