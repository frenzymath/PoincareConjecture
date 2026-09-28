import PoincareConjecture.Proofs.M38.IncidentFilledComparison
import PoincareConjecture.Proofs.M38.WholeComponentAssembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem projectiveDouble_incident_assembly_of_fillings
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
    (x : eventDiscardedOpen F T hT) (Q : GeneralizedSliceCarrier.{u})
    (C : SmoothProjectiveDoubleModel Q.carrier)
    (e : OpenPartialHomeomorph (F.slice (F.event T hT).tMinus).carrier Q.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hsource : closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ e.source)
    (R : IncidentComponentRegion F T hT P x Q)
    (hR : R.region = e '' connectedComponentIn (F.event T hT).retained_preᶜ x.val)
    (hfill : ∀ i, ∃ B : SurgeryBallEmbedding Q,
      frontier B.closedBall = range (R.sphere i)) :
    ∃ n : ℕ, ∃ D : Fin n → GeneralizedSliceCarrier.{u},
      (∀ j, IsCompact (univ : Set (D j).carrier)) ∧
      (∀ j, IsConnected (univ : Set (D j).carrier)) ∧
      (∀ j, Nonempty (SurgerySphereBundle (D j)) ∨ Nonempty (SurgeryPositiveSpaceform (D j))) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly D
        (componentCarrier (cappedDiscardedCarrier F T hT P)
          (cappedOldInclusion F T hT P x))) := by
  rcases incident_filled_frontier_comparison F T hT P x Q C.connected.isPreconnected R hfill
      with ⟨s, hRs, hs, hsi⟩ | hd
  · have hclosure : e '' closure
        (connectedComponentIn (F.event T hT).retained_preᶜ x.val) = closure R.region := by
      rw [hR]
      exact partialHomeomorph_image_closure e
        (event_discarded_component_closure_compact F T hT x.val) hsource
    obtain ⟨hspace, hass⟩ := spherical_incident_assembly_of_component_chart F T hT P x
      (e.trans s) (hs.comp (he.mono inter_subset_left) inter_subset_right)
      (hi.comp (hsi.mono inter_subset_left) inter_subset_right)
      (fun y hy => ⟨hsource hy, hRs (hclosure ▸ mem_image_of_mem e hy)⟩)
    exact ⟨1, fun _ => _, fun _ => (Classical.choice hspace).compact,
      fun _ => (Classical.choice hspace).connected, fun _ => Or.inr hspace, hass⟩
  · obtain ⟨d⟩ := hd
    obtain ⟨S⟩ := exists_projectiveDouble_assembly Q C
    refine ⟨2, ![projectiveCarrier, projectiveCarrier], ?_, ?_, ?_,
      exists_transportAssembly S d⟩
    · intro j
      fin_cases j <;> exact projectiveSpaceform.compact
    · intro j
      fin_cases j <;> exact projectiveSpaceform.connected
    · intro j
      fin_cases j <;> exact Or.inr ⟨projectiveSpaceform⟩

end PoincareConjecture.M38
