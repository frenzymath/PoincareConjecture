import PoincareLib.Topology.Manifold.Surgery.Event.Capping.CappingComponents
import PoincareLib.Topology.Manifold.Surgery.Event.Event.EventDiscardedComponents
import PoincareLib.Topology.Manifold.Surgery.Event.Canonical.CanonicalRegions

/-!
# Canonical models for the exact sources of capped components

The old inclusion identifies components of the actual discarded interior
with components of its capped quotient. Their closed source regions are
transported to one common late slice, where the supplied canonical control
and Appendix A theory yield the actual containing-model alternatives.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

/-- Each actual capped component has a representative in the old
discarded interior, with its exact component class preserved. -/
theorem capped_component_representative
    (c : ConnectedComponents (CappedDiscardedSpace F T hT P)) :
    ∃ x : eventDiscardedOpen F T hT,
      ConnectedComponents.mk (cappedOldInclusion F T hT P x) = c := by
  let H := cappedComponentsHomeomorph F T hT P
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (H.symm c)
  refine ⟨x, ?_⟩
  change H (ConnectedComponents.mk x) = c
  rw [hx, H.apply_symm_apply]

/-- At one common strict late time, every actual capped component has
an exact compact connected source region with canonical control up to
the boundary and one of Appendix A's containing-model alternatives.
Source: Proposition 15.3, pp. 357-358, using Assumption (6). This makes
no standard-model identification of the capped smooth component. -/
theorem exists_capped_canonical_regions
    (N : RepairedNeckCapTopologyTheory.{u}) (hF : SurgeryFlowAdmissible F)
    (hepsilon : F.parameters.epsilon ≤ N.epsilon₀) :
    ∃ t : Set.Ico (F.event T hT).tMinus T,
      (F.event T hT).disappearing_start < t.val ∧ t.val ∈ F.time_domain ∧
      ∃ x : ConnectedComponents (CappedDiscardedSpace F T hT P) → eventDiscardedOpen F T hT,
      ∃ region : ConnectedComponents (CappedDiscardedSpace F T hT P) →
          Set (F.slice t.val).carrier,
        (∀ c, ConnectedComponents.mk (cappedOldInclusion F T hT P (x c)) = c) ∧
        (∀ c, region c = (F.event T hT).pre_identify t ''
          closure (connectedComponentIn (F.event T hT).retained_preᶜ (x c).val)) ∧
        (∀ c, IsConnected (region c)) ∧
        (∀ c, IsCompact (region c)) ∧
        (∀ c y, y ∈ region c →
          SurgeryCanonicalControl F t.val y F.parameters.epsilon F.parameters.C) ∧
        (∀ c,
          (∃ H : ConnectedNeckCapCover (F.metric t.val),
            H.X = region c ∧ H.epsilon = F.parameters.epsilon ∧
            H.epsilon_threshold = N.epsilon₀ ∧ H.cap_constant = F.parameters.C ∧
            Nonempty (RepairedNeckCapTopologyData (F.metric t.val) H)) ∨
          (∃ Q : SingularCComponent (F.metric t.val) (F.connection t.val) F.parameters.C,
            region c ⊆ Q.carrier) ∨
          (∃ Q : SingularRoundComponent (F.metric t.val) F.parameters.epsilon,
            region c ⊆ Q.carrier)) := by
  classical
  obtain ⟨t, ht, htdomain, _, hcontrol⟩ := exists_nonempty_late_slice F hF T hT
  choose x hx using capped_component_representative F T hT P
  let region : ConnectedComponents (CappedDiscardedSpace F T hT P) →
      Set (F.slice t.val).carrier := fun c =>
    (F.event T hT).pre_identify t ''
      closure (connectedComponentIn (F.event T hT).retained_preᶜ (x c).val)
  have hconnected (c) : IsConnected (region c) :=
    (isConnected_connectedComponentIn_iff.mpr (x c).property).closure.image _
      ((F.event T hT).pre_identify t).continuous.continuousOn
  have hcompact (c) : IsCompact (region c) :=
    (event_discarded_component_closure_compact F T hT (x c).val).image
      ((F.event T hT).pre_identify t).continuous
  have hcanonical (c) : ∀ y ∈ region c,
      SurgeryCanonicalControl F t.val y F.parameters.epsilon F.parameters.C := by
    rintro y ⟨z, hz, rfl⟩
    apply hcontrol z
    rw [event_discarded_component_closure F T hT (x c).val (x c).property] at hz
    exact connectedComponentIn_subset _ _ hz
  refine ⟨t, ht, htdomain, x, region, hx, fun _ => rfl,
    hconnected, hcompact, hcanonical, ?_⟩
  intro c
  exact canonical_region N F t.val (hconnected c) (hcanonical c) hepsilon

end PoincareMT.M38
