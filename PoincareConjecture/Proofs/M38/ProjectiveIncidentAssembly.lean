import PoincareConjecture.Proofs.M38.ProjectiveDoubleSphereFilling
import PoincareConjecture.Proofs.M38.DihedralCutComparison
import PoincareConjecture.Proofs.M38.ProjectiveIncidentFillings
import PoincareConjecture.Proofs.M38.SpaceformIncidentAssembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem projectiveDouble_incident_assembly_of_component_chart
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
    (x : eventDiscardedOpen F T hT) (Q : GeneralizedSliceCarrier.{u})
    (C : SmoothProjectiveDoubleModel Q.carrier)
    (e : OpenPartialHomeomorph (F.slice (F.event T hT).tMinus).carrier Q.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hsource : closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆ e.source) :
    ∃ n : ℕ, ∃ D : Fin n → GeneralizedSliceCarrier.{u},
      (∀ j, IsCompact (univ : Set (D j).carrier)) ∧
      (∀ j, IsConnected (univ : Set (D j).carrier)) ∧
      (∀ j, Nonempty (SurgerySphereBundle (D j)) ∨ Nonempty (SurgeryPositiveSpaceform (D j))) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly D
        (componentCarrier (cappedDiscardedCarrier F T hT P)
          (cappedOldInclusion F T hT P x))) := by
  classical
  obtain ⟨R, hR⟩ := exists_incident_component_region F T hT P x Q e he hi hsource
  by_cases hfill : ∀ i, ∃ B : SurgeryBallEmbedding Q,
      frontier B.closedBall = range (R.sphere i)
  · exact projectiveDouble_incident_assembly_of_fillings F T hT P x Q C e he hi hsource R hR hfill
  · have hclosure : e '' closure
        (connectedComponentIn (F.event T hT).retained_preᶜ x.val) = closure R.region := by
      rw [hR]
      exact partialHomeomorph_image_closure e
        (event_discarded_component_closure_compact F T hT x.val) hsource
    obtain ⟨i, hiFill⟩ := not_forall.mp hfill
    have hn : ¬ ∃ B : SurgeryBallEmbedding Q,
        frontier B.closedBall = range (fun z : UnitTwoSphere => R.collar i (z, 0)) := by
      simpa only [R.collar_zero] using hiFill
    obtain ⟨q, hq, hsurj, hfibers, η, hη, hηwidth, D, hD⟩ :=
      (projectiveDouble_sphere_filling_or_lifted_coordinates Q C (R.collar i)
        (R.collar_smooth i) (R.collar_inverse_smooth i) (R.width_pos i)
        (R.collar_source i)).resolve_left hn
    let shift := cylinderAffineChange 1 (-η / 2) (by norm_num)
    have havoid : Disjoint (closure R.region)
        (range (fun z : UnitTwoSphere => q ((shift.trans D) (z, 0)))) := by
      apply disjoint_left.mpr
      rintro y hy ⟨z, rfl⟩
      change q (D (z, 1 * 0 + -η / 2)) ∈ closure R.region at hy
      rw [hD _ (by rw [abs_lt]; constructor <;> linarith)] at hy
      exact R.collar_negative i z (1 * 0 + -η / 2) (by linarith) (by linarith) hy
    rcases dihedral_cut_connected_standard_chart q hq hsurj hfibers
        (shift.trans D).toHomeomorph R.connected.closure havoid
        with ⟨s, hRs⟩ | ⟨a, n, hreflection, s, hss, hRs, hformula⟩
    · obtain ⟨hspace, hass⟩ := spherical_incident_assembly_of_component_chart F T hT P x
        (e.trans s.toOpenPartialHomeomorph)
        (s.contMDiffOn_toFun.comp (he.mono inter_subset_left) inter_subset_right)
        (hi.comp (s.contMDiffOn_invFun.mono inter_subset_left) inter_subset_right)
        (fun y hy => ⟨hsource hy, hRs (hclosure ▸ mem_image_of_mem e hy)⟩)
      exact ⟨1, fun _ => _, fun _ => (Classical.choice hspace).compact,
        fun _ => (Classical.choice hspace).connected, fun _ => Or.inr hspace, hass⟩
    · obtain ⟨hspace, hass⟩ := spaceform_incident_assembly_of_component_chart F T hT P x
        projectiveCarrier projectiveSpaceform (e.trans s.toOpenPartialHomeomorph)
        (s.contMDiffOn_toFun.comp (he.mono inter_subset_left) inter_subset_right)
        (hi.comp (s.contMDiffOn_invFun.mono inter_subset_left) inter_subset_right)
        (fun y hy => ⟨hsource hy, hRs (hclosure ▸ mem_image_of_mem e hy)⟩)
      exact ⟨1, fun _ => _, fun _ => (Classical.choice hspace).compact,
        fun _ => (Classical.choice hspace).connected, fun _ => Or.inr hspace, hass⟩

end PoincareConjecture.M38
