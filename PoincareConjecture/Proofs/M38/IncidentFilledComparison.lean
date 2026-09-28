import PoincareConjecture.Proofs.M38.IncidentSphericalRegion
import PoincareConjecture.Proofs.M38.FilledRegionComplement
import PoincareConjecture.Proofs.M38.EnclosingBallSphere

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem incident_filled_frontier_comparison
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
    (x : eventDiscardedOpen F T hT) (Q : GeneralizedSliceCarrier.{u})
    (hQ : IsPreconnected (univ : Set Q.carrier))
    (R : IncidentComponentRegion F T hT P x Q)
    (hfill : ∀ i, ∃ B : SurgeryBallEmbedding Q,
      frontier B.closedBall = range (R.sphere i)) :
    (∃ s : OpenPartialHomeomorph Q.carrier sphereCarrier.{u}.carrier,
      closure R.region ⊆ s.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ s s.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ s.symm s.target) ∨
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) Q.carrier
      (componentCarrier (cappedDiscardedCarrier F T hT P)
        (cappedOldInclusion F T hT P x)).carrier ∞) := by
  classical
  choose B hB using hfill
  have hsep (i j) (hij : i ≠ j) :
      Disjoint (frontier (B i).closedBall) (frontier (B j).closedBall) := by
    rw [hB, hB]
    exact R.sphere_disjoint i j hij
  have hfrontier : frontier R.region = ⋃ i, frontier (B i).closedBall := by
    simpa only [hB] using R.frontier_eq
  rcases enclosing_ball_or_exact_complement_of_fillings hQ R.open_region R.connected
      B hsep hfrontier with ⟨i, henclosed⟩ | ⟨hdisjoint, hcompl⟩
  · left
    let pole : sphereCarrier.{u}.carrier := ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
    let s := regionPartialDiffeomorph (enclosingBallSphereCoordinates (B i) pole)
      (surgeryBall_image_open (B i)) (surgeryBall_image_open (spherePoleReferenceBall pole))
    exact ⟨s.toOpenPartialHomeomorph,
      henclosed.trans (surgeryBall_closedBall_subset_image (B i)),
      s.contMDiffOn_toFun, s.contMDiffOn_invFun⟩
  · right
    have hzero (i) : R.collar i '' (univ ×ˢ ({0} : Set ℝ)) = frontier (B i).closedBall := by
      rw [hB]
      ext y
      constructor
      · rintro ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
        have hs0 : s = 0 := hs
        subst s
        exact ⟨z, (R.collar_zero i z).symm⟩
      · rintro ⟨z, rfl⟩
        exact ⟨(z, 0), by simp, R.collar_zero i z⟩
    obtain ⟨B', r, hr, _, hsep', hRB, hmatch⟩ := exists_collared_region_complement
      B hdisjoint hcompl R.collar R.collar_smooth R.collar_inverse_smooth
      R.width R.width_pos R.collar_source hzero R.collar_positive
    obtain ⟨d, _, _⟩ := exists_incident_diffeomorph_of_matched_balls F T hT P x Q R.identify
      B' hsep' hRB (fun i => R.collar i) r R.width (fun i => (hr i).1) R.width_pos
      hmatch R.collar_compare
    exact ⟨d⟩

end PoincareConjecture.M38
