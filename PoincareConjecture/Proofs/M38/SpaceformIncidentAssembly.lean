import PoincareConjecture.Proofs.M38.IncidentSphericalRegion
import PoincareConjecture.Proofs.M38.SpaceformSphereFilling
import PoincareConjecture.Proofs.M38.FilledRegionComplement
import PoincareConjecture.Proofs.M38.EnclosingBallSphere

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem spaceform_incident_assembly_of_component_chart
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
    (x : eventDiscardedOpen F T hT) (Q : GeneralizedSliceCarrier.{u})
    (S : SurgeryPositiveSpaceform Q)
    (e : OpenPartialHomeomorph (F.slice (F.event T hT).tMinus).carrier Q.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hsource : closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆
      e.source) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    Nonempty (SurgeryPositiveSpaceform A) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  classical
  obtain ⟨R, hR⟩ := exists_incident_component_region F T hT P x Q e he hi hsource
  obtain ⟨p, hp⟩ := R.connected.nonempty
  have hpf (i) : p ∉ range (R.sphere i) := by
    intro h
    have hfront : p ∈ frontier R.region := R.frontier_eq.symm ▸ mem_iUnion.mpr ⟨i, h⟩
    exact hfront.2 (R.open_region.interior_eq.symm ▸ hp)
  choose B hB using fun i =>
    exists_spaceform_sphere_filling Q S (R.sphere i) (R.sphere_smooth i) p (hpf i)
  have hdisjoint (i j) (hij : i ≠ j) :
      Disjoint (frontier (B i).closedBall) (frontier (B j).closedBall) := by
    rw [hB, hB]
    exact R.sphere_disjoint i j hij
  have hfrontier : frontier R.region = ⋃ i, frontier (B i).closedBall := by
    simpa only [hB] using R.frontier_eq
  rcases enclosing_ball_or_exact_complement_of_fillings S.connected.isPreconnected
      R.open_region R.connected B hdisjoint hfrontier with ⟨i, henclosed⟩ | ⟨hsep, hcompl⟩
  · let pole : sphereCarrier.{u}.carrier := ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
    let b := regionPartialDiffeomorph (enclosingBallSphereCoordinates (B i) pole)
      (surgeryBall_image_open (B i)) (surgeryBall_image_open (spherePoleReferenceBall pole))
    let c := e.trans b.toOpenPartialHomeomorph
    have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c c.source :=
      b.contMDiffOn_toFun.comp (he.mono inter_subset_left) inter_subset_right
    have hci : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm c.target :=
      hi.comp (b.contMDiffOn_invFun.mono inter_subset_left) inter_subset_right
    apply spherical_incident_assembly_of_component_chart F T hT P x c hc hci
    intro y hy
    refine ⟨hsource hy, ?_⟩
    apply surgeryBall_closedBall_subset_image (B i)
    apply henclosed
    rw [hR, ← partialHomeomorph_image_closure e
      (event_discarded_component_closure_compact F T hT x.val) hsource]
    exact mem_image_of_mem e hy
  · have hzero (i) : R.collar i '' (univ ×ˢ ({0} : Set ℝ)) = frontier (B i).closedBall := by
      rw [hB]
      ext y
      constructor
      · rintro ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
        have hs0 : s = 0 := hs
        subst s
        exact ⟨z, (R.collar_zero i z).symm⟩
      · rintro ⟨z, rfl⟩
        exact ⟨(z, 0), by simp, R.collar_zero i z⟩
    obtain ⟨D, r, hr, _, hDsep, hRD, hmatch⟩ := exists_collared_region_complement
      B hsep hcompl R.collar R.collar_smooth R.collar_inverse_smooth R.width R.width_pos
      R.collar_source hzero R.collar_positive
    obtain ⟨d, _, _⟩ := exists_incident_diffeomorph_of_matched_balls F T hT P x Q R.identify
      D hDsep hRD (fun i => R.collar i) r R.width (fun i => (hr i).1) R.width_pos
      hmatch R.collar_compare
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    have hcompact : IsCompact (univ : Set A.carrier) := by
      rw [← image_univ_of_surjective d.surjective]
      exact S.compact.image d.contMDiff.continuous
    exact ⟨⟨spaceformAlongDiffeomorph A S.metric S.connection d.symm hcompact
      (componentCarrier_connected _ _) S.round⟩,
      ⟨(singletonDisjointUnion A).toAssembly⟩⟩

end PoincareConjecture.M38
