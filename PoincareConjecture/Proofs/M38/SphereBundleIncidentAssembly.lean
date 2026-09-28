import PoincareConjecture.Proofs.M38.SphereBundleSphereFilling
import PoincareConjecture.Proofs.M38.SphereBundleCutChart
import PoincareConjecture.Proofs.M38.SpaceformIncidentAssembly
import PoincareConjecture.Proofs.M38.ComponentTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem sphereBundle_incident_assembly_of_component_chart
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
    (x : eventDiscardedOpen F T hT) (Q : GeneralizedSliceCarrier.{u})
    [CompactSpace Q.carrier] (B : SurgerySphereBundle Q)
    (e : OpenPartialHomeomorph (F.slice (F.event T hT).tMinus).carrier Q.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hsource : closure (connectedComponentIn (F.event T hT).retained_preᶜ x.val) ⊆
      e.source) :
    let A := componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)
    (Nonempty (SurgerySphereBundle A) ∨ Nonempty (SurgeryPositiveSpaceform A)) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
  classical
  obtain ⟨R, hR⟩ := exists_incident_component_region F T hT P x Q e he hi hsource
  have hclosure : e '' closure
      (connectedComponentIn (F.event T hT).retained_preᶜ x.val) = closure R.region := by
    rw [hR]
    exact partialHomeomorph_image_closure e
      (event_discarded_component_closure_compact F T hT x.val) hsource
  have hspherical (s : OpenPartialHomeomorph Q.carrier sphereCarrier.{u}.carrier)
      (hs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ s s.source)
      (hsi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ s.symm s.target)
      (hRs : closure R.region ⊆ s.source) :
      let A := componentCarrier (cappedDiscardedCarrier F T hT P)
        (cappedOldInclusion F T hT P x)
      Nonempty (SurgeryPositiveSpaceform A) ∧
        Nonempty (SmoothFiniteConnectedSumAssembly (fun _ : Fin 1 => A) A) := by
    apply spherical_incident_assembly_of_component_chart F T hT P x (e.trans s)
      (hs.comp (he.mono inter_subset_left) inter_subset_right)
      (hi.comp (hsi.mono inter_subset_left) inter_subset_right)
    intro y hy
    exact ⟨hsource hy, hRs (hclosure ▸ mem_image_of_mem e hy)⟩
  by_cases hfill : ∀ i, ∃ D : SurgeryBallEmbedding Q,
      frontier D.closedBall = range (R.sphere i)
  · choose D hD using hfill
    have hQ : IsPreconnected (univ : Set Q.carrier) := by
      let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
        (isConnected_sphere (E := StandardCapSpace)
          (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
      obtain ⟨d, _⟩ := exists_sphereBundle_pullback_cylinder Q B
      let q := circlePullbackProjection Q B.projection B.projection_smooth
      have hq := circlePullback_projection_localDiffeomorph Q B.projection B.projection_smooth
      have hsurj : Function.Surjective (q ∘ d) :=
        (CirclePullback.projection_surjective B.projection).comp d.surjective
      simpa only [image_univ, hsurj.range_eq] using
        isPreconnected_univ.image (q ∘ d) (hq.contMDiff.comp d.contMDiff).continuous.continuousOn
    have hsep (i j) (hij : i ≠ j) :
        Disjoint (frontier (D i).closedBall) (frontier (D j).closedBall) := by
      rw [hD, hD]
      exact R.sphere_disjoint i j hij
    have hfrontier : frontier R.region = ⋃ i, frontier (D i).closedBall := by
      simpa only [hD] using R.frontier_eq
    rcases enclosing_ball_or_exact_complement_of_fillings hQ R.open_region R.connected
        D hsep hfrontier with ⟨i, henclosed⟩ | ⟨hdisjoint, hcompl⟩
    · let pole : sphereCarrier.{u}.carrier := ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
      let s := regionPartialDiffeomorph (enclosingBallSphereCoordinates (D i) pole)
        (surgeryBall_image_open (D i)) (surgeryBall_image_open (spherePoleReferenceBall pole))
      obtain ⟨hspace, hass⟩ := hspherical s.toOpenPartialHomeomorph
        s.contMDiffOn_toFun s.contMDiffOn_invFun
        (henclosed.trans (surgeryBall_closedBall_subset_image (D i)))
      exact ⟨Or.inr hspace, hass⟩
    · have hzero (i) : R.collar i '' (univ ×ˢ ({0} : Set ℝ)) = frontier (D i).closedBall := by
        rw [hD]
        ext y
        constructor
        · rintro ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
          have hs0 : s = 0 := hs
          subst s
          exact ⟨z, (R.collar_zero i z).symm⟩
        · rintro ⟨z, rfl⟩
          exact ⟨(z, 0), by simp, R.collar_zero i z⟩
      obtain ⟨D', r, hr, _, hsep', hRD, hmatch⟩ := exists_collared_region_complement
        D hdisjoint hcompl R.collar R.collar_smooth R.collar_inverse_smooth
        R.width R.width_pos R.collar_source hzero R.collar_positive
      obtain ⟨d, _, _⟩ := exists_incident_diffeomorph_of_matched_balls F T hT P x Q R.identify
        D' hsep' hRD (fun i => R.collar i) r R.width (fun i => (hr i).1) R.width_pos
        hmatch R.collar_compare
      exact ⟨Or.inl ⟨surgeryBundleAlongDiffeomorph B d.symm⟩,
        ⟨(singletonDisjointUnion _).toAssembly⟩⟩
  · obtain ⟨i, hiFill⟩ := not_forall.mp hfill
    have hn : ¬ ∃ D : SurgeryBallEmbedding Q,
        frontier D.closedBall = range (fun z : UnitTwoSphere => R.collar i (z, 0)) := by
      simpa only [R.collar_zero] using hiFill
    obtain ⟨η, hη, hηwidth, D, hD⟩ :=
      (sphereBundle_sphere_filling_or_lifted_coordinates Q B (R.collar i)
        (R.collar_smooth i) (R.collar_inverse_smooth i) (R.width_pos i)
        (R.collar_source i)).resolve_left hn
    let shift : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
        RoundCylinderSpace RoundCylinderSpace ∞ := {
      toFun := fun p => (p.1, p.2 - η / 2)
      invFun := fun p => (p.1, p.2 + η / 2)
      left_inv := fun p => Prod.ext rfl (sub_add_cancel _ _)
      right_inv := fun p => Prod.ext rfl (add_sub_cancel_right _ _)
      contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)
      contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_const) }
    have havoid : Disjoint (closure R.region) (range (fun z : UnitTwoSphere =>
        circlePullbackProjection Q B.projection B.projection_smooth ((shift.trans D) (z, 0)))) := by
      apply disjoint_left.mpr
      rintro y hy ⟨z, rfl⟩
      change circlePullbackProjection Q B.projection B.projection_smooth
        (D (z, 0 - η / 2)) ∈ closure R.region at hy
      rw [hD _ (by rw [abs_lt]; constructor <;> linarith)] at hy
      exact R.collar_negative i z (0 - η / 2) (by linarith) (by linarith) hy
    obtain ⟨s, hRs, hs, hsi⟩ := sphereBundle_cut_connected_spherical_chart Q B
      (shift.trans D) R.connected.closure havoid
    obtain ⟨hspace, hass⟩ := hspherical s hs hsi hRs
    exact ⟨Or.inr hspace, hass⟩

end PoincareConjecture.M38
