import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderOrdinaryTransport










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44




theorem exists_cylinder_through_ordinary_endpoint
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale c d : ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U)
    (hU : IsOpen U) (hcd : c < d) (r : ℝ) (hr : r ∈ Ico 0 c)
    (hJ : Ico (origin + r / scale) (origin + d / scale) ⊆ F.time_domain)
    (hNo : Disjoint F.surgery_times (Ioo (origin + r / scale) (origin + d / scale))) :
    ∃ E : SurgeryFlowCylinder F C origin scale (Ico 0 d) U,
      ∀ s (hs : s ∈ Ico 0 c) (hs' : s ∈ Ico 0 d) x,
        E.forward s hs' x = e.forward s hs x := by
  classical
  let bridge := cylinderSliceChart e hU r hr
  have hclock : StrictMono (fun s : ℝ => origin + s / scale) := by
    intro s t hst
    dsimp only
    linarith [(div_lt_div_iff_of_pos_right e.scale_pos).mpr hst]
  have hpostTime (s : ℝ) (hs : s < d) (hrs : r ≤ s) :
      origin + s / scale ∈ Ico (origin + r / scale) (origin + d / scale) :=
    ⟨hclock.monotone hrs, hclock hs⟩
  let post (s : ℝ) (hs : s < d) (hrs : r ≤ s) :=
    F.regularIdentifyIco hJ hNo ⟨origin + s / scale, hpostTime s hs hrs⟩
  let chart (s : ℝ) (hs : s ∈ Ico 0 d) :
      PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier
        (F.slice (origin + s / scale)).carrier ∞ :=
    if hsc : s < c then cylinderSliceChart e hU s ⟨hs.1, hsc⟩
    else bridge.trans (post s hs.2 (hr.2.le.trans (le_of_not_gt hsc))).toPartialDiffeomorph
  have hsource (s : ℝ) (hs : s ∈ Ico 0 d) : (chart s hs).source = U := by
    dsimp only [chart]
    split_ifs
    · rfl
    · change U ∩ bridge ⁻¹' (univ : Set (F.slice (origin + r / scale)).carrier) = U
      simp only [preimage_univ, inter_univ]
  have hbefore (s : ℝ) (hs : s ∈ Ico 0 d) (hsc : s < c) (x : C.carrier) :
      chart s hs x = e.forward s ⟨hs.1, hsc⟩ x := by
    dsimp only [chart]
    rw [dif_pos hsc]
    rfl
  have hafter (s : ℝ) (hs : s ∈ Ico 0 d) (hcs : c ≤ s) (x : C.carrier) :
      chart s hs x = post s hs.2 (hr.2.le.trans hcs) (e.forward r hr x) := by
    dsimp only [chart]
    rw [dif_neg (not_lt_of_ge hcs)]
    rfl
  have hoverlap (s : ℝ) (hs : s ∈ Ico 0 c) (hrs : r ≤ s) (x : C.carrier) (hx : x ∈ U) :
      post s (hs.2.trans hcd) hrs (e.forward r hr x) = e.forward s hs x :=
    cylinder_regularIdentifyIco e r hr hJ hNo s hs
      (hpostTime s (hs.2.trans hcd) hrs) x hx
  have hcross (a b : ℝ) (hab : a < b) (hK : Icc a b ⊆ F.time_domain)
      (hfree : Disjoint F.surgery_times (Ioc a b))
      (s : ℝ) (hs : s ∈ Ico 0 c) (t : ℝ) (ht : t ∈ Ico 0 d) (hct : c ≤ t)
      (hs' : origin + s / scale ∈ Icc a b) (ht' : origin + t / scale ∈ Icc a b)
      (x : C.carrier) (hx : x ∈ U) :
      (F.regular_slabs a b hab hK hfree).transport
        ⟨origin + s / scale, hs'⟩ ⟨origin + t / scale, ht'⟩ (e.forward s hs x) =
          post t ht.2 (hr.2.le.trans hct) (e.forward r hr x) := by
    let z := max s r
    have hz : z ∈ Ico 0 c := ⟨le_max_of_le_left hs.1, max_lt hs.2 hr.2⟩
    have hrz : r ≤ z := le_max_right _ _
    have hsz : s ≤ z := le_max_left _ _
    have hzt : z ≤ t := max_le (hs.2.le.trans hct) (hr.2.le.trans hct)
    have hz' : origin + z / scale ∈ Icc a b :=
      ⟨hs'.1.trans (hclock.monotone hsz), (hclock.monotone hzt).trans ht'.2⟩
    have he := e.slab_compatibility a b hab hK hfree s hs z hz hs' hz' x hx
    have hp := F.regularIdentifyIco_transport hJ hNo hab hK hfree
      ⟨origin + z / scale, hpostTime z (hz.2.trans hcd) hrz⟩
      ⟨origin + t / scale, hpostTime t ht.2 (hr.2.le.trans hct)⟩ hz' ht' (e.forward r hr x)
    change (F.regular_slabs a b hab hK hfree).transport
      ⟨origin + z / scale, hz'⟩ ⟨origin + t / scale, ht'⟩
        (post z (hz.2.trans hcd) hrz (e.forward r hr x)) = _ at hp
    rw [hoverlap z hz hrz x hx, ← he, SurgeryRegularSlab.transport_trans] at hp
    exact hp
  have hevent_before (s : ℝ) (hs : s ∈ Ico 0 d)
      (hT : origin + s / scale ∈ F.surgery_times) : s < c := by
    by_contra hsc
    exact Set.disjoint_left.mp hNo hT
      ⟨hclock (hr.2.trans_le (le_of_not_gt hsc)), hclock hs.2⟩
  let E : SurgeryFlowCylinder F C origin scale (Ico 0 d) U := {
    scale_pos := e.scale_pos
    interval_connected := ordConnected_Ico
    time_subset := by
      rintro _ ⟨s, hs, rfl⟩
      by_cases hsc : s < c
      · exact e.time_subset (mem_image_of_mem _ ⟨hs.1, hsc⟩)
      · exact hJ (hpostTime s hs.2 (hr.2.le.trans (le_of_not_gt hsc)))
    forward := fun s hs => chart s hs
    inverse := fun s hs => (chart s hs).symm
    forward_smooth := by
      intro s hs
      simpa only [hsource] using (chart s hs).contMDiffOn
    inverse_smooth := by
      intro s hs
      have himage : chart s hs '' U = (chart s hs).target := by
        rw [← hsource s hs]
        exact (chart s hs).toPartialEquiv.image_source_eq_target
      rw [himage]
      exact (chart s hs).contMDiffOn_invFun
    left_inverse := by
      intro s hs x hx
      exact (chart s hs).left_inv (hsource s hs ▸ hx)
    right_inverse := by
      intro s hs y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact (chart s hs).right_inv ((chart s hs).map_source (hsource s hs ▸ hx))
    slab_compatibility := by
      intro a b hab hK hfree s hs t ht hs' ht' x hx
      by_cases hsc : s < c
      · by_cases htc : t < c
        · rw [hbefore s hs hsc x, hbefore t ht htc x]
          exact e.slab_compatibility a b hab hK hfree
            s ⟨hs.1, hsc⟩ t ⟨ht.1, htc⟩ hs' ht' x hx
        · rw [hbefore s hs hsc x, hafter t ht (le_of_not_gt htc) x]
          exact hcross a b hab hK hfree s ⟨hs.1, hsc⟩ t ht (le_of_not_gt htc) hs' ht' x hx
      · by_cases htc : t < c
        · rw [hafter s hs (le_of_not_gt hsc) x, hbefore t ht htc x]
          have h := hcross a b hab hK hfree t ⟨ht.1, htc⟩ s hs
            (le_of_not_gt hsc) ht' hs' x hx
          have hi := congrArg ((F.regular_slabs a b hab hK hfree).transport
            ⟨origin + s / scale, hs'⟩ ⟨origin + t / scale, ht'⟩) h
          simpa only [SurgeryRegularSlab.transport_trans, SurgeryRegularSlab.transport_self]
            using hi.symm
        · rw [hafter s hs (le_of_not_gt hsc) x, hafter t ht (le_of_not_gt htc) x]
          exact F.regularIdentifyIco_transport hJ hNo hab hK hfree
            ⟨origin + s / scale, hpostTime s hs.2 (hr.2.le.trans (le_of_not_gt hsc))⟩
            ⟨origin + t / scale, hpostTime t ht.2 (hr.2.le.trans (le_of_not_gt htc))⟩
            hs' ht' (e.forward r hr x)
    retained_at_surgery := by
      intro s hs hT _ hearlier
      have hsc := hevent_before s hs hT
      rintro _ ⟨x, hx, rfl⟩
      rw [hbefore s hs hsc x]
      obtain ⟨t, ht, hts⟩ := hearlier
      exact e.retained_at_surgery s ⟨hs.1, hsc⟩ hT
        ⟨t, ⟨ht.1, hts.trans hsc⟩, hts⟩ (mem_image_of_mem _ hx)
    pre_retained_at_surgery := by
      intro s hs hT _ t ht ht' x hx
      have hsc := hevent_before s hs hT
      have htc : t < c := (hclock.lt_iff_lt.mp ht'.2).trans hsc
      rw [hbefore t ht htc x]
      exact e.pre_retained_at_surgery s ⟨hs.1, hsc⟩ hT t ⟨ht.1, htc⟩ ht' x hx
    surgery_compatibility := by
      intro s hs hT _ t ht ht' x hx
      have hsc := hevent_before s hs hT
      have htc : t < c := (hclock.lt_iff_lt.mp ht'.2).trans hsc
      rw [hbefore t ht htc x, hbefore s hs hsc x]
      exact e.surgery_compatibility s ⟨hs.1, hsc⟩ hT t ⟨ht.1, htc⟩ ht' x hx
  }
  exact ⟨E, fun s hs hs' x => hbefore s hs' hs.2 x⟩

end PoincareConjecture.M44
