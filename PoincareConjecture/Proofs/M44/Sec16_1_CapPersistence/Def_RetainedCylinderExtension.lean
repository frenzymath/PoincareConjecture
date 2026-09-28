import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_PreterminalTransport










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale c d : ℝ} {U : Set C.carrier}





theorem exists_cylinder_across_retained_event
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U)
    (hU : IsOpen U) (hc : 0 < c) (hcd : c < d)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (hpre : Disjoint F.surgery_times
      (Ioo (F.event (origin + c / scale) hT).tMinus (origin + c / scale)))
    (hJ : Ico (origin + c / scale) (origin + d / scale) ⊆ F.time_domain)
    (hNo : Disjoint F.surgery_times (Ioo (origin + c / scale) (origin + d / scale)))
    (r : ℝ) (hr : r ∈ Ico 0 c)
    (hr' : origin + r / scale ∈
      Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale))
    (hret : ∀ x ∈ U, ((F.event (origin + c / scale) hT).pre_identify
      ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x) ∈
        interior (F.event (origin + c / scale) hT).retained_pre) :
    ∃ e' : SurgeryFlowCylinder F C origin scale (Ico 0 d) U,
      (∀ s (hs : s ∈ Ico 0 c) (hs' : s ∈ Ico 0 d) x,
        e'.forward s hs' x = e.forward s hs x) ∧
      ∀ x, e'.forward c ⟨hc.le, hcd⟩ x =
        (F.event (origin + c / scale) hT).retention.map
          (((F.event (origin + c / scale) hT).pre_identify
            ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x)) := by
  classical
  let bridge := cylinderRetainedChart e hU hT r hr hr'
  have hbridge : bridge.source = U := cylinderRetainedChart_source e hU hT r hr hr' hret
  have hclock : StrictMono (fun s : ℝ => origin + s / scale) := by
    intro s t hst
    dsimp only
    linarith [(div_lt_div_iff_of_pos_right e.scale_pos).mpr hst]
  have hpostTime (s : ℝ) (hs : s < d) (hcs : c ≤ s) :
      origin + s / scale ∈ Ico (origin + c / scale) (origin + d / scale) :=
    ⟨hclock.monotone hcs, hclock hs⟩
  let post (s : ℝ) (hs : s < d) (hcs : c ≤ s) :=
    F.regularIdentifyIco hJ hNo ⟨origin + s / scale, hpostTime s hs hcs⟩
  let chart (s : ℝ) (hs : s ∈ Ico 0 d) :
      PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier
        (F.slice (origin + s / scale)).carrier ∞ :=
    if hsc : s < c then cylinderSliceChart e hU s ⟨hs.1, hsc⟩
    else bridge.trans (post s hs.2 (le_of_not_gt hsc)).toPartialDiffeomorph
  have hsource (s : ℝ) (hs : s ∈ Ico 0 d) : (chart s hs).source = U := by
    dsimp only [chart]
    split_ifs
    · rfl
    · change bridge.source ∩ bridge ⁻¹' (univ : Set (F.slice (origin + c / scale)).carrier) = U
      simp only [preimage_univ, inter_univ, hbridge]
  have hbefore (s : ℝ) (hs : s ∈ Ico 0 d) (hsc : s < c) (x : C.carrier) :
      chart s hs x = e.forward s ⟨hs.1, hsc⟩ x := by
    dsimp only [chart]
    rw [dif_pos hsc]
    rfl
  have hafter (s : ℝ) (hs : s ∈ Ico 0 d) (hcs : c ≤ s) (x : C.carrier) :
      chart s hs x = post s hs.2 hcs (bridge x) := by
    dsimp only [chart]
    rw [dif_neg (not_lt_of_ge hcs)]
    rfl
  have hpost_initial (hs : c < d) (y : (F.slice (origin + c / scale)).carrier) :
      post c hs le_rfl y = y := by
    dsimp only [post, SurgeryFlowData.regularIdentifyIco]
    exact SurgeryRegularSlab.initial_identify _ y
  have hlater_event (s : ℝ) (hs : s ∈ Ico 0 d) (hcs : c ≤ s)
      (hsurgery : origin + s / scale ∈ F.surgery_times) : s = c := by
    apply le_antisymm _ hcs
    by_contra hsc
    exact Set.disjoint_left.mp hNo hsurgery ⟨hclock (lt_of_not_ge hsc), hclock hs.2⟩
  let e' : SurgeryFlowCylinder F C origin scale (Ico 0 d) U := {
    scale_pos := e.scale_pos
    interval_connected := ordConnected_Ico
    time_subset := by
      rintro _ ⟨s, hs, rfl⟩
      by_cases hsc : s < c
      · exact e.time_subset (mem_image_of_mem _ ⟨hs.1, hsc⟩)
      · exact hJ (hpostTime s hs.2 (le_of_not_gt hsc))
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
        · exact (Set.disjoint_left.mp hfree hT
            ⟨hs'.1.trans_lt (hclock hsc),
              (hclock.monotone (le_of_not_gt htc)).trans ht'.2⟩).elim
      · by_cases htc : t < c
        · exact (Set.disjoint_left.mp hfree hT
            ⟨ht'.1.trans_lt (hclock htc),
              (hclock.monotone (le_of_not_gt hsc)).trans hs'.2⟩).elim
        · rw [hafter s hs (le_of_not_gt hsc) x, hafter t ht (le_of_not_gt htc) x]
          exact F.regularIdentifyIco_transport hJ hNo hab hK hfree
            ⟨origin + s / scale, hpostTime s hs.2 (le_of_not_gt hsc)⟩
            ⟨origin + t / scale, hpostTime t ht.2 (le_of_not_gt htc)⟩ hs' ht' (bridge x)
    retained_at_surgery := by
      intro s hs hsurgery _ hearlier
      rintro _ ⟨x, hx, rfl⟩
      by_cases hsc : s < c
      · rw [hbefore s hs hsc x]
        obtain ⟨t, ht, hts⟩ := hearlier
        exact e.retained_at_surgery s ⟨hs.1, hsc⟩ hsurgery
          ⟨t, ⟨ht.1, hts.trans hsc⟩, hts⟩ (mem_image_of_mem _ hx)
      · have hseq := hlater_event s hs (le_of_not_gt hsc) hsurgery
        subst s
        rw [hafter c hs le_rfl x, hpost_initial hs.2]
        exact cylinderRetainedChart_mem_retained e hU hT r hr hr' hret hx
    pre_retained_at_surgery := by
      intro s hs hsurgery _ t ht ht' x hx
      have hts : t < s := hclock.lt_iff_lt.mp ht'.2
      by_cases hsc : s < c
      · rw [hbefore t ht (hts.trans hsc) x]
        exact e.pre_retained_at_surgery s ⟨hs.1, hsc⟩ hsurgery
          t ⟨ht.1, hts.trans hsc⟩ ht' x hx
      · have hseq := hlater_event s hs (le_of_not_gt hsc) hsurgery
        subst s
        rw [hbefore t ht hts x]
        rw [cylinder_preterminal_coordinates_eq e hT hpre
          t ⟨ht.1, hts⟩ r hr ht' hr' x hx]
        exact hret x hx
    surgery_compatibility := by
      intro s hs hsurgery _ t ht ht' x hx
      have hts : t < s := hclock.lt_iff_lt.mp ht'.2
      by_cases hsc : s < c
      · rw [hbefore t ht (hts.trans hsc) x, hbefore s hs hsc x]
        exact e.surgery_compatibility s ⟨hs.1, hsc⟩ hsurgery
          t ⟨ht.1, hts.trans hsc⟩ ht' x hx
      · have hseq := hlater_event s hs (le_of_not_gt hsc) hsurgery
        subst s
        rw [hbefore t ht hts x, hafter c hs le_rfl x, hpost_initial hs.2]
        rw [cylinder_preterminal_coordinates_eq e hT hpre
          t ⟨ht.1, hts⟩ r hr ht' hr' x hx]
        rfl
  }
  refine ⟨e', ?_, ?_⟩
  · intro s hs hs' x
    exact hbefore s hs' hs.2 x
  · intro x
    change chart c ⟨hc.le, hcd⟩ x = _
    rw [hafter c ⟨hc.le, hcd⟩ le_rfl x, hpost_initial hcd]
    rfl

end PoincareConjecture.M44
