import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_TrackedBall










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46




theorem exists_cylinder_backward_along_ordinary_slab
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale c d : ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale (Icc c 0) U)
    (hU : IsOpen U) (hc : c ≤ 0) (hdc : d < c)
    (hJ : Icc (origin + d / scale) (origin + c / scale) ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc (origin + d / scale) (origin + c / scale))) :
    ∃ E : SurgeryFlowCylinder F C origin scale (Icc d 0) U,
      ∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc d 0) x,
        E.forward s hs' x = e.forward s hs x := by
  classical
  have hclock : StrictMono (fun s : ℝ => origin + s / scale) := by
    intro s t hst
    simpa only [add_comm] using
      add_lt_add_left ((div_lt_div_iff_of_pos_right e.scale_pos).mpr hst) origin
  let S := F.regular_slabs _ _ (hclock hdc) hJ hfree
  let endpoint : Icc (origin + d / scale) (origin + c / scale) :=
    ⟨origin + c / scale, ⟨(hclock hdc).le, le_rfl⟩⟩
  let bridge := (M44.cylinderSliceChart e hU c ⟨le_rfl, hc⟩).trans
    (S.identify endpoint).symm.toPartialDiffeomorph
  have hbridge : bridge.source = U := by
    change U ∩ (e.forward c ⟨le_rfl, hc⟩) ⁻¹' univ = U
    simp only [preimage_univ, inter_univ]
  have hbridge_end (x : C.carrier) :
      S.identify endpoint (bridge x) = e.forward c ⟨le_rfl, hc⟩ x :=
    (S.identify endpoint).apply_symm_apply _
  have hpreTime (s : ℝ) (hds : d ≤ s) (hsc : s ≤ c) :
      origin + s / scale ∈ Icc (origin + d / scale) (origin + c / scale) :=
    ⟨hclock.monotone hds, hclock.monotone hsc⟩
  let chart (s : ℝ) (hs : s ∈ Icc d 0) :
      PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier
        (F.slice (origin + s / scale)).carrier ∞ :=
    if hcs : c ≤ s then M44.cylinderSliceChart e hU s ⟨hcs, hs.2⟩
    else bridge.trans (S.identify
      ⟨origin + s / scale, hpreTime s hs.1 (lt_of_not_ge hcs).le⟩).toPartialDiffeomorph
  have hsource (s : ℝ) (hs : s ∈ Icc d 0) : (chart s hs).source = U := by
    dsimp only [chart]
    split_ifs
    · rfl
    · change bridge.source ∩ bridge ⁻¹' univ = U
      simp only [preimage_univ, inter_univ, hbridge]
  have hold (s : ℝ) (hs : s ∈ Icc d 0) (hcs : c ≤ s) (x : C.carrier) :
      chart s hs x = e.forward s ⟨hcs, hs.2⟩ x := by
    dsimp only [chart]
    rw [dif_pos hcs]
    rfl
  have hnew (s : ℝ) (hs : s ∈ Icc d 0) (hsc : s < c) (x : C.carrier) :
      chart s hs x = S.identify
        ⟨origin + s / scale, hpreTime s hs.1 hsc.le⟩ (bridge x) := by
    dsimp only [chart]
    rw [dif_neg (not_le_of_gt hsc)]
    rfl
  have hnew_transport (a b : ℝ) (hab : a < b)
      (hK : Icc a b ⊆ F.time_domain) (hNo : Disjoint F.surgery_times (Ioc a b))
      (s : ℝ) (hs : s ∈ Icc d c) (t : ℝ) (ht : t ∈ Icc d c)
      (hs' : origin + s / scale ∈ Icc a b) (ht' : origin + t / scale ∈ Icc a b)
      (x : C.carrier) :
      (F.regular_slabs a b hab hK hNo).transport
        ⟨origin + s / scale, hs'⟩ ⟨origin + t / scale, ht'⟩
        (S.identify ⟨origin + s / scale, hpreTime s hs.1 hs.2⟩ (bridge x)) =
          S.identify ⟨origin + t / scale, hpreTime t ht.1 ht.2⟩ (bridge x) := by
    rw [F.slab_transport_coherent a b _ _ hab hK hNo (hclock hdc) hJ hfree
      _ _ hs' ht' (hpreTime s hs.1 hs.2) (hpreTime t ht.1 ht.2)]
    exact congrArg (S.identify ⟨origin + t / scale, hpreTime t ht.1 ht.2⟩)
      ((S.identify ⟨origin + s / scale, hpreTime s hs.1 hs.2⟩).symm_apply_apply _)
  have hcross (a b : ℝ) (hab : a < b)
      (hK : Icc a b ⊆ F.time_domain) (hNo : Disjoint F.surgery_times (Ioc a b))
      (s : ℝ) (hs : s ∈ Icc d 0) (hsc : s < c)
      (t : ℝ) (ht : t ∈ Icc c 0)
      (hs' : origin + s / scale ∈ Icc a b) (ht' : origin + t / scale ∈ Icc a b)
      (x : C.carrier) (hx : x ∈ U) :
      (F.regular_slabs a b hab hK hNo).transport
        ⟨origin + s / scale, hs'⟩ ⟨origin + t / scale, ht'⟩ (chart s hs x) =
          e.forward t ht x := by
    have hc' : origin + c / scale ∈ Icc a b :=
      ⟨hs'.1.trans (hclock.monotone hsc.le), (hclock.monotone ht.1).trans ht'.2⟩
    have hp := hnew_transport a b hab hK hNo s ⟨hs.1, hsc.le⟩
      c ⟨hdc.le, le_rfl⟩ hs' hc' x
    rw [hbridge_end] at hp
    rw [← hnew s hs hsc x] at hp
    have he := e.slab_compatibility a b hab hK hNo
      c ⟨le_rfl, hc⟩ t ht hc' ht' x hx
    rw [← hp, SurgeryRegularSlab.transport_trans] at he
    exact he
  have hevent (s : ℝ) (hs : s ∈ Icc d 0)
      (hS : origin + s / scale ∈ F.surgery_times) : s = d ∨ c < s := by
    by_cases hcs : c < s
    · exact Or.inr hcs
    left
    apply le_antisymm _ hs.1
    by_contra hsd
    exact Set.disjoint_left.mp hfree hS
      ⟨hclock (lt_of_not_ge hsd), hclock.monotone (le_of_not_gt hcs)⟩
  have hpre_coordinate (s : ℝ) (hcs : c < s)
      (hS : origin + s / scale ∈ F.surgery_times)
      [Nonempty (F.slice (origin + s / scale)).carrier]
      (t : ℝ) (ht : t ∈ Icc d 0) (htc : t < c)
      (ht' : origin + t / scale ∈ Ico
        (F.event (origin + s / scale) hS).tMinus (origin + s / scale)) (x : C.carrier) :
      ((F.event (origin + s / scale) hS).pre_identify
        ⟨origin + t / scale, ht'⟩).symm (chart t ht x) =
      ((F.event (origin + s / scale) hS).pre_identify
        ⟨origin + c / scale, ⟨ht'.1.trans (hclock.monotone htc.le), hclock hcs⟩⟩).symm
        (e.forward c ⟨le_rfl, hc⟩ x) := by
    let event := F.event (origin + s / scale) hS
    have hce : origin + c / scale ∈ Ico event.tMinus (origin + s / scale) :=
      ⟨ht'.1.trans (hclock.monotone htc.le), hclock hcs⟩
    have h := F.event_slab_compatibility _ hS _ _ (hclock hdc) hJ hfree
      _ _ (hpreTime t ht.1 htc.le) endpoint.property ht' hce
      ((event.pre_identify ⟨origin + t / scale, ht'⟩).symm (chart t ht x))
    rw [Diffeomorph.apply_symm_apply, hnew t ht htc x] at h
    change S.identify endpoint
      ((S.identify ⟨origin + t / scale, hpreTime t ht.1 htc.le⟩).symm
        (S.identify ⟨origin + t / scale, hpreTime t ht.1 htc.le⟩ (bridge x))) = _ at h
    rw [Diffeomorph.symm_apply_apply, hbridge_end] at h
    rw [← hnew t ht htc x] at h
    change e.forward c ⟨le_rfl, hc⟩ x =
      event.pre_identify ⟨origin + c / scale, hce⟩
        ((event.pre_identify ⟨origin + t / scale, ht'⟩).symm (chart t ht x)) at h
    have hinv := congrArg (event.pre_identify ⟨origin + c / scale, hce⟩).symm h
    simpa only [Diffeomorph.symm_apply_apply] using hinv.symm
  let E : SurgeryFlowCylinder F C origin scale (Icc d 0) U := {
    scale_pos := e.scale_pos
    interval_connected := ordConnected_Icc
    time_subset := by
      rintro _ ⟨s, hs, rfl⟩
      by_cases hcs : c ≤ s
      · exact e.time_subset (mem_image_of_mem _ ⟨hcs, hs.2⟩)
      · exact hJ (hpreTime s hs.1 (lt_of_not_ge hcs).le)
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
      obtain ⟨x, hx, rfl⟩ := hy
      exact (chart s hs).right_inv ((chart s hs).map_source (hsource s hs ▸ hx))
    slab_compatibility := by
      intro a b hab hK hNo s hs t ht hs' ht' x hx
      by_cases hcs : c ≤ s
      · by_cases hct : c ≤ t
        · rw [hold s hs hcs x, hold t ht hct x]
          exact e.slab_compatibility a b hab hK hNo
            s ⟨hcs, hs.2⟩ t ⟨hct, ht.2⟩ hs' ht' x hx
        · rw [hold s hs hcs x]
          have h := hcross a b hab hK hNo t ht (lt_of_not_ge hct)
            s ⟨hcs, hs.2⟩ ht' hs' x hx
          have hi := congrArg ((F.regular_slabs a b hab hK hNo).transport
            ⟨origin + s / scale, hs'⟩ ⟨origin + t / scale, ht'⟩) h
          simpa only [SurgeryRegularSlab.transport_trans, SurgeryRegularSlab.transport_self]
            using hi.symm
      · by_cases hct : c ≤ t
        · rw [hold t ht hct x]
          exact hcross a b hab hK hNo s hs (lt_of_not_ge hcs)
            t ⟨hct, ht.2⟩ hs' ht' x hx
        · rw [hnew s hs (lt_of_not_ge hcs) x, hnew t ht (lt_of_not_ge hct) x]
          exact hnew_transport a b hab hK hNo s ⟨hs.1, (lt_of_not_ge hcs).le⟩
            t ⟨ht.1, (lt_of_not_ge hct).le⟩ hs' ht' x
    retained_at_surgery := by
      intro s hs hS _ hearlier
      rcases hevent s hs hS with hsd | hcs
      · obtain ⟨t, ht, hts⟩ := hearlier
        exact (not_lt_of_ge ht.1 (hsd ▸ hts)).elim
      · rintro _ ⟨x, hx, rfl⟩
        rw [hold s hs hcs.le x]
        exact e.retained_at_surgery s ⟨hcs.le, hs.2⟩ hS
          ⟨c, ⟨le_rfl, hc⟩, hcs⟩ (mem_image_of_mem _ hx)
    pre_retained_at_surgery := by
      intro s hs hS _ t ht ht' x hx
      have hts := hclock.lt_iff_lt.mp ht'.2
      rcases hevent s hs hS with hsd | hcs
      · exact (not_lt_of_ge ht.1 (hsd ▸ hts)).elim
      · by_cases hct : c ≤ t
        · rw [hold t ht hct x]
          exact e.pre_retained_at_surgery s ⟨hcs.le, hs.2⟩ hS
            t ⟨hct, ht.2⟩ ht' x hx
        · rw [hpre_coordinate s hcs hS t ht (lt_of_not_ge hct) ht' x]
          exact e.pre_retained_at_surgery s ⟨hcs.le, hs.2⟩ hS
            c ⟨le_rfl, hc⟩ _ x hx
    surgery_compatibility := by
      intro s hs hS _ t ht ht' x hx
      have hts := hclock.lt_iff_lt.mp ht'.2
      rcases hevent s hs hS with hsd | hcs
      · exact (not_lt_of_ge ht.1 (hsd ▸ hts)).elim
      · rw [hold s hs hcs.le x]
        by_cases hct : c ≤ t
        · rw [hold t ht hct x]
          exact e.surgery_compatibility s ⟨hcs.le, hs.2⟩ hS
            t ⟨hct, ht.2⟩ ht' x hx
        · rw [hpre_coordinate s hcs hS t ht (lt_of_not_ge hct) ht' x]
          exact e.surgery_compatibility s ⟨hcs.le, hs.2⟩ hS
            c ⟨le_rfl, hc⟩ _ x hx
  }
  exact ⟨E, fun s hs hs' x => hold s hs' hs.1 x⟩

end PoincareConjecture.Proofs.M46
