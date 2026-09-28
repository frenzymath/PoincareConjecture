import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_TrackedBall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_cylinder_forward_along_ordinary_slab
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale a b : ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale (Icc a 0) U)
    (hU : IsOpen U) (ha : a ≤ 0) (hb : 0 < b)
    (hJ : Icc origin (origin + b / scale) ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc origin (origin + b / scale))) :
    ∃ E : SurgeryFlowCylinder F C origin scale (Icc a b) U,
      ∀ s (hs : s ∈ Icc a 0) (hs' : s ∈ Icc a b) x,
        E.forward s hs' x = e.forward s hs x := by
  classical
  have hclock : StrictMono (fun s : ℝ => origin + s / scale) := by
    intro s t hst
    simpa only [add_comm] using
      add_lt_add_left ((div_lt_div_iff_of_pos_right e.scale_pos).mpr hst) origin
  have hJ' : Icc (origin + 0 / scale) (origin + b / scale) ⊆ F.time_domain := by
    simpa only [zero_div, add_zero] using hJ
  have hfree' : Disjoint F.surgery_times
      (Ioc (origin + 0 / scale) (origin + b / scale)) := by
    simpa only [zero_div, add_zero] using hfree
  let S := F.regular_slabs _ _ (hclock hb) hJ' hfree'
  let initial : Icc (origin + 0 / scale) (origin + b / scale) :=
    ⟨origin + 0 / scale, ⟨le_rfl, (hclock hb).le⟩⟩
  let bridge := (M44.cylinderSliceChart e hU 0 ⟨ha, le_rfl⟩).trans
    (S.identify initial).symm.toPartialDiffeomorph
  have hbridge : bridge.source = U := by
    change U ∩ (e.forward 0 ⟨ha, le_rfl⟩) ⁻¹' univ = U
    simp only [preimage_univ, inter_univ]
  have hbridge_zero (x : C.carrier) :
      S.identify initial (bridge x) = e.forward 0 ⟨ha, le_rfl⟩ x :=
    (S.identify initial).apply_symm_apply _
  have hpostTime (s : ℝ) (h0s : 0 ≤ s) (hsb : s ≤ b) :
      origin + s / scale ∈ Icc (origin + 0 / scale) (origin + b / scale) :=
    ⟨hclock.monotone h0s, hclock.monotone hsb⟩
  let chart (s : ℝ) (hs : s ∈ Icc a b) :
      PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier
        (F.slice (origin + s / scale)).carrier ∞ :=
    if hs0 : s ≤ 0 then M44.cylinderSliceChart e hU s ⟨hs.1, hs0⟩
    else bridge.trans (S.identify
      ⟨origin + s / scale, hpostTime s (lt_of_not_ge hs0).le hs.2⟩).toPartialDiffeomorph
  have hsource (s : ℝ) (hs : s ∈ Icc a b) : (chart s hs).source = U := by
    dsimp only [chart]
    split_ifs
    · rfl
    · change bridge.source ∩ bridge ⁻¹' univ = U
      simp only [preimage_univ, inter_univ, hbridge]
  have hold (s : ℝ) (hs : s ∈ Icc a b) (hs0 : s ≤ 0) (x : C.carrier) :
      chart s hs x = e.forward s ⟨hs.1, hs0⟩ x := by
    dsimp only [chart]
    rw [dif_pos hs0]
    rfl
  have hnew (s : ℝ) (hs : s ∈ Icc a b) (h0s : 0 < s) (x : C.carrier) :
      chart s hs x = S.identify
        ⟨origin + s / scale, hpostTime s h0s.le hs.2⟩ (bridge x) := by
    dsimp only [chart]
    rw [dif_neg (not_le_of_gt h0s)]
    rfl
  have hnew_transport (l h : ℝ) (hlh : l < h)
      (hK : Icc l h ⊆ F.time_domain) (hNo : Disjoint F.surgery_times (Ioc l h))
      (s : ℝ) (hs : s ∈ Icc 0 b) (t : ℝ) (ht : t ∈ Icc 0 b)
      (hs' : origin + s / scale ∈ Icc l h) (ht' : origin + t / scale ∈ Icc l h)
      (x : C.carrier) :
      (F.regular_slabs l h hlh hK hNo).transport
        ⟨origin + s / scale, hs'⟩ ⟨origin + t / scale, ht'⟩
        (S.identify ⟨origin + s / scale, hpostTime s hs.1 hs.2⟩ (bridge x)) =
          S.identify ⟨origin + t / scale, hpostTime t ht.1 ht.2⟩ (bridge x) := by
    rw [F.slab_transport_coherent l h _ _ hlh hK hNo (hclock hb) hJ' hfree'
      _ _ hs' ht' (hpostTime s hs.1 hs.2) (hpostTime t ht.1 ht.2)]
    exact congrArg (S.identify ⟨origin + t / scale, hpostTime t ht.1 ht.2⟩)
      ((S.identify ⟨origin + s / scale, hpostTime s hs.1 hs.2⟩).symm_apply_apply _)
  have hcross (l h : ℝ) (hlh : l < h)
      (hK : Icc l h ⊆ F.time_domain) (hNo : Disjoint F.surgery_times (Ioc l h))
      (s : ℝ) (hs : s ∈ Icc a 0) (t : ℝ) (ht : t ∈ Icc a b) (h0t : 0 < t)
      (hs' : origin + s / scale ∈ Icc l h) (ht' : origin + t / scale ∈ Icc l h)
      (x : C.carrier) (hx : x ∈ U) :
      (F.regular_slabs l h hlh hK hNo).transport
        ⟨origin + s / scale, hs'⟩ ⟨origin + t / scale, ht'⟩ (e.forward s hs x) =
          chart t ht x := by
    have hz : origin + 0 / scale ∈ Icc l h :=
      ⟨hs'.1.trans (hclock.monotone hs.2), (hclock.monotone h0t.le).trans ht'.2⟩
    have he := e.slab_compatibility l h hlh hK hNo
      s hs 0 ⟨ha, le_rfl⟩ hs' hz x hx
    have hn := hnew_transport l h hlh hK hNo 0 ⟨le_rfl, hb.le⟩
      t ⟨h0t.le, ht.2⟩ hz ht' x
    rw [hbridge_zero, ← hnew t ht h0t x, ← he,
      SurgeryRegularSlab.transport_trans] at hn
    exact hn
  have hevent (s : ℝ) (hs : s ∈ Icc a b)
      (hT : origin + s / scale ∈ F.surgery_times) : s ≤ 0 := by
    by_contra hs0
    exact Set.disjoint_left.mp hfree' hT
      ⟨hclock (lt_of_not_ge hs0), hclock.monotone hs.2⟩
  let E : SurgeryFlowCylinder F C origin scale (Icc a b) U := {
    scale_pos := e.scale_pos
    interval_connected := ordConnected_Icc
    time_subset := by
      rintro _ ⟨s, hs, rfl⟩
      by_cases hs0 : s ≤ 0
      · exact e.time_subset (mem_image_of_mem _ ⟨hs.1, hs0⟩)
      · exact hJ' (hpostTime s (lt_of_not_ge hs0).le hs.2)
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
    left_inverse := fun s hs x hx => (chart s hs).left_inv (hsource s hs ▸ hx)
    right_inverse := by
      rintro s hs _ ⟨x, hx, rfl⟩
      exact (chart s hs).right_inv ((chart s hs).map_source (hsource s hs ▸ hx))
    slab_compatibility := by
      intro l h hlh hK hNo s hs t ht hs' ht' x hx
      by_cases hs0 : s ≤ 0
      · by_cases ht0 : t ≤ 0
        · rw [hold s hs hs0 x, hold t ht ht0 x]
          exact e.slab_compatibility l h hlh hK hNo
            s ⟨hs.1, hs0⟩ t ⟨ht.1, ht0⟩ hs' ht' x hx
        · rw [hold s hs hs0 x]
          exact hcross l h hlh hK hNo s ⟨hs.1, hs0⟩ t ht (lt_of_not_ge ht0) hs' ht' x hx
      · by_cases ht0 : t ≤ 0
        · rw [hold t ht ht0 x]
          have hcrossEq := hcross l h hlh hK hNo t ⟨ht.1, ht0⟩ s hs
            (lt_of_not_ge hs0) ht' hs' x hx
          have hi := congrArg ((F.regular_slabs l h hlh hK hNo).transport
            ⟨origin + s / scale, hs'⟩ ⟨origin + t / scale, ht'⟩) hcrossEq
          simpa only [SurgeryRegularSlab.transport_trans,
            SurgeryRegularSlab.transport_self] using hi.symm
        · rw [hnew s hs (lt_of_not_ge hs0) x, hnew t ht (lt_of_not_ge ht0) x]
          exact hnew_transport l h hlh hK hNo
            s ⟨(lt_of_not_ge hs0).le, hs.2⟩ t ⟨(lt_of_not_ge ht0).le, ht.2⟩ hs' ht' x
    retained_at_surgery := by
      intro s hs hT _ hearlier
      have hs0 := hevent s hs hT
      rintro _ ⟨x, hx, rfl⟩
      rw [hold s hs hs0 x]
      obtain ⟨t, ht, hts⟩ := hearlier
      exact e.retained_at_surgery s ⟨hs.1, hs0⟩ hT
        ⟨t, ⟨ht.1, (hts.trans_le hs0).le⟩, hts⟩ (mem_image_of_mem _ hx)
    pre_retained_at_surgery := by
      intro s hs hT _ t ht ht' x hx
      have hs0 := hevent s hs hT
      have ht0 : t ≤ 0 := (hclock.lt_iff_lt.mp ht'.2).le.trans hs0
      rw [hold t ht ht0 x]
      exact e.pre_retained_at_surgery s ⟨hs.1, hs0⟩ hT t ⟨ht.1, ht0⟩ ht' x hx
    surgery_compatibility := by
      intro s hs hT _ t ht ht' x hx
      have hs0 := hevent s hs hT
      have ht0 : t ≤ 0 := (hclock.lt_iff_lt.mp ht'.2).le.trans hs0
      rw [hold t ht ht0 x, hold s hs hs0 x]
      exact e.surgery_compatibility s ⟨hs.1, hs0⟩ hT t ⟨ht.1, ht0⟩ ht' x hx
  }
  exact ⟨E, fun s hs hs' x => hold s hs' hs.2 x⟩

end PoincareConjecture.Proofs.M47
