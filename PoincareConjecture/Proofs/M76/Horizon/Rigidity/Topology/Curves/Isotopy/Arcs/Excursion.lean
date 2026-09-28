import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.Contacts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

theorem exists_positive_finitePL_excursion {f : ℝ → ℝ}
    (hf : FinitePiecewiseAffineOn f (Icc 0 1))
    {u t v c : ℝ} (hu : 0 ≤ u) (hut : u < t) (htv : t < v) (hv : v ≤ 1)
    (hfu : f u = c) (hfv : f v = c) (hft : c < f t) :
    ∃ a b : ℝ, u ≤ a ∧ a < t ∧ t < b ∧ b ≤ v ∧
      f a = c ∧ f b = c ∧ ∀ x ∈ Ioo a b, c < f x := by
  classical
  let Z : Set ℝ := Icc 0 1 ∩ {x | f x = c}
  obtain ⟨J, _, hJ⟩ := exists_finite_interval_level_contacts hf c
  have hZcompact : IsCompact Z := by
    rw [show Z = ⋃ p ∈ J, Icc p.1 p.2 from hJ]
    exact J.isCompact_biUnion fun _ _ => isCompact_Icc
  obtain ⟨a, ha, hamax⟩ := (hZcompact.inter_right isClosed_Icc).exists_isGreatest
    (show (Z ∩ Icc u t).Nonempty from ⟨u, ⟨⟨hu, by linarith⟩, hfu⟩, le_rfl, hut.le⟩)
  obtain ⟨b, hb, hbmin⟩ := (hZcompact.inter_right isClosed_Icc).exists_isLeast
    (show (Z ∩ Icc t v).Nonempty from ⟨v, ⟨⟨by linarith, hv⟩, hfv⟩, htv.le, le_rfl⟩)
  have hat : a < t := lt_of_le_of_ne ha.2.2 (by
    intro h
    have hz : f t = c := h ▸ ha.1.2
    linarith)
  have htb : t < b := lt_of_le_of_ne hb.2.1 (by
    intro h
    have hz : f t = c := h.symm ▸ hb.1.2
    linarith)
  refine ⟨a, b, ha.2.1, hat, htb, hb.2.2, ha.1.2, hb.1.2, ?_⟩
  intro x hx
  by_contra h
  have hxc : f x ≤ c := le_of_not_gt h
  have hxI : x ∈ Icc 0 1 := ⟨ha.1.1.1.trans hx.1.le, hx.2.le.trans hb.1.1.2⟩
  rcases le_total x t with hxt | htx
  · have hcont : ContinuousOn f (Icc x t) := hf.continuousOn.mono
      (fun y hy => ⟨hxI.1.trans hy.1, hy.2.trans (by linarith)⟩)
    obtain ⟨z, hz, hzc⟩ := intermediate_value_Icc hxt hcont ⟨hxc, hft.le⟩
    have hzZ : z ∈ Z := ⟨⟨hxI.1.trans hz.1, hz.2.trans (by linarith)⟩, hzc⟩
    have hza : z ≤ a := hamax ⟨hzZ, ⟨by linarith [ha.2.1, hx.1, hz.1], hz.2⟩⟩
    linarith [hz.1, hx.1]
  · have hcont : ContinuousOn f (Icc t x) := hf.continuousOn.mono
      (fun y hy => ⟨(by linarith : (0 : ℝ) ≤ t).trans hy.1, hy.2.trans hxI.2⟩)
    obtain ⟨z, hz, hzc⟩ := intermediate_value_Icc' htx hcont ⟨hxc, hft.le⟩
    have hzZ : z ∈ Z := ⟨⟨(by linarith : (0 : ℝ) ≤ t).trans hz.1, hz.2.trans hxI.2⟩, hzc⟩
    have hbz : b ≤ z := hbmin ⟨hzZ, ⟨hz.1, by linarith [hb.2.2, hx.2, hz.2]⟩⟩
    linarith [hz.2, hx.2]

theorem exists_finitePL_annular_returning_subarc {r : ℝ → ℝ × ℝ}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) (hi : InjOn r (Icc 0 1))
    {u t v c : ℝ} (hu : 0 ≤ u) (hut : u < t) (htv : t < v) (hv : v ≤ 1)
    (hru : (r u).1 = c) (hrv : (r v).1 = c) (hrt : c < (r t).1) :
    ∃ a b : ℝ, u ≤ a ∧ a < t ∧ t < b ∧ b ≤ v ∧
      (r a).1 = c ∧ (r b).1 = c ∧
      IsFinitePLBallPair ℝ (r '' Icc a b) {r a, r b} ∧
      (r '' Icc a b) ∩ {x | x.1 = c} = {r a, r b} ∧
      ∀ x ∈ (r '' Icc a b) \ {r a, r b}, c < x.1 := by
  obtain ⟨a, b, hua, hat, htb, hbv, hca, hcb, hpos⟩ :=
    exists_positive_finitePL_excursion
      (hr.postcomp (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap)
      hu hut htv hv hru hrv hrt
  have hab : a < b := hat.trans htb
  have hsub : Icc a b ⊆ Icc 0 1 := fun x hx =>
    ⟨(hu.trans hua).trans hx.1, hx.2.trans (hbv.trans hv)⟩
  have hball : IsFinitePLBallPair ℝ (r '' Icc a b) {r a, r b} := by
    simpa only [image_pair] using (isFinitePLBallPair_Icc hab).image_of_subset hr hsub hi
  refine ⟨a, b, hua, hat, htb, hbv, hca, hcb, hball, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro x ⟨⟨s, hs, rfl⟩, hsc⟩
      by_cases hsa : s = a
      · simp [hsa]
      by_cases hsb : s = b
      · simp [hsb]
      have hp := hpos s ⟨lt_of_le_of_ne hs.1 (Ne.symm hsa), lt_of_le_of_ne hs.2 hsb⟩
      exact (not_lt_of_ge (le_of_eq hsc) hp).elim
    · rintro x (rfl | rfl)
      · exact ⟨mem_image_of_mem r ⟨le_rfl, hab.le⟩, hca⟩
      · exact ⟨mem_image_of_mem r ⟨hab.le, le_rfl⟩, hcb⟩
  · rintro x ⟨⟨s, hs, rfl⟩, hnot⟩
    apply hpos s
    constructor
    · apply lt_of_le_of_ne hs.1
      intro h
      apply hnot
      simp [h]
    · apply lt_of_le_of_ne hs.2
      intro h
      apply hnot
      simp [h]

end PoincareConjecture.M76.Dehn
