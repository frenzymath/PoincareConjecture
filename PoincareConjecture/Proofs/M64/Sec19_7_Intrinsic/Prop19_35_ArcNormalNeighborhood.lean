import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopNormalNeighborhood













noncomputable section
set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture





theorem m64Intrinsic_exists_arc_normal_neighborhood
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {A B a b : ℝ}
    (hinj : InjOn gamma (Icc A B)) (hab : a ≤ b) (ha : A < a) (hb : b < B)
    (hregular : ∀ t ∈ Ioo A B, deriv gamma t ≠ 0)
    {K : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoid : ∀ t ∈ Icc a b, gamma t ∉ K) :
    ∃ delta > 0, ∃ H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates,
      Icc a b ×ˢ Ioo (-delta) delta ⊆ H.source ∧
      (∀ q, H q = normalStrip gamma q) ∧
      ContDiffOn ℝ ∞ H H.source ∧ ContDiffOn ℝ ∞ H.symm H.target ∧
      ∀ q ∈ H.source, H q ∈ gamma '' Icc A B ∪ K ↔ q.2 = 0 := by
  let l := (A + a) / 2
  let u := (b + B) / 2
  have hAl : A < l := by dsimp only [l]; linarith
  have hla : l < a := by dsimp only [l]; linarith
  have hbu : b < u := by dsimp only [u]; linarith
  have huB : u < B := by dsimp only [u]; linarith
  have hlu : l < u := hla.trans_le hab |>.trans hbu
  have hsub : Icc l u ⊆ Icc A B := Icc_subset_Icc hAl.le huB.le
  obtain ⟨epsilon, hepsilon, F, _, hstrip, hformula, hF, hFi, _⟩ :=
    exists_normal_collar_coordinates hg (hinj.mono hsub)
      (fun t ht => hregular t ⟨hAl.trans_le ht.1, ht.2.trans_lt huB⟩)
  let tail := gamma '' (Icc A l ∪ Icc u B) ∪ K
  have htail : IsClosed tail :=
    (((isCompact_Icc.union isCompact_Icc).image hg.continuous).union hK).isClosed
  have havoids (t : ℝ) (ht : t ∈ Icc a b) : gamma t ∉ tail := by
    rintro (⟨s, hs, heq⟩ | htK)
    · have htI : t ∈ Icc A B := ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩
      have hsI : s ∈ Icc A B := by
        rcases hs with hs | hs
        · exact ⟨hs.1, hs.2.trans (hlu.le.trans huB.le)⟩
        · exact ⟨(hAl.le.trans hlu.le).trans hs.1, hs.2⟩
      have hst := hinj hsI htI heq
      subst s
      rcases hs with hs | hs
      · linarith [ht.1, hs.2]
      · linarith [ht.2, hs.1]
    · exact havoid t ht htK
  let W := (Ioo l u ×ˢ (univ : Set ℝ)) ∩ (F.source ∩ F ⁻¹' tailᶜ)
  have hW : IsOpen W := (isOpen_Ioo.prod isOpen_univ).inter
    (F.isOpen_inter_preimage htail.isOpen_compl)
  let H := F.restrOpen W hW
  have hHformula (q : ℝ × ℝ) : H q = normalStrip gamma q := hformula q
  have haxis : Icc a b ×ˢ ({0} : Set ℝ) ⊆ H.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    have htlu : t ∈ Icc l u := ⟨hla.le.trans ht.1, ht.2.trans hbu.le⟩
    have hts : (t, (0 : ℝ)) ∈ F.source := hstrip ⟨htlu, ⟨by linarith, hepsilon⟩⟩
    refine ⟨hts, ⟨⟨hla.trans_le ht.1, ht.2.trans_lt hbu⟩, mem_univ _⟩, hts, ?_⟩
    change F (t, 0) ∉ tail
    simpa only [hformula, normalStrip_axis] using havoids t ht
  obtain ⟨X, Y, _, hY, hIX, h0Y, hXY⟩ := generalized_tube_lemma
    isCompact_Icc isCompact_singleton H.open_source haxis
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp
    (hY.mem_nhds (h0Y (mem_singleton (0 : ℝ))))
  refine ⟨delta, hdelta, H, ?_, hHformula, hF.mono inter_subset_left,
    hFi.mono inter_subset_left, ?_⟩
  · rintro ⟨t, z⟩ ⟨ht, hz⟩
    exact hXY ⟨hIX ht, hball (by
      simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr hz)⟩
  · intro q hq
    have hnotF : H q ∉ tail := hq.2.2.2
    constructor
    · rintro (⟨t, ht, heq⟩ | hqK)
      · have htlu : t ∈ Ioo l u := by
          have hnot : gamma t ∉ tail := heq ▸ hnotF
          constructor
          · by_contra hn
            exact hnot (Or.inl ⟨t, Or.inl ⟨ht.1, le_of_not_gt hn⟩, rfl⟩)
          · by_contra hn
            exact hnot (Or.inl ⟨t, Or.inr ⟨le_of_not_gt hn, ht.2⟩, rfl⟩)
        have hts : (t, (0 : ℝ)) ∈ F.source :=
          hstrip ⟨⟨htlu.1.le, htlu.2.le⟩, ⟨by linarith, hepsilon⟩⟩
        have heq' : q = (t, 0) := F.injOn hq.1 hts (by
          calc
            F q = H q := rfl
            _ = gamma t := heq.symm
            _ = F (t, 0) := by rw [hformula (t, 0), normalStrip_axis])
        exact congrArg Prod.snd heq'
      · exact False.elim (hnotF (Or.inr hqK))
    · intro hz
      refine Or.inl ⟨q.1, ⟨hAl.le.trans hq.2.1.1.1.le,
        hq.2.1.1.2.le.trans huB.le⟩, ?_⟩
      rw [hHformula]
      simp only [normalStrip, hz, zero_smul, add_zero]

end PoincareConjecture
