import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcBandChain
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JordanLineGerm

noncomputable section
set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

private theorem regular_arc_buffer
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {T a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hb : b < T)
    (hregular : ∀ t ∈ Icc a b, deriv gamma t ≠ 0) :
    ∃ l u : ℝ, 0 < l ∧ l < a ∧ b < u ∧ u < T ∧
      ∀ t ∈ Icc l u, deriv gamma t ≠ 0 := by
  let X := Ioo (0 : ℝ) T ∩ {t | deriv gamma t ≠ 0}
  have hX : IsOpen X := isOpen_Ioo.inter
    (isOpen_ne.preimage (contDiff_infty_iff_deriv.mp hg).2.continuous)
  have hI : Icc a b ⊆ X :=
    fun t ht => ⟨⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩, hregular t ht⟩
  obtain ⟨l, r, hlr, hleft⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hX.mem_nhds (hI (left_mem_Icc.mpr hab)))
  obtain ⟨s, u, hsu, hright⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hX.mem_nhds (hI (right_mem_Icc.mpr hab)))
  let l' := (l + a) / 2
  let u' := (b + u) / 2
  have hl'a : l' < a := by dsimp [l']; linarith [hlr.1]
  have hbu' : b < u' := by dsimp [u']; linarith [hsu.2]
  have hl' : l' ∈ X := hleft ⟨by dsimp [l']; linarith [hlr.1], hl'a.trans hlr.2⟩
  have hu' : u' ∈ X := hright ⟨hsu.1.trans hbu', by dsimp [u']; linarith [hsu.2]⟩
  refine ⟨l', u', hl'.1.1, hl'a, hbu', hu'.1.2, ?_⟩
  intro t ht
  by_cases hta : t < a
  · exact (hleft ⟨by dsimp [l'] at ht; linarith [ht.1, hlr.1], hta.trans hlr.2⟩).2
  by_cases hbt : b < t
  · exact (hright ⟨hsu.1.trans hbt, by dsimp [u'] at ht; linarith [ht.2, hsu.2]⟩).2
  exact hregular t ⟨le_of_not_gt hta, le_of_not_gt hbt⟩

theorem m64Intrinsic_exists_loop_normal_neighborhood
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T a b : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hab : a ≤ b) (ha : 0 < a) (hb : b < T)
    (hregular : ∀ t ∈ Icc a b, deriv gamma t ≠ 0) :
    ∃ delta > 0, ∃ H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates,
      Icc a b ×ˢ Ioo (-delta) delta ⊆ H.source ∧
      (∀ q, H q = normalStrip gamma q) ∧
      ContDiffOn ℝ ∞ H H.source ∧ ContDiffOn ℝ ∞ H.symm H.target ∧
      ∀ q ∈ H.source, H q ∈ gamma '' Icc 0 T ↔ q.2 = 0 := by
  obtain ⟨l, u, hl0, hla, hbu, huT, hreg⟩ := regular_arc_buffer hg hab ha hb hregular
  have hlu : l < u := hla.trans_le hab |>.trans hbu
  have hsub : Icc l u ⊆ Ico (0 : ℝ) T :=
    fun t ht => ⟨hl0.le.trans ht.1, ht.2.trans_lt huT⟩
  obtain ⟨epsilon, hepsilon, F, _, hstrip, hformula, hF, hFi, _⟩ :=
    exists_normal_collar_coordinates hg (hinj.mono hsub) hreg
  let tail := gamma '' (Icc (0 : ℝ) l ∪ Icc u T)
  have htail : IsClosed tail :=
    ((isCompact_Icc.union isCompact_Icc).image hg.continuous).isClosed
  have havoid (t : ℝ) (ht : t ∈ Icc a b) : gamma t ∉ tail := by
    rintro ⟨s, hs, heq⟩
    have htI : t ∈ Ico (0 : ℝ) T := ⟨ha.le.trans ht.1, ht.2.trans_lt hb⟩
    have hsI : s ∈ Icc (0 : ℝ) T := by
      rcases hs with hs | hs
      · exact ⟨hs.1, hs.2.trans (hlu.le.trans huT.le)⟩
      · exact ⟨(hl0.le.trans hlu.le).trans hs.1, hs.2⟩
    have hsT : s < T := by
      by_contra hn
      have heT : s = T := le_antisymm hsI.2 (le_of_not_gt hn)
      have h0t := hinj ⟨le_rfl, ha.trans_le hab |>.trans hb⟩ htI
        (hend.trans (heT ▸ heq))
      linarith [ha.trans_le ht.1]
    have hst := hinj ⟨hsI.1, hsT⟩ htI heq
    subst s
    rcases hs with hs | hs
    · linarith [ht.1, hs.2]
    · linarith [ht.2, hs.1]
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
    simpa only [hformula, normalStrip_axis] using havoid t ht
  obtain ⟨A, B, _, hB, hIA, h0B, hAB⟩ := generalized_tube_lemma
    isCompact_Icc isCompact_singleton H.open_source haxis
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp
    (hB.mem_nhds (h0B (mem_singleton (0 : ℝ))))
  refine ⟨delta, hdelta, H, ?_, hHformula, hF.mono inter_subset_left,
    hFi.mono inter_subset_left, ?_⟩
  · rintro ⟨t, z⟩ ⟨ht, hz⟩
    exact hAB ⟨hIA ht, hball (by
      simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr hz)⟩
  · intro q hq
    constructor
    · rintro ⟨t, ht, heq⟩
      have htlu : t ∈ Ioo l u := by
        have hnotF : H q ∉ tail := hq.2.2.2
        have hnot : gamma t ∉ tail := heq ▸ hnotF
        constructor
        · by_contra hn
          exact hnot ⟨t, Or.inl ⟨ht.1, le_of_not_gt hn⟩, rfl⟩
        · by_contra hn
          exact hnot ⟨t, Or.inr ⟨le_of_not_gt hn, ht.2⟩, rfl⟩
      have hts : (t, (0 : ℝ)) ∈ F.source :=
        hstrip ⟨⟨htlu.1.le, htlu.2.le⟩, ⟨by linarith, hepsilon⟩⟩
      have he : q = (t, 0) := F.injOn hq.1 hts (by
        calc
          F q = H q := rfl
          _ = gamma t := heq.symm
          _ = F (t, 0) := by rw [hformula (t, 0), normalStrip_axis])
      exact congrArg Prod.snd he
    · intro hz
      refine ⟨q.1, ⟨hl0.le.trans hq.2.1.1.1.le, hq.2.1.1.2.le.trans huT.le⟩, ?_⟩
      rw [hHformula]
      simp only [normalStrip, hz, zero_smul, add_zero]

end PoincareConjecture
