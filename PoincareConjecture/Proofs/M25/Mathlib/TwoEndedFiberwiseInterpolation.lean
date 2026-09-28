import PoincareConjecture.Proofs.M25.Mathlib.RelativeFiberwiseExtension
import PoincareConjecture.Proofs.M25.Mathlib.SmoothRetainedClamp
import Mathlib.Geometry.Manifold.Algebra.Structures

set_option autoImplicit false
open Set
open scoped Manifold ContDiff
universe u v w
namespace Diffeomorph
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {H : Type v} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {K : Type w} [TopologicalSpace K] [ChartedSpace H K]
  [IsManifold I ∞ K] [CompactSpace K]

theorem exists_two_ended_fiberwise_interpolation
    (g0 g1 : K × ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    (hg0 : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ g0
      (univ ×ˢ Ioo (-r) r))
    (hg1 : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ g1
      (univ ×ˢ Ioo (1 - r) (1 + r)))
    (hzero : ∀ q : K, g0 (q, 0) = 0)
    (hone : ∀ q : K, g1 (q, 1) = 1)
    (hd0 : ∀ q : K, ∀ s ∈ Ioo (-r) r,
      0 < deriv (fun t : ℝ => g0 (q, t)) s)
    (hd1 : ∀ q : K, ∀ s ∈ Ioo (1 - r) (1 + r),
      0 < deriv (fun t : ℝ => g1 (q, t)) s) :
    ∃ (delta : ℝ)
      (D : Diffeomorph (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (K × ℝ) (K × ℝ) ∞),
      0 < delta ∧ delta < r ∧ delta < 1 / 8 ∧
      (∀ z : K × ℝ, (D z).1 = z.1 ∧ (D.symm z).1 = z.1) ∧
      (∀ q : K, D (q, 0) = (q, 0) ∧ D (q, 1) = (q, 1)) ∧
      (∀ q : K, ∀ s : ℝ,
        0 < deriv (fun t : ℝ => (D (q, t)).2) s) ∧
      EqOn (fun z : K × ℝ => (D z).2) g0
        (univ ×ˢ Ioo (-delta) delta) ∧
      EqOn (fun z : K × ℝ => (D z).2) g1
        (univ ×ˢ Ioo (1 - delta) (1 + delta)) ∧
      D '' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1 ∧
      D ⁻¹' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1 ∧
      D '' (univ ×ˢ Ioo (0 : ℝ) 1) = univ ×ˢ Ioo (0 : ℝ) 1 ∧
      D ⁻¹' (univ ×ˢ Ioo (0 : ℝ) 1) = univ ×ˢ Ioo (0 : ℝ) 1 := by
  classical
  have huniform (G : K × ℝ → ℝ) (c v : ℝ)
      (hG : ContinuousOn G (univ ×ˢ Ioo (c - r) (c + r)))
      (hc : ∀ q : K, G (q, c) = v) :
      ∃ a : ℝ, 0 < a ∧ ∀ (q : K) (s : ℝ), |s - c| < a →
        G (q, s) ∈ Ioo (v - 1 / 4) (v + 1 / 4) := by
    let O : Set (K × ℝ) :=
      (univ ×ˢ Ioo (c - r) (c + r)) ∩ G ⁻¹' Ioo (v - 1 / 4) (v + 1 / 4)
    have hO : IsOpen O :=
      hG.isOpen_inter_preimage (isOpen_univ.prod isOpen_Ioo) isOpen_Ioo
    have hslice : (univ : Set K) ×ˢ {c} ⊆ O := by
      rintro ⟨q, s⟩ ⟨_, hs⟩
      have hsc : s = c := mem_singleton_iff.mp hs
      subst s
      refine ⟨⟨mem_univ _, ?_⟩, ?_⟩
      · constructor <;> linarith
      · change v - 1 / 4 < G (q, c) ∧ G (q, c) < v + 1 / 4
        rw [hc q]
        constructor <;> linarith
    obtain ⟨U, V, _, hV, hKU, hcV, hUV⟩ :=
      generalized_tube_lemma isCompact_univ isCompact_singleton hO hslice
    have hcV' : c ∈ V := hcV (mem_singleton c)
    obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hcV')
    refine ⟨a, ha, ?_⟩
    intro q s hs
    exact (hUV ⟨hKU (mem_univ q), hball (by simpa [Real.dist_eq] using hs)⟩).2
  obtain ⟨a0, ha0, hbound0⟩ :=
    huniform g0 0 0 (by simpa using hg0.continuousOn) hzero
  obtain ⟨a1, ha1, hbound1⟩ := huniform g1 1 1 hg1.continuousOn hone
  have hmin : 0 < min (a0 / 4) (min (a1 / 4) (min (r / 4) (1 / 8 : ℝ))) := by
    exact lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by norm_num)))
  obtain ⟨d, hd, hdsmall⟩ := exists_between hmin
  have hda0 : 4 * d < a0 := by
    have h := (lt_min_iff.mp hdsmall).1
    linarith
  have hda1 : 4 * d < a1 := by
    have h := (lt_min_iff.mp (lt_min_iff.mp hdsmall).2).1
    linarith
  have hdr : 4 * d < r := by
    have h := (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp hdsmall).2).2).1
    linarith
  have hdsmall' : d < 1 / 8 :=
    (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp hdsmall).2).2).2
  let weight : ℝ → ℝ := fun s => Real.smoothTransition ((s - d) / d)
  let line : ℝ → ℝ := fun s => 3 / 8 + s / 4
  let blend : (K × ℝ → ℝ) → K × ℝ → ℝ := fun G z =>
    (1 - weight z.2) * G z + weight z.2 * line z.2
  have hws : ContDiff ℝ ∞ weight :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const d)
  have hls : ContDiff ℝ ∞ line := contDiff_const.add (contDiff_id.div_const 4)
  have hwd : ∀ s : ℝ, 0 ≤ deriv weight s := by
    have hm : Monotone weight := by
      intro s t hst
      exact Real.smoothTransition.monotone
        (div_le_div_of_nonneg_right (sub_le_sub_right hst d) hd.le)
    exact fun _ => hm.deriv_nonneg
  have hwb (s : ℝ) : weight s ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hwzero (s : ℝ) (hs : s ≤ d) : weight s = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hd.le)
  have hwone (s : ℝ) (hs : 2 * d ≤ s) : weight s = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hd).mpr (by linarith))
  have hld (s : ℝ) : HasDerivAt line (1 / 4) s := by
    simpa only [line, one_div] using!
      ((hasDerivAt_id s).div_const 4).const_add (3 / 8)
  have hleft (G : K × ℝ → ℝ) (z : K × ℝ) (hz : z.2 ≤ d) : blend G z = G z := by
    simp only [blend, hwzero z.2 hz, sub_zero, one_mul, zero_mul, add_zero]
  have hright (G : K × ℝ → ℝ) (z : K × ℝ) (hz : 2 * d ≤ z.2) :
      blend G z = line z.2 := by
    simp only [blend, hwone z.2 hz, sub_self, zero_mul, one_mul, zero_add]
  have hwm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : K × ℝ => weight z.2) := hws.comp_contMDiff contMDiff_snd
  have hlm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : K × ℝ => line z.2) := hls.comp_contMDiff contMDiff_snd
  have hblend (G : K × ℝ → ℝ)
      (hGs : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ G
        (univ ×ˢ Ioo (-r) r))
      (hGp : ∀ q : K, ∀ s ∈ Ioo (-r) r,
        0 < deriv (fun t : ℝ => G (q, t)) s)
      (hGb : ∀ q : K, ∀ s ∈ Ioo (-d) (3 * d), G (q, s) < 1 / 4) :
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (blend G)
          (univ ×ˢ Ioi (-d)) ∧
        ∀ q : K, ∀ s ∈ Ioi (-d), 0 < deriv (fun t : ℝ => blend G (q, t)) s := by
    have hdom : univ ×ˢ Ioo (-d) (3 * d) ⊆ (univ : Set K) ×ˢ Ioo (-r) r := by
      intro z hz
      exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    have hsmall : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (blend G)
        (univ ×ˢ Ioo (-d) (3 * d)) :=
      ((contMDiff_const.sub hwm).contMDiffOn.mul (hGs.mono hdom)).add
        (hwm.mul hlm).contMDiffOn
    refine ⟨?_, ?_⟩
    · intro z hz
      by_cases hs : z.2 < 3 * d
      · exact (hsmall.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
          ⟨mem_univ _, hz.2, hs⟩)).contMDiffWithinAt
      · have htwo : 2 * d < z.2 := by linarith
        apply (hlm.contMDiffAt.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds htwo] with y hy
        exact hright G y hy.le
    · intro q s hs
      change -d < s at hs
      by_cases htwo : 2 * d < s
      · have hder : HasDerivAt (fun t : ℝ => blend G (q, t)) (1 / 4) s := by
          apply (hld s).congr_of_eventuallyEq
          filter_upwards [lt_mem_nhds htwo] with t ht
          exact hright G (q, t) ht.le
        rw [hder.deriv]
        norm_num
      · have hsdom : s ∈ Ioo (-r) r := by
          constructor <;> linarith [le_of_not_gt htwo]
        have hp := hGp q s hsdom
        have hgder := (differentiableAt_of_deriv_ne_zero (ne_of_gt hp)).hasDerivAt
        have hwder := (hws.differentiable (by simp) s).hasDerivAt
        have hformula : deriv (fun t : ℝ => blend G (q, t)) s =
            (1 - weight s) * deriv (fun t : ℝ => G (q, t)) s + weight s / 4 +
              deriv weight s * (line s - G (q, s)) := by
          have h := (((hasDerivAt_const s 1).sub hwder).mul hgder).add
            (hwder.mul (hld s))
          have h' : HasDerivAt (fun t : ℝ => blend G (q, t))
              ((0 - deriv weight s) * G (q, s) +
                (1 - weight s) * deriv (fun t : ℝ => G (q, t)) s +
                (deriv weight s * line s + weight s * (1 / 4))) s := by
            simpa only [blend, Pi.add_apply, Pi.sub_apply, Pi.mul_apply] using! h
          rw [h'.deriv]
          ring
        have hgap : 0 < line s - G (q, s) := by
          have hb := hGb q s ⟨hs, by linarith [le_of_not_gt htwo]⟩
          dsimp only [line]
          linarith
        have hbase : 0 <
            (1 - weight s) * deriv (fun t : ℝ => G (q, t)) s + weight s / 4 := by
          rcases lt_or_eq_of_le (hwb s).2 with hlt | heq
          · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hp)
              (div_nonneg (hwb s).1 (by norm_num))
          · rw [heq]
            norm_num
        rw [hformula]
        exact add_pos_of_pos_of_nonneg hbase (mul_nonneg (hwd s) hgap.le)
  have hb0 (q : K) (s : ℝ) (hs : s ∈ Ioo (-d) (3 * d)) : g0 (q, s) < 1 / 4 := by
    have ha : |s - 0| < a0 := abs_lt.mpr (by constructor <;> linarith [hs.1, hs.2])
    simpa using (hbound0 q s ha).2
  let reflect : K × ℝ → K × ℝ := fun z => (z.1, 1 - z.2)
  let G1 : K × ℝ → ℝ := fun z => 1 - g1 (reflect z)
  have hrefl : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ reflect :=
    contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)
  have hG1s : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ G1
      (univ ×ˢ Ioo (-r) r) := by
    apply contMDiffOn_const.sub (hg1.comp hrefl.contMDiffOn ?_)
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    change 1 - r < 1 - z.2 ∧ 1 - z.2 < 1 + r
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hG1p (q : K) (s : ℝ) (hs : s ∈ Ioo (-r) r) :
      0 < deriv (fun t : ℝ => G1 (q, t)) s := by
    have ht : 1 - s ∈ Ioo (1 - r) (1 + r) := by
      constructor <;> linarith [hs.1, hs.2]
    have hp := hd1 q (1 - s) ht
    have hgd := (differentiableAt_of_deriv_ne_zero (ne_of_gt hp)).hasDerivAt
    have hrd := (hasDerivAt_const s 1).sub (hasDerivAt_id s)
    have h := (hasDerivAt_const s 1).sub (hgd.comp s hrd)
    have heq : deriv (fun t : ℝ => G1 (q, t)) s =
        deriv (fun t : ℝ => g1 (q, t)) (1 - s) := by
      have h' : HasDerivAt (fun t : ℝ => G1 (q, t))
          (deriv (fun t : ℝ => g1 (q, t)) (1 - s)) s := by
        simpa only [G1, reflect, Function.comp_apply, Pi.sub_apply,
          zero_sub, mul_neg_one, neg_neg] using! h
      exact h'.deriv
    rw [heq]
    exact hp
  have hG1b (q : K) (s : ℝ) (hs : s ∈ Ioo (-d) (3 * d)) : G1 (q, s) < 1 / 4 := by
    have ha : |(1 - s) - 1| < a1 := by
      rw [show (1 - s) - 1 = -s by ring, abs_neg]
      exact abs_lt.mpr (by constructor <;> linarith [hs.1, hs.2])
    have hb := (hbound1 q (1 - s) ha).1
    dsimp only [G1, reflect]
    linarith
  obtain ⟨hlo, hlop⟩ := hblend g0 hg0 hd0 hb0
  obtain ⟨hup, hupp⟩ := hblend G1 hG1s hG1p hG1b
  let upper : K × ℝ → ℝ := fun z => 1 - blend G1 (reflect z)
  have hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ upper
      (univ ×ˢ Iio (1 + d)) := by
    apply contMDiffOn_const.sub (hup.comp hrefl.contMDiffOn ?_)
    intro z hz
    have hz' : z.2 < 1 + d := hz.2
    exact ⟨mem_univ _, by change -d < 1 - z.2; linarith⟩
  have hupderiv (q : K) (s : ℝ) (hs : s < 1 + d) :
      0 < deriv (fun t : ℝ => upper (q, t)) s := by
    have hp := hupp q (1 - s) (by change -d < 1 - s; linarith)
    have hgd := (differentiableAt_of_deriv_ne_zero (ne_of_gt hp)).hasDerivAt
    have hrd := (hasDerivAt_const s 1).sub (hasDerivAt_id s)
    have h := (hasDerivAt_const s 1).sub (hgd.comp s hrd)
    have heq : deriv (fun t : ℝ => upper (q, t)) s =
        deriv (fun t : ℝ => blend G1 (q, t)) (1 - s) := by
      have h' : HasDerivAt (fun t : ℝ => upper (q, t))
          (deriv (fun t : ℝ => blend G1 (q, t)) (1 - s)) s := by
        simpa only [upper, reflect, Function.comp_apply, Pi.sub_apply,
          zero_sub, mul_neg_one, neg_neg] using! h
      exact h'.deriv
    rw [heq]
    exact hp
  have hflat (z : K × ℝ) (hz0 : 2 * d ≤ z.2) (hz1 : z.2 ≤ 1 - 2 * d) :
      blend g0 z = upper z := by
    rw [hright g0 z hz0]
    change line z.2 = 1 - blend G1 (z.1, 1 - z.2)
    rw [hright G1 (z.1, 1 - z.2) (by dsimp; linarith)]
    dsimp only [line]
    ring
  let h : K × ℝ → ℝ := fun z => if z.2 ≤ 1 / 2 then blend g0 z else upper z
  have hloeq (z : K × ℝ) (hz : z.2 < 3 / 4) : h z = blend g0 z := by
    dsimp only [h]
    split_ifs with ht
    · rfl
    · exact (hflat z (by linarith) (by linarith)).symm
  have hupeq (z : K × ℝ) (hz : 1 / 4 < z.2) : h z = upper z := by
    dsimp only [h]
    split_ifs with ht
    · exact hflat z (by linarith) (by linarith)
    · rfl
  have hh : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h
      (univ ×ˢ Ioo (-d) (1 + d)) := by
    intro z hz
    by_cases ht : z.2 < 3 / 4
    · have hs := hlo.contMDiffAt ((isOpen_univ.prod isOpen_Ioi).mem_nhds
        ⟨mem_univ _, hz.2.1⟩)
      apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds ht] with y hy
      exact hloeq y hy
    · have ht' : 1 / 4 < z.2 := by linarith
      have hs := hu.contMDiffAt ((isOpen_univ.prod isOpen_Iio).mem_nhds
        ⟨mem_univ _, hz.2.2⟩)
      apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds ht'] with y hy
      exact hupeq y hy
  have hhp (q : K) (s : ℝ) (hs : s ∈ Ioo (-d) (1 + d)) :
      0 < deriv (fun t : ℝ => h (q, t)) s := by
    by_cases ht : s < 3 / 4
    · have hp := hlop q s hs.1
      have hder := (differentiableAt_of_deriv_ne_zero (ne_of_gt hp)).hasDerivAt
      have hder' : HasDerivAt (fun t : ℝ => h (q, t))
          (deriv (fun t : ℝ => blend g0 (q, t)) s) s := by
        apply hder.congr_of_eventuallyEq
        filter_upwards [gt_mem_nhds ht] with t hts
        exact hloeq (q, t) hts
      rw [hder'.deriv]
      exact hp
    · have ht' : 1 / 4 < s := by linarith
      have hp := hupderiv q s hs.2
      have hder := (differentiableAt_of_deriv_ne_zero (ne_of_gt hp)).hasDerivAt
      have hder' : HasDerivAt (fun t : ℝ => h (q, t))
          (deriv (fun t : ℝ => upper (q, t)) s) s := by
        apply hder.congr_of_eventuallyEq
        filter_upwards [lt_mem_nhds ht'] with t hts
        exact hupeq (q, t) hts
      rw [hder'.deriv]
      exact hp
  have hzeroAgree (z : K × ℝ) (hz : z.2 ≤ d) : h z = g0 z := by
    rw [hloeq z (by linarith), hleft g0 z hz]
  have honeAgree (z : K × ℝ) (hz : 1 - d ≤ z.2) : h z = g1 z := by
    rw [hupeq z (by linarith)]
    change 1 - blend G1 (z.1, 1 - z.2) = g1 z
    rw [hleft G1 (z.1, 1 - z.2) (by dsimp; linarith)]
    simp only [G1, reflect, sub_sub_cancel, Prod.eta]
  have hhzero (q : K) : h (q, 0) = 0 := by
    rw [hzeroAgree (q, 0) hd.le, hzero q]
  have hhone (q : K) : h (q, 1) = 1 := by
    rw [honeAgree (q, 1) (by dsimp; linarith), hone q]
  have hleftGap : -d < -d / 2 := by linarith
  have hgap : -d / 2 < 1 + d / 2 := by linarith
  have hrightGap : 1 + d / 2 < 1 + d := by linarith
  obtain ⟨rho, hrhos, _, hrange, hagree, hrhod, hrhol, hrhor⟩ :=
    Real.exists_smooth_retained_clamp hleftGap hgap hrightGap
  obtain ⟨D, hD, hDi, hDp, hDa, _⟩ :=
    exists_relative_fiberwise_extension (Diffeomorph.refl I K ∞) h
      hleftGap hgap hrightGap hh hhp rho hrhos hrange hagree hrhod hrhol hrhor
  have hfirst (z : K × ℝ) : (D z).1 = z.1 ∧ (D.symm z).1 = z.1 := by
    constructor
    · simpa using congrArg Prod.fst (hD z)
    · simpa using (hDi z).1
  have hretained (z : K × ℝ) (hz : z.2 ∈ Icc (-d / 2) (1 + d / 2)) :
      D z = (z.1, h z) := by simpa using (hDa z hz).1
  have hfixed (q : K) : D (q, 0) = (q, 0) ∧ D (q, 1) = (q, 1) := by
    constructor
    · rw [hretained (q, 0) (by constructor <;> dsimp <;> linarith), hhzero q]
    · rw [hretained (q, 1) (by constructor <;> dsimp <;> linarith), hhone q]
  have hpositive (q : K) (s : ℝ) : 0 < deriv (fun t : ℝ => (D (q, t)).2) s := by
    have heq : (fun t : ℝ => (D (q, t)).2) =
        (fun t : ℝ => h (q, rho t) + t - rho t) := by
      funext t
      exact congrArg Prod.snd (hD (q, t))
    rw [heq]
    exact hDp q s
  have hmono (q : K) : StrictMono (fun s : ℝ => (D (q, s)).2) :=
    strictMono_of_deriv_pos (hpositive q)
  have hfixed0 (q : K) : (D (q, 0)).2 = 0 := congrArg Prod.snd (hfixed q).1
  have hfixed1 (q : K) : (D (q, 1)).2 = 1 := congrArg Prod.snd (hfixed q).2
  have hclosed (z : K × ℝ) :
      D z ∈ univ ×ˢ Icc (0 : ℝ) 1 ↔ z ∈ univ ×ˢ Icc (0 : ℝ) 1 := by
    rcases z with ⟨q, s⟩
    simpa only [mem_prod, mem_univ, true_and, mem_Icc, hfixed0, hfixed1] using
      and_congr ((hmono q).le_iff_le (a := 0) (b := s))
        ((hmono q).le_iff_le (a := s) (b := 1))
  have hopen (z : K × ℝ) :
      D z ∈ univ ×ˢ Ioo (0 : ℝ) 1 ↔ z ∈ univ ×ˢ Ioo (0 : ℝ) 1 := by
    rcases z with ⟨q, s⟩
    simpa only [mem_prod, mem_univ, true_and, mem_Ioo, hfixed0, hfixed1] using
      and_congr ((hmono q).lt_iff_lt (a := 0) (b := s))
        ((hmono q).lt_iff_lt (a := s) (b := 1))
  have himage (S : Set ℝ) (hmem : ∀ z : K × ℝ, D z ∈ univ ×ˢ S ↔ z ∈ univ ×ˢ S) :
      D '' (univ ×ˢ S) = univ ×ˢ S := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).2 hx
    · intro hz
      refine ⟨D.symm z, (hmem (D.symm z)).1 ?_, D.apply_symm_apply z⟩
      simpa using hz
  refine ⟨d / 2, D, by positivity, by linarith, by linarith, hfirst, hfixed,
    hpositive, ?_, ?_, himage _ hclosed, Set.ext hclosed, himage _ hopen, Set.ext hopen⟩
  · intro z hz
    change (D z).2 = g0 z
    rw [hretained z (by constructor <;> linarith [hz.2.1, hz.2.2])]
    exact hzeroAgree z (by linarith [hz.2.2])
  · intro z hz
    change (D z).2 = g1 z
    rw [hretained z (by constructor <;> linarith [hz.2.1, hz.2.2])]
    exact honeAgree z (by linarith [hz.2.1])

end Diffeomorph
