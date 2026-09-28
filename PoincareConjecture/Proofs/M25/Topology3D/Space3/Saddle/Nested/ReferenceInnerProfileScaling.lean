import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceEndAxis
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag









set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower




theorem exists_inner_reference_profile_scaling
    (P : SurgeryCapProfile) (h m lambda : ℝ)
    (hlambda : 0 < lambda) (hgap : lambda < h - m) :
    ∃ (g : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) (a : ℝ → ℝ),
      (∀ t : ℝ, g t = h + lambda * t - (h - m - lambda) *
        (1 - Real.smoothTransition (2 * t + 3 / 2))) ∧
      StrictMono g ∧ g (-1) = m ∧ g 0 = h ∧
      (∀ t : ℝ, -1 / 4 ≤ t → g t = h + lambda * t) ∧
      ContDiff ℝ ∞ a ∧ (∀ t : ℝ, 0 < a t) ∧
      (∀ t : ℝ, -1 / 8 ≤ t → a t = Real.sqrt (g t - m)) ∧
      (∀ t ∈ Icc (-1 : ℝ) 0,
        a t ^ 2 * (P.horizontal t * Real.sqrt (1 - t ^ 2)) ^ 2 = g t - m) := by
  classical
  obtain ⟨g, hg, _, hgm, _, hgr, hgm1, hg0⟩ :=
    exists_nonnested_reference_end_axis h (h - m) lambda hlambda hgap
  have hpole : g (-1) = m := by
    rw [hgm1]
    ring
  have hgapPos : 0 < h - m - lambda := sub_pos.mpr hgap
  let chi : ℝ → ℝ := fun t => Real.smoothTransition (2 * t + 3 / 2)
  have hchi : ContDiff ℝ ∞ chi := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hchi0 (t : ℝ) (ht : t ≤ -3 / 4) : chi t = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hquot : ContDiff ℝ ∞ (fun t : ℝ => chi t / (t + 1)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    by_cases ht : t = -1
    · subst t
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds (show (-1 : ℝ) < -3 / 4 by norm_num)] with s hs
      rw [hchi0 s hs.le, zero_div]
    · exact hchi.contDiffAt.div (contDiffAt_id.add contDiffAt_const)
        (by intro hzero; apply ht; linarith)
  let R : ℝ → ℝ := fun t => lambda + (h - m - lambda) * (chi t / (t + 1))
  have hRsm : ContDiff ℝ ∞ R := contDiff_const.add (contDiff_const.mul hquot)
  have hRp (t : ℝ) : 0 < R t := by
    by_cases ht : t ≤ -3 / 4
    · simpa only [R, hchi0 t ht, zero_div, mul_zero, add_zero] using hlambda
    · have hden : 0 < t + 1 := by linarith [lt_of_not_ge ht]
      have hq : 0 ≤ chi t / (t + 1) :=
        div_nonneg (Real.smoothTransition.nonneg _) hden.le
      exact add_pos_of_pos_of_nonneg hlambda (mul_nonneg hgapPos.le hq)
  have hRlaw (t : ℝ) : (t + 1) * R t = g t - m := by
    by_cases ht : t = -1
    · subst t
      rw [hpole]
      simp
    · rw [hg t]
      change (t + 1) * R t =
        h + lambda * t - (h - m - lambda) * (1 - chi t) - m
      dsimp [R]
      field_simp [show t + 1 ≠ 0 by intro hzero; apply ht; linarith]
      ring
  let bot : ℝ → ℝ := fun t => Real.sqrt (R t / (1 - t)) / P.horizontal t
  let top : ℝ → ℝ := fun t => Real.sqrt (g t - m)
  have htop (t : ℝ) (ht : -3 / 16 < t) : 0 < g t - m := by
    rw [hgr t (by linarith)]
    have hh := mul_lt_mul_of_pos_left ht hlambda
    nlinarith
  have hbot (t : ℝ) (ht : t < -1 / 16) : ContDiffAt ℝ ∞ bot t := by
    have hden : 0 < 1 - t := by linarith only [ht]
    exact ((hRsm.contDiffAt.div (contDiffAt_const.sub contDiffAt_id)
      hden.ne').sqrt (ne_of_gt (div_pos (hRp t) hden))).div
        P.horizontal_smooth.contDiffAt (P.horizontal_pos t).ne'
  have hagree (t : ℝ) (ht : t ∈ Ioo (-3 / 16 : ℝ) (-1 / 16)) : bot t = top t := by
    have hs : 0 < 1 - t ^ 2 := by
      have hh := mul_pos (show 0 < 1 - t by linarith [ht.2])
        (show 0 < 1 + t by linarith [ht.1])
      nlinarith only [hh]
    have hsSq := Real.sq_sqrt hs.le
    have hn : P.horizontal t = (Real.sqrt (1 - t ^ 2))⁻¹ :=
      P.horizontal_near t (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hbSq : bot t ^ 2 = g t - m := by
      dsimp [bot]
      rw [div_pow, Real.sq_sqrt (div_nonneg (hRp t).le (by linarith [ht.2])), hn,
        inv_pow, div_inv_eq_mul, hsSq]
      calc
        R t / (1 - t) * (1 - t ^ 2) = (t + 1) * R t := by
          field_simp [show 1 - t ≠ 0 by linarith [ht.2]]
          ring
        _ = g t - m := hRlaw t
    have htSq : top t ^ 2 = g t - m := Real.sq_sqrt (htop t ht.1).le
    have hb0 : 0 ≤ bot t := div_nonneg (Real.sqrt_nonneg _) (P.horizontal_pos t).le
    have ht0 : 0 ≤ top t := Real.sqrt_nonneg _
    nlinarith only [hbSq, htSq, hb0, ht0]
  let a : ℝ → ℝ := fun t => if t < -1 / 8 then bot t else top t
  have hasm : ContDiff ℝ ∞ a := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    by_cases ht : t < -1 / 8
    · apply (hbot t (by linarith)).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact if_pos hs
    · have htt : -3 / 16 < t := by linarith [le_of_not_gt ht]
      apply ((g.contDiff.contDiffAt.sub contDiffAt_const).sqrt
        (htop t htt).ne').congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds htt] with s hs
      dsimp [a]
      split_ifs with hss
      · exact hagree s ⟨hs, by linarith⟩
      · rfl
  have hap (t : ℝ) : 0 < a t := by
    dsimp [a]
    split_ifs with ht
    · exact div_pos (Real.sqrt_pos.2 (div_pos (hRp t) (by linarith))) (P.horizontal_pos t)
    · exact Real.sqrt_pos.2 (htop t (by linarith [le_of_not_gt ht]))
  have hatop (t : ℝ) (ht : -1 / 8 ≤ t) : a t = Real.sqrt (g t - m) :=
    if_neg (not_lt.mpr ht)
  let rn : ℝ → ℝ := fun t => P.horizontal t * Real.sqrt (1 - t ^ 2)
  have hasq (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 0) :
      a t ^ 2 * rn t ^ 2 = g t - m := by
    have hs : 0 ≤ 1 - t ^ 2 := by
      have hh := mul_nonneg (show 0 ≤ 1 - t by linarith [ht.2])
        (show 0 ≤ 1 + t by linarith [ht.1])
      nlinarith only [hh]
    by_cases hb : t < -1 / 8
    · rw [show a t = bot t from if_pos hb]
      calc
        bot t ^ 2 * rn t ^ 2 = R t / (1 - t) * (1 - t ^ 2) := by
          dsimp [bot, rn]
          rw [div_pow, mul_pow, Real.sq_sqrt hs,
            Real.sq_sqrt (div_nonneg (hRp t).le (by linarith [ht.2]))]
          field_simp [(P.horizontal_pos t).ne']
        _ = (t + 1) * R t := by
          field_simp [show 1 - t ≠ 0 by linarith [ht.2]]
          ring
        _ = g t - m := hRlaw t
    · rw [hatop t (le_of_not_gt hb), Real.sq_sqrt (htop t (by linarith)).le]
      have hrn : rn t = 1 := by
        dsimp [rn]
        rw [P.horizontal_near t (abs_le.mpr ⟨by linarith, by linarith [ht.2]⟩)]
        have hr : 0 < 1 - t ^ 2 := by
          have hh := mul_pos (show 0 < 1 - t by linarith [ht.2])
            (show 0 < 1 + t by linarith [le_of_not_gt hb])
          nlinarith only [hh]
        exact inv_mul_cancel₀ (Real.sqrt_pos.2 hr).ne'
      rw [hrn, one_pow, mul_one]
  exact ⟨g, a, hg, hgm, hpole, hg0, hgr, hasm, hap, hatop, hasq⟩

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
