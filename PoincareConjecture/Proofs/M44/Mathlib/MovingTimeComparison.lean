import PoincareConjecture.Proofs.M44.Mathlib.CompactTimeModulus
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare




theorem uniformly_close_on_moving_initial_intervals
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K : Set X} (hK : IsCompact K) {H c L : ℝ}
    (hc : 0 ≤ c) (hcH : c ≤ H) (hL : 0 ≤ L)
    {endpoints : ℕ → ℝ} (hend : Tendsto endpoints atTop (𝓝 c))
    (hendH : ∀ n, endpoints n ≤ H)
    {f : ℕ → ℝ × X → Y} {g : ℝ × X → Y}
    (hg : ContinuousOn g (Icc (0 : ℝ) H ×ˢ K))
    (hbirth : TendstoUniformlyOn (fun n x => f n (0, x)) (fun x => g (0, x)) atTop K)
    (hinterior : ∀ b : ℝ, 0 ≤ b → b < c →
      TendstoUniformlyOn f g atTop (Icc (0 : ℝ) b ×ˢ K))
    (hmod : ∀ᶠ n in atTop, ∀ s ∈ Ico (0 : ℝ) (endpoints n),
      ∀ t ∈ Ico (0 : ℝ) (endpoints n), ∀ x ∈ K,
        dist (f n (t, x)) (f n (s, x)) ≤ L * |t - s|) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n in atTop,
      ∀ t ∈ Ico (0 : ℝ) (endpoints n), ∀ x ∈ K,
        dist (f n (t, x)) (g (t, x)) < epsilon := by
  intro epsilon hepsilon
  have heps3 : 0 < epsilon / 3 := by positivity
  obtain ⟨delta, hdelta, hmodel⟩ := hg.exists_uniform_time_delta isCompact_Icc hK heps3
  let h := min (delta / 4) (epsilon / (6 * (L + 1)))
  have hden : 0 < 6 * (L + 1) := by positivity
  have hh : 0 < h := lt_min (by positivity) (div_pos hepsilon hden)
  have hhd : 2 * h < delta := by
    have hd : h ≤ delta / 4 := min_le_left _ _
    linarith only [hd, hdelta]
  have hLh : L * (2 * h) ≤ epsilon / 3 := by
    have he : h * (6 * (L + 1)) ≤ epsilon :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    nlinarith only [he, hh]
  let b := max 0 (c - h)
  have hb : 0 ≤ b := le_max_left _ _
  have hbc : b ≤ c := max_le hc (sub_le_self c hh.le)
  have hgap : c - b ≤ h := by
    have hcb : c - h ≤ b := le_max_right _ _
    linarith only [hcb]
  have hfixed : ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) b, ∀ x ∈ K,
      dist (f n (t, x)) (g (t, x)) < epsilon / 3 := by
    by_cases hc0 : c = 0
    · have hb0 : b = 0 := le_antisymm (hbc.trans_eq hc0) hb
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hbirth (epsilon / 3) heps3]
        with n hn
      intro t ht x hx
      have ht0 : t = 0 := le_antisymm (ht.2.trans_eq hb0) ht.1
      subst t
      simpa only [dist_comm] using hn x hx
    · have hbc' : b < c := max_lt (lt_of_le_of_ne hc (Ne.symm hc0)) (sub_lt_self c hh)
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hinterior b hb hbc')
        (epsilon / 3) heps3] with n hn
      intro t ht x hx
      simpa only [dist_comm] using hn (t, x) ⟨ht, hx⟩
  have hupper : ∀ᶠ n in atTop, endpoints n < c + h :=
    hend.eventually (gt_mem_nhds (lt_add_of_pos_right c hh))
  filter_upwards [hmod, hfixed, hupper] with n hmodn hfixedn huppern
  intro t ht x hx
  by_cases htb : t ≤ b
  · exact (hfixedn t ⟨ht.1, htb⟩ x hx).trans (by linarith)
  · have hbt : b < t := lt_of_not_ge htb
    have htime : t - b < 2 * h := by linarith only [ht.2, huppern, hgap]
    have hbI : b ∈ Ico (0 : ℝ) (endpoints n) := ⟨hb, hbt.trans ht.2⟩
    have hactual : dist (f n (t, x)) (f n (b, x)) ≤ epsilon / 3 := by
      have h := hmodn b hbI t ht x hx
      rw [abs_of_nonneg (sub_nonneg.mpr hbt.le)] at h
      exact h.trans ((mul_le_mul_of_nonneg_left htime.le hL).trans hLh)
    have hstandard : dist (g (b, x)) (g (t, x)) < epsilon / 3 := by
      apply hmodel b ⟨hb, hbc.trans hcH⟩ t ⟨ht.1, ht.2.le.trans (hendH n)⟩ _ x hx
      rw [abs_of_neg (sub_neg.mpr hbt)]
      linarith only [htime, hhd]
    have hmiddle := hfixedn b ⟨hb, le_rfl⟩ x hx
    calc
      _ ≤ dist (f n (t, x)) (f n (b, x)) + dist (f n (b, x)) (g (t, x)) :=
        dist_triangle _ _ _
      _ ≤ dist (f n (t, x)) (f n (b, x)) +
          (dist (f n (b, x)) (g (b, x)) + dist (g (b, x)) (g (t, x))) :=
        add_le_add_right (dist_triangle _ _ _) _
      _ < epsilon := by linarith only [hactual, hmiddle, hstandard]

end Poincare
