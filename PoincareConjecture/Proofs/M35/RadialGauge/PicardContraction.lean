import PoincareConjecture.Proofs.M35.RadialGauge.HeatC1Bounds
import PoincareConjecture.Proofs.M35.RadialGauge.RadialSymmetry










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))



theorem gaugeSource_weighted_bound {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ}
    {u : ℝ → V → ℝ} {eta B L C t : ℝ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hb : ∀ s ∈ Icc 0 t, ∀ x, ‖b s x‖ ≤ B)
    (hGzero : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * |G s x 0| ≤ C)
    (hGlip : ∀ s ∈ Icc 0 t, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      |G s x a - G s x c| ≤ L * |a - c|)
    (hu : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * |u s x| ≤ eta)
    (hdu : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖fderiv ℝ (u s) x‖ ≤ eta)
    (s : ℝ) (hs : s ∈ Icc 0 t) (x : V) :
    (1 + ‖x‖) * ‖gaugeSource (b s) (G s) (u s) x‖ ≤
      B * eta + eta ^ 2 + L * eta + C := by
  have hua : |u s x| ≤ eta := by
    nlinarith [hu s hs x, mul_nonneg (norm_nonneg x) (abs_nonneg (u s x))]
  simpa only [gaugeSource, Real.norm_eq_abs] using
    semilinearSource_weighted_bound (by linarith [norm_nonneg x]) heta hB hL
      (b s x) (G s x) (fderiv ℝ (u s) x) (hb s hs x) (hu s hs x) (hdu s hs x)
      (hGzero s hs x) (by simpa using hGlip s hs x (u s x) 0 hua (by simpa using heta))




theorem gaugeDuhamel_c1_difference_bound
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u v : ℝ → V → ℝ}
    {eta B L C d t : ℝ} (heta : 0 ≤ eta) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hC : 0 ≤ C) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (hb : ∀ s ∈ Icc 0 t, ∀ x, ‖b s x‖ ≤ B)
    (hGzero : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * |G s x 0| ≤ C)
    (hGlip : ∀ s ∈ Icc 0 t, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      |G s x a - G s x c| ≤ L * |a - c|)
    (hu : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * |u s x| ≤ eta)
    (hv : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * |v s x| ≤ eta)
    (hdu : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖fderiv ℝ (u s) x‖ ≤ eta)
    (hdv : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖fderiv ℝ (v s) x‖ ≤ eta)
    (huv : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * |u s x - v s x| ≤ d)
    (hduv : ∀ s ∈ Icc 0 t, ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (u s) x - fderiv ℝ (v s) x‖ ≤ d)
    (hmu : StronglyMeasurable (fun p : ℝ × V => gaugeSource (b p.1) (G p.1) (u p.1) p.2))
    (hmv : StronglyMeasurable (fun p : ℝ × V => gaugeSource (b p.1) (G p.1) (v p.1) p.2))
    (hru : ∀ s ∈ Icc 0 t, ContDiff ℝ 1 (gaugeSource (b s) (G s) (u s)))
    (hrv : ∀ s ∈ Icc 0 t, ContDiff ℝ 1 (gaugeSource (b s) (G s) (v s)))
    (hbu : ∀ s ∈ Ico 0 t, ∃ D : ℝ, ∀ x,
      ‖fderiv ℝ (gaugeSource (b s) (G s) (u s)) x‖ ≤ D)
    (hbv : ∀ s ∈ Ico 0 t, ∃ D : ℝ, ∀ x,
      ‖fderiv ℝ (gaugeSource (b s) (G s) (v s)) x‖ ≤ D) (x : V) :
    (1 + ‖x‖) * ‖gaugeDuhamel b G u t x - gaugeDuhamel b G v t x‖ ≤
      (L + B + 2 * eta) * d * heatC1Gain (n + 1) t ∧
    (1 + ‖x‖) * ‖fderiv ℝ (gaugeDuhamel b G u t) x -
      fderiv ℝ (gaugeDuhamel b G v t) x‖ ≤
      (L + B + 2 * eta) * d * heatC1Gain (n + 1) t := by
  have hS : 0 ≤ B * eta + eta ^ 2 + L * eta + C := by positivity
  have hfu := gaugeSource_weighted_bound heta hB hL hb hGzero hGlip hu hdu
  have hfv := gaugeSource_weighted_bound heta hB hL hb hGzero hGlip hv hdv
  have hdiff (s : ℝ) (hs : s ∈ Icc 0 t) (y : V) :
      (1 + ‖y‖) * ‖gaugeSource (b s) (G s) (u s) y -
        gaugeSource (b s) (G s) (v s) y‖ ≤ (L + B + 2 * eta) * d := by
    have hua : |u s y| ≤ eta := by
      nlinarith [hu s hs y, mul_nonneg (norm_nonneg y) (abs_nonneg (u s y))]
    have hva : |v s y| ≤ eta := by
      nlinarith [hv s hs y, mul_nonneg (norm_nonneg y) (abs_nonneg (v s y))]
    have h := semilinearSource_weighted_lipschitz (by linarith [norm_nonneg y])
      (b s y) (G s y) (fderiv ℝ (u s) y) (fderiv ℝ (v s) y)
      (hb s hs y) (hdu s hs y) (hdv s hs y) (hGlip s hs y (u s y) (v s y) hua hva)
    have h1 := mul_le_mul_of_nonneg_left (huv s hs y) hL
    have h2 := mul_le_mul_of_nonneg_left (hduv s hs y) (show 0 ≤ B + 2 * eta by positivity)
    change (1 + ‖y‖) * |semilinearSource _ _ _ _ - semilinearSource _ _ _ _| ≤ _
    nlinarith [h, h1, h2]
  exact heatDuhamel_c1_difference_bound hS hS (by positivity) ht
    hmu hmv hru hrv hbu hbv hfu hfv hdiff x



theorem exists_short_time_gauge_constants {eta S K T : ℝ}
    (heta : 0 < eta) (hS : 0 ≤ S) (hK : 0 ≤ K) (hT : 0 < T) :
    ∃ t : ℝ, 0 < t ∧ t ≤ T ∧ S * heatC1Gain (n + 1) t ≤ eta ∧
      K * heatC1Gain (n + 1) t ≤ 1 / 2 := by
  have he : 0 < min (eta / (S + 1)) (1 / (2 * (K + 1))) := by positivity
  obtain ⟨a, ha, hga⟩ := exists_pos_heatC1Gain_lt (n := n + 1) he
  let t := min a T
  have ht : 0 < t := lt_min ha hT
  have hg : heatC1Gain (n + 1) t < min (eta / (S + 1)) (1 / (2 * (K + 1))) :=
    (heatC1Gain_mono ht.le (min_le_left a T)).trans_lt hga
  have hg0 := heatC1Gain_nonneg (n := n + 1) ht.le
  have hs := (lt_div_iff₀ (show 0 < S + 1 by linarith)).mp
    (hg.trans_le (min_le_left _ _))
  have hk := (lt_div_iff₀ (show 0 < 2 * (K + 1) by positivity)).mp
    (hg.trans_le (min_le_right _ _))
  exact ⟨t, ht, min_le_right a T, by nlinarith [hs, hg0], by nlinarith [hk, hg0]⟩

end PoincareConjecture.M35.RadialGauge
