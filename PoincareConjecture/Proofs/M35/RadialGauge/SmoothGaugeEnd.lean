import PoincareConjecture.Proofs.M35.RadialGauge.SmoothExistence
import PoincareConjecture.Proofs.M35.RadialGauge.ForcingPartialBounds
import PoincareConjecture.Proofs.M35.RadialGauge.ForcingDerivativeLipschitz
import PoincareConjecture.Proofs.M35.RadialGauge.PicardThirdBound
import PoincareConjecture.Proofs.M35.RadialGauge.PicardLimitEnd
import PoincareConjecture.Proofs.M35.RadialGauge.SmoothWeightedLimit










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))
local notation "Cov" => V →L[ℝ] ℝ

noncomputable local instance m35SmoothGaugeEndLocal1 :
    NormedAddCommGroup Cov := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35SmoothGaugeEndLocal2 :
    NormedSpace ℝ Cov := ContinuousLinearMap.toNormedSpace

theorem smooth_gauge_limit_weighted_end
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u : ℝ → V → ℝ} {T eta B L C : ℝ}
    (hT : 0 ≤ T) (heta : 0 ≤ eta) (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hbm : StronglyMeasurable (fun p : Icc 0 T × V => b p.1.1 p.2))
    (hGm : Measurable (fun p : (Icc 0 T × V) × ℝ => G p.1.1.1 p.1.2 p.2))
    (hbs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (b s))
    (hGs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (fun p : V × ℝ => G s p.1 p.2))
    (hbb : ∀ j : ℕ, ∃ D : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ j (b s) x‖ ≤ D)
    (hGw : ∀ j : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta →
      (1 + ‖x‖) * ‖iteratedFDeriv ℝ j (fun p : V × ℝ => G s p.1 p.2) (x, z)‖ ≤ D)
    (hb : ∀ s ∈ Icc 0 T, ∀ x, ‖b s x‖ ≤ B)
    (hGzero : ∀ s ∈ Icc 0 T, ∀ x, (1 + ‖x‖) * |G s x 0| ≤ C)
    (hGlip : ∀ s ∈ Icc 0 T, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      |G s x a - G s x c| ≤ L * |a - c|)
    (hsmall : (B * eta + eta ^ 2 + L * eta + C) * heatC1Gain (n + 1) T ≤ eta)
    (hcontract : (L + B + 2 * eta) * heatC1Gain (n + 1) T ≤ 1 / 4)
    (hhigh : (B + 2 * (n + 1 : ℕ) * eta) *
      (2 * gaussianFirstMoment (n + 1) * Real.sqrt T) ≤ 1 / 2)
    (hus : ∀ t ∈ Icc 0 T, Differentiable ℝ (u t))
    (hu : ∀ t ∈ Icc 0 T, ∀ x,
      Tendsto (fun k => gaugePicard b G k t x) atTop (𝓝 (u t x)))
    (hgrad : ∀ t ∈ Icc 0 T,
      TendstoUniformly (fun k => fderiv ℝ (gaugePicard b G k t)) (fderiv ℝ (u t)) atTop)
    (htail : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G k t) x - fderiv ℝ (u t) x‖ ≤
        2 * eta * (1 / 2 : ℝ) ^ k)
    (hGend : ∀ e > 0, ∃ R : ℝ, ∀ s ∈ Icc 0 T, ∀ x z, R ≤ ‖x‖ → |z| ≤ eta →
      (1 + ‖x‖) * ‖forcingSpaceDeriv (G s) x z‖ < e) :
    (∃ H J : ℝ, 0 ≤ H ∧ 0 ≤ J ∧ ∀ t ∈ Icc 0 T, ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ H ∧
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u t))) x‖ ≤ J) ∧
    ∀ e > 0, ∃ R : ℝ, ∀ t ∈ Icc 0 T, ∀ x, R ≤ ‖x‖ →
      (1 + ‖x‖) * ‖fderiv ℝ (u t) x‖ < e ∧
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (u t)) x‖ < e := by
  have hunweight {s z D : ℝ} {x : V} (j : ℕ)
      (h : (1 + ‖x‖) *
        ‖iteratedFDeriv ℝ j (fun p : V × ℝ => G s p.1 p.2) (x, z)‖ ≤ D) :
      ‖iteratedFDeriv ℝ j (fun p : V × ℝ => G s p.1 p.2) (x, z)‖ ≤ D := by
    nlinarith only [h, mul_nonneg (norm_nonneg x)
      (norm_nonneg (iteratedFDeriv ℝ j (fun p : V × ℝ => G s p.1 p.2) (x, z)))]
  have hGb (j : ℕ) : ∃ D : ℝ, ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta →
      ‖iteratedFDeriv ℝ j (fun p : V × ℝ => G s p.1 p.2) (x, z)‖ ≤ D := by
    obtain ⟨D, _hD, hDb⟩ := hGw j
    exact ⟨D, fun s hs x z hz => hunweight j (hDb s hs x z hz)⟩
  have hc := gaugePicard_slab_control hT heta hB hL hC hbm hGm hbs hGs hbb hGb
    hb hGzero hGlip hsmall
  have hsource (k : ℕ) := (hc k).source hT hbm hGm hbs hGs hbb hGb
  have hsourceD (k : ℕ) (s : ℝ) (hs : s ∈ Ico 0 T) : ∃ D : ℝ, ∀ x : V,
      ‖fderiv ℝ (gaugeSource (b s) (G s) (gaugePicard b G k s)) x‖ ≤ D := by
    obtain ⟨D, hDb⟩ := (hsource k).2.2 1
    refine ⟨D, fun x => ?_⟩
    simpa only [norm_iteratedFDeriv_one] using (hDb s ⟨hs.1, hs.2.le⟩ x)
  have hstep := gaugePicard_slab_geometric heta hB hL hC hb hGzero hGlip
    (fun k => (hsource k).1)
    (fun k s hs => ((hsource k).2.1 s hs).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
    hsourceD
    (fun k => (hc k).weighted) (hcontract.trans (by norm_num))
  obtain ⟨D1, hD1b⟩ := hbb 1
  obtain ⟨D2, hD2b⟩ := hbb 2
  let B1 := max D1 0
  let B2 := max D2 0
  have hB1 : 0 ≤ B1 := le_max_right _ _
  have hB2 : 0 ≤ B2 := le_max_right _ _
  have hdb (s : ℝ) (hs : s ∈ Icc 0 T) (x : V) : ‖fderiv ℝ (b s) x‖ ≤ B1 := by
    simpa only [norm_iteratedFDeriv_one] using (hD1b s hs x).trans (le_max_left D1 0)
  have hddb (s : ℝ) (hs : s ∈ Icc 0 T) (x : V) :
      ‖fderiv ℝ (fderiv ℝ (b s)) x‖ ≤ B2 := by
    simpa only [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]
      using (hD2b s hs x).trans (le_max_left D2 0)
  obtain ⟨C1, hC1, hC1b⟩ := hGw 1
  obtain ⟨C2, hC2, hC2b⟩ := hGw 2
  have hGx (s : ℝ) (hs : s ∈ Icc 0 T) (x : V) (z : ℝ) (hz : |z| ≤ eta) :
      (1 + ‖x‖) * ‖forcingSpaceDeriv (G s) x z‖ ≤ C1 :=
    (mul_le_mul_of_nonneg_left (forcing_partial_norm_le (G s) x z).1
      (by positivity)).trans (hC1b s hs x z hz)
  have hGz (s : ℝ) (hs : s ∈ Icc 0 T) (x : V) (z : ℝ) (hz : |z| ≤ eta) :
      |forcingScalarDeriv (G s) x z| ≤ C1 :=
    (forcing_partial_norm_le (G s) x z).2.trans (hunweight 1 (hC1b s hs x z hz))
  have hquarter : (B + 2 * eta) * heatC1Gain (n + 1) T ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_right (by linarith only [hL])
      (heatC1Gain_nonneg hT)).trans hcontract
  let H := 2 * ((B1 + C1) * eta + C1) * heatC1Gain (n + 1) T
  have hH : 0 ≤ H := mul_nonneg (by positivity) (heatC1Gain_nonneg hT)
  have hHess := gaugePicard_weighted_hessian_bound hT heta hB hB1 hC1 hC1
    hc hbm hGm hbs hGs hbb hGb hb hdb hGx hGz (hquarter.trans (by norm_num))
  have hlip2 (s : ℝ) (hs : s ∈ Icc 0 T) (x : V) {a c : ℝ}
      (ha : |a| ≤ eta) (hz : |c| ≤ eta) :=
    forcing_derivatives_lipschitz_of_second_bound (hGs s hs)
      (fun y z hz => hunweight 2 (hC2b s hs y z hz)) x ha hz
  have hstep2 := gaugePicard_weighted_hessian_geometric hT heta hB hB1 hC1 hC1 hC2 hC2 hH
    hc hstep hHess hbm hGm hbs hGs hbb hGb hb hdb hGx hGz
    (fun s hs x _ _ ha hz => (hlip2 s hs x ha hz).1)
    (fun s hs x _ _ ha hz => (hlip2 s hs x ha hz).2) hquarter
  have hlimit2 := gaugePicard_limit_contDiff_two hus hgrad
    (fun k => (hc k).smooth) hstep2 hHess
  have hpartials (s : ℝ) (hs : s ∈ Icc 0 T) (x : V) (z : ℝ) :=
    forcing_second_partials_norm_le (hGs s hs) x z
  have hthird := gaugePicard_weighted_third_derivative_bound hT heta hB hB1 hB2
    hC1 hC2 hC2 hH hc hHess hbm hGm hbs hGs hbb hGb hb hdb hddb hGz
    (fun s hs x z hz => (mul_le_mul_of_nonneg_left (hpartials s hs x z).1
      (by positivity)).trans (hC2b s hs x z hz))
    (fun s hs x z hz => (hpartials s hs x z).2.1.trans (hunweight 2 (hC2b s hs x z hz)))
    (fun s hs x z hz => (hpartials s hs x z).2.2.1.trans
      (hunweight 2 (hC2b s hs x z hz)))
    (fun s hs x z hz => (hpartials s hs x z).2.2.2.trans
      (hunweight 2 (hC2b s hs x z hz))) (hquarter.trans (by norm_num))
  let J := 2 * ((2 * B1 + 2 * H + C1) * H + (B2 + 2 * C2 + C2 * eta) * eta + C2) *
    heatC1Gain (n + 1) T
  have hJ : 0 ≤ J := mul_nonneg (by positivity) (heatC1Gain_nonneg hT)
  have hfull := gaugePicard_uniform_all_order_bounds hT heta hB hc hbm hGm hbs hGs
    hbb hGb hb hhigh
  choose D _hD hDb using hfull
  have hlimit3 (t : ℝ) (ht : t ∈ Icc 0 T) (x : V) :
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u t))) x‖ ≤ J := by
    have h := smooth_limit_preserves_weighted_jet_bound 3
      (fun k => (hc k).smooth t ht) (fun j k y => hDb j k t ht y) (hu t ht)
      (w := fun y => 1 + ‖y‖) (J := J) (fun k y => by
        simpa only [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]
          using hthird k t ht y) x
    simpa only [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] using h
  have hstrip {x : V} {z : ℝ} (hz : (1 + ‖x‖) * |z| ≤ eta) : |z| ≤ eta := by
    nlinarith only [hz, mul_nonneg (norm_nonneg x) (abs_nonneg z)]
  have hfiniteEnd := gaugePicard_derivatives_weighted_vanish_uniformly
    hT heta hB hB1 hC1 hC1 hH hc hHess hbm hGm hbs hGs hbb hGb hb hdb
    (fun s hs x z hz => hGx s hs x z (hstrip hz))
    (fun s hs x z hz => hGz s hs x z (hstrip hz))
    (fun e he => by
      obtain ⟨R, hR⟩ := hGend e he
      exact ⟨R, fun s hs x z hx hz => hR s hs x z hx (hstrip hz)⟩)
  refine ⟨⟨H, J, hH, hJ, fun t ht x => ⟨(hlimit2 t ht).2.2.1 x, hlimit3 t ht x⟩⟩, ?_⟩
  exact gaugePicard_limit_derivatives_weighted_vanish_uniformly htail
    (fun k t ht => (hlimit2 t ht).2.2.2 k) hfiniteEnd

end PoincareConjecture.M35.RadialGauge
