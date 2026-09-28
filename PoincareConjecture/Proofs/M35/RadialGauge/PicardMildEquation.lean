import PoincareConjecture.Proofs.M35.RadialGauge.PicardConvergence
import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem gaugeSource_tendsto_of_c1 {b : V → V} {G : V → ℝ → ℝ}
    {u : ℕ → V → ℝ} {v : V → ℝ} {eta L : ℝ}
    (hG : ∀ x a c, |a| ≤ eta → |c| ≤ eta → |G x a - G x c| ≤ L * |a - c|)
    (hu : ∀ k x, |u k x| ≤ eta) (hv : ∀ x, |v x| ≤ eta)
    (hul : ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (v x)))
    (hdl : ∀ x, Tendsto (fun k => fderiv ℝ (u k) x) atTop (𝓝 (fderiv ℝ v x)))
    (x : V) :
    Tendsto (fun k => gaugeSource b G (u k) x) atTop (𝓝 (gaugeSource b G v x)) := by
  have hforcing : Tendsto (fun k => G x (u k x)) atTop (𝓝 (G x (v x))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hz : Tendsto (fun k => L * |u k x - v x|) atTop (𝓝 0) := by
      simpa using (((hul x).sub_const (v x)).abs.const_mul L)
    simpa only [Real.dist_eq] using squeeze_zero (fun k => abs_nonneg _)
      (fun k => hG x (u k x) (v x) (hu k x) (hv x)) hz
  have heval : Tendsto (fun k => (fderiv ℝ (u k) x) (b x)) atTop
      (𝓝 ((fderiv ℝ v x) (b x))) := by
    exact (ContinuousLinearMap.apply ℝ ℝ (b x)).continuous.continuousAt.tendsto.comp (hdl x)
  exact (heval.add ((hdl x).norm.pow 2)).add hforcing

theorem gaugePicard_limit_mild_equation
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u : ℝ → V → ℝ}
    {eta B L C T : ℝ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hb : ∀ s ∈ Icc 0 T, ∀ x, ‖b s x‖ ≤ B)
    (hGzero : ∀ s ∈ Icc 0 T, ∀ x, (1 + ‖x‖) * |G s x 0| ≤ C)
    (hGlip : ∀ s ∈ Icc 0 T, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      |G s x a - G s x c| ≤ L * |a - c|)
    (hm : ∀ k, StronglyMeasurable (fun p : Icc (0 : ℝ) T × V =>
      gaugeSource (b p.1) (G p.1) (gaugePicard b G k p.1) p.2))
    (hr : ∀ k s, s ∈ Icc 0 T → Continuous (gaugeSource (b s) (G s) (gaugePicard b G k s)))
    (hball : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖gaugePicard b G k t x‖ ≤ eta ∧
      (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G k t) x‖ ≤ eta)
    (hu : ∀ t, t ∈ Icc 0 T → ∀ x,
      Tendsto (fun k => gaugePicard b G k t x) atTop (𝓝 (u t x)))
    (hdu : ∀ t, t ∈ Icc 0 T → ∀ x,
      Tendsto (fun k => fderiv ℝ (gaugePicard b G k t) x) atTop (𝓝 (fderiv ℝ (u t) x))) :
    ∀ t, t ∈ Icc 0 T → ∀ x, u t x = gaugeDuhamel b G u t x := by
  have hvalues (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (x : V) :
      |gaugePicard b G k t x| ≤ eta := by
    have h := (hball k t ht x).1
    rw [Real.norm_eq_abs] at h
    nlinarith [mul_nonneg (norm_nonneg x) (abs_nonneg (gaugePicard b G k t x))]
  have hlimit (t : ℝ) (ht : t ∈ Icc 0 T) (x : V) : |u t x| ≤ eta :=
    le_of_tendsto (hu t ht x).abs (Eventually.of_forall (fun k => hvalues k t ht x))
  have hsrc (k : ℕ) (s : ℝ) (hs : s ∈ Icc 0 T) (x : V) :
      ‖gaugeSource (b s) (G s) (gaugePicard b G k s) x‖ ≤
        B * eta + eta ^ 2 + L * eta + C := by
    have h := gaugeSource_weighted_bound heta hB hL hb hGzero hGlip
      (fun t ht y => by simpa only [Real.norm_eq_abs] using (hball k t ht y).1)
      (fun t ht y => (hball k t ht y).2) s hs x
    nlinarith [mul_nonneg (norm_nonneg x)
      (norm_nonneg (gaugeSource (b s) (G s) (gaugePicard b G k s) x))]
  intro t ht x
  have hlim := heatDuhamel_tendsto_on_slab ht hm hr hsrc
    (fun s hs y => gaugeSource_tendsto_of_c1 (hGlip s hs)
      (fun k => hvalues k s hs) (hlimit s hs) (hu s hs) (hdu s hs) y) x
  have hsucc := (hu t ht x).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hsucc hlim

end PoincareConjecture.M35.RadialGauge
