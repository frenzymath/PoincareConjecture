import PoincareConjecture.Proofs.M35.RadialGauge.RadiusInverseEnd











set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

private theorem weighted_value_tendsto_zero
    {A : Type*} {l : Filter A} {r : A → ℝ} {v : A → ℝ → ℝ} {C : ℝ}
    (hr : Tendsto r l atTop)
    (hb : ∀ a s, 0 ≤ s → (1 + s) * |v a s| ≤ C) :
    Tendsto (fun a => v a (r a)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  filter_upwards [(tendsto_atTop.1 hr) (max 0 ((|C| + 1) / epsilon))] with a ha
  have hra : 0 ≤ r a := (le_max_left _ _).trans ha
  have hlarge := (div_le_iff₀ hepsilon).mp ((le_max_right _ _).trans ha)
  have hbound := hb a (r a) hra
  have hweight : 0 ≤ 1 + r a := by linarith only [hra]
  have hv : |v a (r a)| < epsilon := by
    by_contra h
    have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt h) hweight
    nlinarith only [hmul, hlarge, hbound, hepsilon, le_abs_self C]
  simpa only [Real.dist_eq, sub_zero] using hv

private theorem weighted_littleO_tendsto_zero
    {A : Type*} {l : Filter A} {r : A → ℝ} {v : A → ℝ → ℝ}
    (hr : Tendsto r l atTop)
    (hend : ∀ epsilon > 0, ∃ R : ℝ, ∀ a s, R ≤ s →
      (1 + s) * |v a s| ≤ epsilon) :
    Tendsto (fun a => v a (r a)) l (𝓝 0) ∧
      Tendsto (fun a => r a * v a (r a)) l (𝓝 0) := by
  have hsmall : ∀ epsilon > 0, ∀ᶠ a in l,
      |v a (r a)| < epsilon ∧ |r a * v a (r a)| < epsilon := by
    intro epsilon hepsilon
    obtain ⟨R, hR⟩ := hend (epsilon / 2) (by linarith only [hepsilon])
    filter_upwards [(tendsto_atTop.1 hr) (max 0 R)] with a ha
    have hra := (le_max_left 0 R).trans ha
    have hb := hR a (r a) ((le_max_right 0 R).trans ha)
    have hv := mul_nonneg hra (abs_nonneg (v a (r a)))
    have hs := abs_nonneg (v a (r a))
    constructor
    · nlinarith only [hb, hv, hepsilon]
    · rw [abs_mul, abs_of_nonneg hra]
      nlinarith only [hb, hs, hepsilon]
  constructor
  · apply Metric.tendsto_nhds.2
    intro epsilon hepsilon
    filter_upwards [hsmall epsilon hepsilon] with a ha
    simpa only [Real.dist_eq, sub_zero] using ha.1
  · apply Metric.tendsto_nhds.2
    intro epsilon hepsilon
    filter_upwards [hsmall epsilon hepsilon] with a ha
    simpa only [Real.dist_eq, sub_zero] using ha.2



theorem mapRadius_end_of_uniform_weighted
    {A : Type*} {l : Filter A} {r : A → ℝ} {u : A → ℝ → ℝ} {C : ℝ}
    (hs : ∀ a, ContDiff ℝ ∞ (u a)) (hr : Tendsto r l atTop)
    (hv : ∀ a s, 0 ≤ s → (1 + s) * |u a s| ≤ C)
    (hd1 : ∀ epsilon > 0, ∃ R : ℝ, ∀ a s, R ≤ s →
      (1 + s) * |deriv (u a) s| ≤ epsilon)
    (hd2 : ∀ epsilon > 0, ∃ R : ℝ, ∀ a s, R ≤ s →
      (1 + s) * |deriv (deriv (u a)) s| ≤ epsilon) :
    Tendsto (fun a => mapRadius (u a) (r a) / r a) l (𝓝 1) ∧
      Tendsto (fun a => deriv (mapRadius (u a)) (r a)) l (𝓝 1) ∧
      Tendsto (fun a => deriv (deriv (mapRadius (u a))) (r a)) l (𝓝 0) := by
  have hvalue := weighted_value_tendsto_zero hr hv
  have hfirst := weighted_littleO_tendsto_zero hr hd1
  have hsecond := weighted_littleO_tendsto_zero hr hd2
  refine ⟨mapRadius_ratio_tendsto ?_ hvalue,
    mapRadius_deriv_tendsto hs hvalue hfirst.2,
    mapRadius_second_deriv_tendsto hs hvalue hfirst.1 hfirst.2 hsecond.2⟩
  filter_upwards [(tendsto_atTop.1 hr) 1] with a ha
  linarith only [ha]



theorem inverse_mapRadius_end_of_uniform_weighted
    {A : Type*} {l : Filter A} {z : A → ℝ} {u q : A → ℝ → ℝ} {eta : ℝ}
    (hs : ∀ a, ContDiff ℝ ∞ (u a)) (heta : eta ≤ 1)
    (hz : Tendsto z l atTop)
    (hv : ∀ a s, (1 + |s|) * |u a s| ≤ eta)
    (hinv : ∀ a s, mapRadius (u a) (q a s) = s)
    (hd1 : ∀ epsilon > 0, ∃ R : ℝ, ∀ a s, R ≤ s →
      (1 + s) * |deriv (u a) s| ≤ epsilon)
    (hd2 : ∀ epsilon > 0, ∃ R : ℝ, ∀ a s, R ≤ s →
      (1 + s) * |deriv (deriv (u a)) s| ≤ epsilon) :
    Tendsto (fun a => deriv (mapRadius (u a)) (q a (z a))) l (𝓝 1) ∧
      Tendsto (fun a => deriv (deriv (mapRadius (u a))) (q a (z a))) l (𝓝 0) := by
  have hr := inverse_mapRadius_tendsto_atTop heta hv hinv hz
  exact (mapRadius_end_of_uniform_weighted hs hr
    (fun a s hs' => by simpa only [abs_of_nonneg hs'] using hv a s) hd1 hd2).2

end PoincareConjecture.M35.RadialGauge
