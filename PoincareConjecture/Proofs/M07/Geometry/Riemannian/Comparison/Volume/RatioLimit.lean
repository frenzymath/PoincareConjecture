import Mathlib.Topology.Instances.ENNReal.Lemmas









set_option autoImplicit false

open Filter
open scoped ENNReal NNReal Topology

namespace Poincare.VolumeComparison



theorem tendsto_div_one_of_eventually_bounds
    {X : Type*} {l : Filter X} {a b : X → ℝ≥0∞} (m : ℕ)
    (hb : ∀ᶠ x in l, b x ≠ 0 ∧ b x ≠ ⊤)
    (h : ∀ K : ℝ≥0, 1 < K → ∀ᶠ x in l,
      a x ≤ (K : ℝ≥0∞) ^ m * b x ∧
        b x ≤ (K : ℝ≥0∞) ^ m * a x) :
    Tendsto (fun x => a x / b x) l (𝓝 1) := by
  have hpow : Tendsto (fun K : ℝ≥0 => (K : ℝ≥0∞) ^ m)
      (𝓝[>] 1) (𝓝 1) := by
    simpa using ENNReal.Tendsto.pow (n := m)
      (ENNReal.continuous_coe.continuousAt.mono_left
        (show 𝓝[>] (1 : ℝ≥0) ≤ 𝓝 1 from nhdsWithin_le_nhds))
  have hinv : Tendsto (fun K : ℝ≥0 => ((K : ℝ≥0∞) ^ m)⁻¹)
      (𝓝[>] 1) (𝓝 1) := by
    simpa using hpow.inv
  have hright : ∀ᶠ K : ℝ≥0 in 𝓝[>] 1, 1 < K := self_mem_nhdsWithin
  apply tendsto_order.mpr
  constructor
  · intro c hc
    obtain ⟨K, hK, hcK⟩ :=
      (hright.and (hinv.eventually (lt_mem_nhds hc))).exists
    filter_upwards [hb, h K hK] with x hx hxab
    apply hcK.trans_le
    have hK0 : (K : ℝ≥0∞) ^ m ≠ 0 := by
      exact pow_ne_zero _ (by exact_mod_cast (zero_lt_one.trans hK).ne')
    have hKtop : (K : ℝ≥0∞) ^ m ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
    have hdivide := (ENNReal.div_le_iff' hK0 hKtop).mpr hxab.2
    have hdivide' := mul_le_mul' hdivide (le_refl (b x)⁻¹)
    rw [div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel hx.1 hx.2,
      one_mul, ← div_eq_mul_inv] at hdivide'
    exact hdivide'
  · intro c hc
    obtain ⟨K, hK, hKc⟩ :=
      (hright.and (hpow.eventually (gt_mem_nhds hc))).exists
    filter_upwards [hb, h K hK] with x hx hxab
    exact ((ENNReal.div_le_iff hx.1 hx.2).mpr hxab.1).trans_lt hKc

end Poincare.VolumeComparison
