import PoincareConjecture.Proofs.M47.CanonicalNeckUniformTimeComparison

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.Proofs.M47

theorem normalized_neck_clock_distance_le (t t0 Q Q0 : ℝ)
    {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 0) :
    |t + u / Q - (t0 + u / Q0)| ≤ |t - t0| + |Q⁻¹ - Q0⁻¹| := by
  have hidentity : t + u / Q - (t0 + u / Q0) =
      (t - t0) + u * (Q⁻¹ - Q0⁻¹) := by
    simp only [div_eq_mul_inv]
    ring
  have huabs : |u| ≤ 1 := abs_le.mpr ⟨hu.1, hu.2.trans zero_le_one⟩
  rw [hidentity]
  calc
    _ ≤ |t - t0| + |u * (Q⁻¹ - Q0⁻¹)| := abs_add_le _ _
    _ = |t - t0| + |u| * |Q⁻¹ - Q0⁻¹| := by rw [abs_mul]
    _ ≤ |t - t0| + 1 * |Q⁻¹ - Q0⁻¹| :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right huabs (abs_nonneg _))
    _ = _ := by rw [one_mul]

theorem eventually_normalized_neck_clock_in_buffer
    {X : Type*} [TopologicalSpace X] {T R : X → ℝ} {p0 : X}
    (hT : ContinuousAt T p0) (hR : ContinuousAt R p0) (hR0 : 0 < R p0)
    {a b eta : ℝ} (hbottom : a < T p0 - (R p0)⁻¹) (htop : T p0 < b)
    (heta : 0 < eta) :
    ∀ᶠ p in 𝓝 p0, 0 < R p ∧ ∀ u ∈ Icc (-1 : ℝ) 0,
      T p + u / R p ∈ Ioo a b ∧
        |T p + u / R p - (T p0 + u / R p0)| < eta := by
  have hinv : ContinuousAt (fun p => (R p)⁻¹) p0 := hR.inv₀ hR0.ne'
  have herror : ContinuousAt
      (fun p => |T p - T p0| + |(R p)⁻¹ - (R p0)⁻¹|) p0 :=
    (hT.sub continuousAt_const).abs.add (hinv.sub continuousAt_const).abs
  have hsmall : ∀ᶠ p in 𝓝 p0,
      |T p - T p0| + |(R p)⁻¹ - (R p0)⁻¹| < eta :=
    herror.eventually (Iio_mem_nhds (by simpa only [sub_self, abs_zero, zero_add] using heta))
  filter_upwards [hR.eventually (Ioi_mem_nhds hR0),
    (hT.sub hinv).eventually (Ioi_mem_nhds hbottom),
    hT.eventually (Iio_mem_nhds htop), hsmall] with p hp hleft hright hclose
  refine ⟨hp, ?_⟩
  intro u hu
  have hpositive : 0 ≤ (R p)⁻¹ := (inv_pos.mpr hp).le
  have hlower : T p - (R p)⁻¹ ≤ T p + u / R p := by
    have h := mul_le_mul_of_nonneg_right hu.1 hpositive
    rw [div_eq_mul_inv]
    linarith
  have hupper : T p + u / R p ≤ T p := by
    have h := mul_nonpos_of_nonpos_of_nonneg hu.2 hpositive
    rw [div_eq_mul_inv]
    linarith
  exact ⟨⟨hleft.trans_le hlower, hupper.trans_lt hright⟩,
    (normalized_neck_clock_distance_le (T p) (T p0) (R p) (R p0) hu).trans_lt hclose⟩

end PoincareConjecture.Proofs.M47
