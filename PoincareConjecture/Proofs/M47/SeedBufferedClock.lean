import PoincareConjecture.Proofs.M47.SeedBlowupVolumeScales








set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.Proofs.M47



theorem seed_blowup_eventually_clock_in_buffer
    (t Q : ℕ → ℝ) {a w T : ℝ} (hw : 0 < w) (_hT : 0 ≤ T)
    (ht : ∀ n, a ≤ t n) (hQ : Tendsto Q atTop atTop) :
    ∀ᶠ n in atTop, 0 < Q n ∧ ∀ s ∈ Icc (-T) 0,
      t n + s / Q n ∈ Icc (a - w) (t n) := by
  filter_upwards [hQ.eventually (eventually_ge_atTop (max 1 (T / w)))] with n hn
  have hpositive : 0 < Q n := zero_lt_one.trans_le ((le_max_left _ _).trans hn)
  have htime : T ≤ w * Q n := by
    have h := (div_le_iff₀ hw).mp ((le_max_right _ _).trans hn)
    simpa only [mul_comm] using h
  refine ⟨hpositive, ?_⟩
  intro s hs
  have hlower : -w ≤ s / Q n := (le_div_iff₀ hpositive).mpr (by
    nlinarith only [htime, hs.1])
  have hupper : s / Q n ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hpositive.le
  constructor <;> linarith only [hlower, hupper, ht n]

end PoincareConjecture.Proofs.M47
