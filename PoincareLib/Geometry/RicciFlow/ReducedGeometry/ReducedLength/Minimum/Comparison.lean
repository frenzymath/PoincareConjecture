import Mathlib.Analysis.Calculus.MeanValue

/-!
# Comparison for a reduced-length minimum

The real-variable argument for Morgan--Tian, Theorem 7.10 and Claim 7.11,
pp. 154--156, applies once continuity, the initial bound, and local upper
barriers have been obtained from the reduced-length variational problem.
This file proves the comparison argument, without asserting those geometric
inputs.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareMT.ReducedLengthMinimum

/-- Arbitrarily accurate differentiable upper barriers bound the right-hand
lower limit of difference quotients. Only upper barriers to the right of the
contact point are needed. -/
theorem frequently_slope_lt_of_upper_barriers {f : ℝ → ℝ} {x a : ℝ}
    (hbarrier : ∀ ε > 0, ∃ (b : ℝ → ℝ) (d : ℝ),
      b x = f x ∧ HasDerivAt b d x ∧
      (∀ᶠ y in 𝓝[>] x, f y ≤ b y) ∧ d ≤ a + ε)
    {r : ℝ} (hr : a < r) : ∃ᶠ y in 𝓝[>] x, slope f x y < r := by
  obtain ⟨b, d, hbx, hbd, hupper, hd⟩ := hbarrier ((r - a) / 2) (by linarith)
  have hdr : d < r := by linarith
  have hfreq : ∃ᶠ y in 𝓝[>] x, slope b x y < r :=
    hbd.hasDerivWithinAt.liminf_right_slope_le hdr
  refine (hfreq.and_eventually (hupper.and self_mem_nhdsWithin)).mono ?_
  intro y hy
  apply lt_of_le_of_lt _ hy.1
  rw [slope_def_field, slope_def_field, hbx]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hy.2.1 _) (le_of_lt (sub_pos.mpr hy.2.2))

/-- If a continuous function on positive times has initial upper limit at most
`c`, and arbitrarily accurate local upper barriers with derivative at most
`(c - m t) / t`, then it stays at most `c`.

The initial condition is stated using eventual upper bounds, so no value or
continuity of `m` at time zero is required. -/
theorem le_of_approximate_upper_barriers {m : ℝ → ℝ} {c : ℝ}
    (hcont : ContinuousOn m (Ioi 0))
    (hinitial : ∀ ε > 0, ∀ᶠ t in 𝓝[>] (0 : ℝ), m t ≤ c + ε)
    (hbarrier : ∀ t > 0, ∀ ε > 0, ∃ (b : ℝ → ℝ) (d : ℝ),
      b t = m t ∧ HasDerivAt b d t ∧
      (∀ᶠ s in 𝓝[>] t, m s ≤ b s) ∧ d ≤ (c - m t) / t + ε)
    {T : ℝ} (hT : 0 < T) : m T ≤ c := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, hma, ha⟩ := ((hinitial ε hε).and (Ioo_mem_nhdsGT hT)).exists
  have hcont' : ContinuousOn m (Icc a T) :=
    hcont.mono fun t ht => lt_of_lt_of_le ha.1 ht.1
  have hslope : ∀ t ∈ Ico a T, ∀ r, (c - m t) / t < r →
      ∃ᶠ s in 𝓝[>] t, slope m t s < r := by
    intro t ht r hr
    exact frequently_slope_lt_of_upper_barriers
      (hbarrier t (lt_of_lt_of_le ha.1 ht.1)) hr
  apply image_le_of_liminf_slope_right_lt_deriv_boundary hcont' hslope hma
    (fun t => hasDerivAt_const t (c + ε)) ?_ ⟨ha.2.le, le_rfl⟩
  intro t ht hmt
  have htpos : 0 < t := lt_of_lt_of_le ha.1 ht.1
  apply div_neg_of_neg_of_pos _ htpos
  change m t = c + ε at hmt
  linarith

/-- A right-continuous initial value bounded by `c` supplies the initial
condition in the minimum comparison theorem. -/
theorem le_of_approximate_upper_barriers_of_continuousWithinAt
    {m : ℝ → ℝ} {c : ℝ}
    (hcont : ContinuousOn m (Ioi 0))
    (hzero : ContinuousWithinAt m (Ioi 0) 0) (hmzero : m 0 ≤ c)
    (hbarrier : ∀ t > 0, ∀ ε > 0, ∃ (b : ℝ → ℝ) (d : ℝ),
      b t = m t ∧ HasDerivAt b d t ∧
      (∀ᶠ s in 𝓝[>] t, m s ≤ b s) ∧ d ≤ (c - m t) / t + ε)
    {T : ℝ} (hT : 0 < T) : m T ≤ c := by
  apply le_of_approximate_upper_barriers hcont _ hbarrier hT
  intro ε hε
  have hbound : m 0 < c + ε := lt_of_le_of_lt hmzero (lt_add_of_pos_right c hε)
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ), m t < c + ε := hzero (Iio_mem_nhds hbound)
  exact hevent.mono fun _ h => le_of_lt h

end PoincareMT.ReducedLengthMinimum
