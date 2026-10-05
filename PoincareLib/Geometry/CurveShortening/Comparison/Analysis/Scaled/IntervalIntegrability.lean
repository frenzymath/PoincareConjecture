import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Integrability on physical cells from actual scaled coordinates,
and finite assembly over adjacent closed cells. Source: MT Lemma 19.15,
pp. 447-449; `2026-09-26-periodic-finite-collar.md`. -/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory

namespace PoincareMT.M64

/-- A continuous integrand in a positive affine coordinate gives
the original integrand's interval integrability on the physical cell.
Source: MT Lemma 19.15, pp. 447-449; the periodic-finite-collar derivation. -/
theorem intervalIntegrable_of_scaled_coordinates {a b r x : ℝ} (hab : a ≤ b) (hr : 0 < r)
    {f F : ℝ → ℝ}
    (hf : ContinuousOn f (Icc ((a - x) / r) ((b - x) / r)))
    (heq : ∀ t ∈ Icc ((a - x) / r) ((b - x) / r), f t = F (x + r * t)) :
    IntervalIntegrable F volume a b := by
  have hmap : MapsTo (fun s => (s - x) / r) (Icc a b)
      (Icc ((a - x) / r) ((b - x) / r)) := by
    intro s hs
    exact ⟨div_le_div_of_nonneg_right (sub_le_sub_right hs.1 x) hr.le,
      div_le_div_of_nonneg_right (sub_le_sub_right hs.2 x) hr.le⟩
  have hc : ContinuousOn F (Icc a b) := by
    have hpsi : Continuous (fun s : ℝ => (s - x) / r) :=
      (continuous_id.sub continuous_const).div_const r
    apply (hf.comp hpsi.continuousOn hmap).congr
    intro s hs
    have hh := heq ((s - x) / r) (hmap hs)
    simpa only [Function.comp_apply, mul_div_cancel₀ _ hr.ne', add_sub_cancel] using hh.symm
  exact hc.intervalIntegrable_of_Icc hab

/-- Integrability on every actual adjacent grid cell gives
integrability on the whole displayed interval.
Source: MT Lemma 19.15, pp. 447-449; the periodic-finite-collar derivation. -/
theorem intervalIntegrable_of_grid {N : ℕ} (v : ℕ → ℝ) (f : ℝ → ℝ)
    (hf : ∀ k < N, IntervalIntegrable f volume (v k) (v (k + 1))) :
    IntervalIntegrable f volume (v 0) (v N) := by
  induction N with
  | zero => exact IntervalIntegrable.refl
  | succ N ih =>
    exact (ih (fun k hk => hf k (Nat.lt_succ_of_lt hk))).trans (hf N (Nat.lt_succ_self N))

end PoincareMT.M64
