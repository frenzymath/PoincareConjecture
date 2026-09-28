import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith











set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Real





theorem exists_strict_scalar_radius_subsequence
    (R : ℝ → ℝ) {eta c B : ℝ} (heta : 0 < eta) (hc : 0 < c)
    (hbound : ∀ t ∈ Ioo (0 : ℝ) eta, c < R t * t ^ 2 ∧ R t * t ^ 2 ≤ B) :
    ∃ rho ∈ Icc c B, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      let d : ℕ → ℝ := fun i => eta / ((phi i : ℝ) + 2)
      (∀ i : ℕ, d i ∈ Ioo (0 : ℝ) eta ∧ 0 < R (d i) ∧
        c < R (d i) * d i ^ 2 ∧ R (d i) * d i ^ 2 ≤ B) ∧
      Tendsto d atTop (𝓝[>] (0 : ℝ)) ∧
      Tendsto (fun i => R (d i)) atTop atTop ∧
      Tendsto (fun i => R (d i) * d i ^ 2) atTop (𝓝 rho) ∧
      Tendsto (fun i => Real.sqrt (R (d i)) * d i) atTop (𝓝 (Real.sqrt rho)) ∧
      Tendsto (fun i => 1 / Real.sqrt (R (d i))) atTop (𝓝[>] (0 : ℝ)) := by
  let t : ℕ → ℝ := fun n => eta / ((n : ℝ) + 2)
  have ht (n : ℕ) : t n ∈ Ioo (0 : ℝ) eta := by
    have hden : 1 < (n : ℝ) + 2 := by
      linarith only [Nat.cast_nonneg (α := ℝ) n]
    exact ⟨div_pos heta (zero_lt_one.trans hden), div_lt_self heta hden⟩
  have hRpositive (n : ℕ) : 0 < R (t n) :=
    (mul_pos_iff_of_pos_right (sq_pos_of_pos (ht n).1)).mp
      (hc.trans (hbound (t n) (ht n)).1)
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      ((tendsto_add_atTop_iff_nat 2).2
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have htzero : Tendsto t atTop (𝓝 (0 : ℝ)) := by
    simpa only [t, mul_one_div, mul_zero] using
      (tendsto_const_nhds (x := eta)).mul hinv
  have htpositive : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨htzero, Eventually.of_forall fun n => (ht n).1⟩
  have hsqpositive : Tendsto (fun n => t n ^ 2) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun n => sq_pos_of_pos (ht n).1⟩
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using htzero.pow 2
  have hlower : Tendsto (fun n => c * (t n ^ 2)⁻¹) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).mpr (tendsto_inv_nhdsGT_zero.comp hsqpositive)
  have hRdiverge : Tendsto (fun n => R (t n)) atTop atTop := by
    apply tendsto_atTop_mono (f := fun n => c * (t n ^ 2)⁻¹) _ hlower
    intro n
    have hh := (div_le_iff₀ (sq_pos_of_pos (ht n).1)).mpr (hbound (t n) (ht n)).1.le
    simpa only [div_eq_mul_inv] using hh
  have hclock : Tendsto (fun n => 1 / Real.sqrt (R (t n))) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hh := Real.continuous_sqrt.continuousAt.tendsto.comp
        (tendsto_inv_atTop_zero.comp hRdiverge)
      simpa only [Function.comp_def, Real.sqrt_inv, Real.sqrt_zero, one_div] using hh
    · exact Eventually.of_forall fun n =>
        one_div_pos.mpr (Real.sqrt_pos.mpr (hRpositive n))
  let b : ℕ → ℝ := fun n => R (t n) * t n ^ 2
  have hb (n : ℕ) : b n ∈ Icc c B :=
    ⟨(hbound (t n) (ht n)).1.le, (hbound (t n) (ht n)).2⟩
  obtain ⟨rho, hrho, phi, hphi, hproduct⟩ := isCompact_Icc.tendsto_subseq hb
  have hnormalized : Tendsto (fun i => Real.sqrt (R (t (phi i))) * t (phi i))
      atTop (𝓝 (Real.sqrt rho)) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hproduct
    apply hh.congr'
    apply Eventually.of_forall
    intro i
    change Real.sqrt (R (t (phi i)) * t (phi i) ^ 2) = _
    rw [Real.sqrt_mul (hRpositive (phi i)).le, Real.sqrt_sq (ht (phi i)).1.le]
  exact ⟨rho, hrho, phi, hphi,
    fun i => ⟨ht (phi i), hRpositive (phi i), hbound (t (phi i)) (ht (phi i))⟩,
    htpositive.comp hphi.tendsto_atTop, hRdiverge.comp hphi.tendsto_atTop,
    hproduct, hnormalized, hclock.comp hphi.tendsto_atTop⟩

end Real
