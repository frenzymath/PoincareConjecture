import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcLengthPartition

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture

theorem m64Intrinsic_total_turning_lt
    (N : IntrinsicAnnulus) {delta r : ℝ} (hdelta : 0 < delta) (hr : 0 < r)
    (hfirst : r < intrinsicBoundaryLength N.metric 1 0 rampPeriod)
    (hturn : N.SmallBoundaryTurning delta r) :
    intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 0 rampPeriod <
      (2 * delta / r) * intrinsicBoundaryLength N.metric 1 0 rampPeriod := by
  let L := intrinsicBoundaryLength N.metric 1 0 rampPeriod
  have hL : 0 < L := hr.trans hfirst
  have hratio : 1 < L / r := (one_lt_div hr).mpr hfirst
  let n := Nat.ceil (L / r)
  have hn : 0 < n := Nat.ceil_pos.mpr (div_pos hL hr)
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnUpper : (n : ℝ) < 2 * (L / r) := by
    have hceil := Nat.ceil_lt_add_one (div_pos hL hr).le
    change (n : ℝ) < L / r + 1 at hceil
    linarith
  have hLn : L / n ≤ r := by
    apply (div_le_iff₀ hnReal).mpr
    have hceil := Nat.le_ceil (L / r)
    change L / r ≤ (n : ℝ) at hceil
    have hmul := (div_le_iff₀ hr).mp hceil
    linarith
  obtain ⟨p, hp0, hpn, hp, hcell⟩ :=
    m64Intrinsic_exists_equal_boundary_length_partition N (by norm_num : (1 : ℝ) ≠ 0) hn
  have hcellTurn (k : ℕ) (hk : k < n) :
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 (p k) (p (k + 1)) <
        delta := by
    apply hturn (p k) (p (k + 1)) (hcell k hk).1.le
    · have ha := (hp k hk.le).1
      have hb := (hp (k + 1) (Nat.add_one_le_iff.mpr hk)).2
      linarith
    · rw [(hcell k hk).2]
      exact hLn
  have hsum := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hn.ne')
    (fun k hk => hcellTurn k (Finset.mem_range.mp hk))
  have hsumEq := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (a := p) (n := n)
    (fun k _ => (m64Intrinsic_continuous_turning_density N
      (by norm_num : (1 : ℝ) ≠ 0)).intervalIntegrable (p k) (p (k + 1)))
  change (∑ k ∈ Finset.range n,
    intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 (p k) (p (k + 1))) =
    intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 (p 0) (p n) at hsumEq
  rw [hsumEq, hp0, hpn] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hcount := mul_lt_mul_of_pos_right hnUpper hdelta
  apply hsum.trans
  convert hcount using 1
  ring

end PoincareConjecture
