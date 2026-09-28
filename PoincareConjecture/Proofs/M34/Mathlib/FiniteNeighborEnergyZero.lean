import PoincareConjecture.Proofs.M34.Mathlib.FiniteNeighborEnergy
import PoincareConjecture.Proofs.M34.Mathlib.InteriorGronwall
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set Filter
open scoped Topology BigOperators

theorem eq_zero_of_uniformly_bounded_neighbor_energy_rates
    {E : ℕ → ℝ → ℝ} {a b C M : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i, ContinuousOn (E i) (Icc a b))
    (hd : ∀ i t, t ∈ Ioo a b → DifferentiableAt ℝ (E i) t)
    (hzero : ∀ i, E i a = 0)
    (hn : ∀ i t, t ∈ Icc a b → 0 ≤ E i t)
    (hb : ∀ i t, t ∈ Icc a b → E i t ≤ M)
    (hr0 : ∀ t ∈ Ioo a b, deriv (E 0) t ≤ C * (E 0 t + E 1 t + E 2 t))
    (hr1 : ∀ t ∈ Ioo a b, deriv (E 1) t ≤ C * (E 0 t + E 1 t + E 2 t))
    (hrn : ∀ n t, t ∈ Ioo a b →
      deriv (E (n + 2)) t ≤ C * (E (n + 1) t + E (n + 2) t + E (n + 3) t)) :
    ∀ i, EqOn (E i) (fun _ => 0) (Icc a b) := by
  let F : ℕ → ℝ → ℝ := fun k t =>
    ∑ i ∈ Finset.range (k + 3), (1 / 2 : ℝ) ^ i * E i t
  have hFc (k) : ContinuousOn (F k) (Icc a b) :=
    continuousOn_finsetSum _ (fun i _ => continuousOn_const.mul (hc i))
  have hFd (k) (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (F k) (∑ i ∈ Finset.range (k + 3), (1 / 2 : ℝ) ^ i * deriv (E i) t) t :=
    HasDerivAt.fun_sum (fun i _ => (hd i t ht).hasDerivAt.const_mul ((1 / 2 : ℝ) ^ i))
  have hF0 (k) : F k a = 0 := by simp only [F, hzero, mul_zero, Finset.sum_const_zero]
  have hFr (k) (t : ℝ) (ht : t ∈ Ioo a b) :
      deriv (F k) t ≤ 8 * C * F k t + 2 * C * M * (1 / 2 : ℝ) ^ (k + 3) := by
    rw [(hFd k t ht).deriv]
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    calc
      _ ≤ 8 * C * F k t + 2 * C * ((1 / 2 : ℝ) ^ (k + 3) * E (k + 3) t) :=
        geometric_weighted_neighbor_sum_range_le (fun i => hn i t ht') hC
          (hr0 t ht) (hr1 t ht) (fun n => hrn n t ht) k
      _ ≤ 8 * C * F k t + 2 * C * ((1 / 2 : ℝ) ^ (k + 3) * M) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hb (k + 3) t ht')
            (pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) (k + 3)))
          (show 0 ≤ 2 * C by positivity))
      _ = _ := by ring
  have hFg (k) (t : ℝ) (ht : t ∈ Icc a b) :
      F k t ≤ gronwallBound 0 (8 * C) (2 * C * M * (1 / 2 : ℝ) ^ (k + 3)) (t - a) :=
    le_gronwallBound_of_interior_deriv_le (hFc k)
      (fun s hs => (hFd k s hs).differentiableAt) (by rw [hF0]) (hFr k) t ht
  intro i t ht
  have hle (n : ℕ) : (1 / 2 : ℝ) ^ i * E i t ≤
      gronwallBound 0 (8 * C) (2 * C * M * (1 / 2 : ℝ) ^ (n + i + 3)) (t - a) := by
    have hs : (1 / 2 : ℝ) ^ i * E i t ≤ F (n + i) t := by
      apply Finset.single_le_sum (s := Finset.range (n + i + 3))
        (f := fun j => (1 / 2 : ℝ) ^ j * E j t)
      · intro j _
        exact mul_nonneg (pow_nonneg (by norm_num) j) (hn j t ht)
      · exact Finset.mem_range.mpr (by omega)
    exact hs.trans (hFg (n + i) t ht)
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have heps : Tendsto (fun n : ℕ => 2 * C * M * (1 / 2 : ℝ) ^ (n + i + 3))
      atTop (𝓝 0) := by
    simpa only [pow_add, mul_zero, zero_mul] using
      ((hp.mul_const ((1 / 2 : ℝ) ^ i)).mul_const ((1 / 2 : ℝ) ^ 3)).const_mul (2 * C * M)
  have hg : Tendsto (fun n : ℕ =>
      gronwallBound 0 (8 * C) (2 * C * M * (1 / 2 : ℝ) ^ (n + i + 3)) (t - a))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, gronwallBound_ε0_δ0] using
      ((gronwallBound_continuous_ε 0 (8 * C) (t - a)).tendsto 0).comp heps
  have hz : (1 / 2 : ℝ) ^ i * E i t ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hg hle
  exact le_antisymm (nonpos_of_mul_nonpos_right hz (pow_pos (by norm_num) _)) (hn i t ht)
