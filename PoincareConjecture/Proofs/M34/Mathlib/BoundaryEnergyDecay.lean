import PoincareConjecture.Proofs.M34.Mathlib.TentNeighborEnergy
import PoincareConjecture.Proofs.M34.Mathlib.InteriorGronwall
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set Filter
open scoped Topology BigOperators

theorem le_geometric_exp_of_bounded_neighbor_energy_rates
    {E : ℕ → ℝ → ℝ} {a b C M : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i, ContinuousOn (E i) (Icc a b))
    (hd : ∀ i t, t ∈ Ioo a b → DifferentiableAt ℝ (E i) t)
    (hinit : ∀ i, E i a = if i = 0 then M else 0)
    (hn : ∀ i t, t ∈ Icc a b → 0 ≤ E i t)
    (hb : ∀ i t, t ∈ Icc a b → E i t ≤ M)
    (hr0 : ∀ t ∈ Ioo a b, deriv (E 0) t ≤ 0)
    (hr : ∀ n t, t ∈ Ioo a b →
      deriv (E (n + 1)) t ≤ C * (E n t + E (n + 1) t + E (n + 2) t)) :
    ∀ j t, t ∈ Icc a b → E j t ≤ M * (1 / 2 : ℝ) ^ j * Real.exp (9 * C * (t - a)) := by
  intro j
  let w := fun i => (1 / 2 : ℝ) ^ Nat.dist i j
  let F := fun k t => ∑ i ∈ Finset.range (k + j + 3), w i * E i t
  have hw (i) : 0 ≤ w i := pow_nonneg (by norm_num) _
  have hFc (k) : ContinuousOn (F k) (Icc a b) :=
    continuousOn_finsetSum _ (fun i _ => continuousOn_const.mul (hc i))
  have hFd (k) (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (F k) (∑ i ∈ Finset.range (k + j + 3), w i * deriv (E i) t) t :=
    HasDerivAt.fun_sum (fun i _ => (hd i t ht).hasDerivAt.const_mul (w i))
  have hF0 (k) : F k a = M * (1 / 2 : ℝ) ^ j := by
    simp [F, hinit, w, Nat.dist_zero_left, mul_comm]
  have hFr (k) (t : ℝ) (ht : t ∈ Ioo a b) :
      deriv (F k) t ≤ 9 * C * F k t + 2 * C * M * (1 / 2 : ℝ) ^ (k + 3) := by
    rw [(hFd k t ht).deriv]
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    have hdistance : Nat.dist (k + j + 3) j = k + 3 := by simp only [Nat.dist]; omega
    have htail : w (k + j + 3) * E (k + j + 3) t ≤ (1 / 2 : ℝ) ^ (k + 3) * M := by
      dsimp only [w]
      rw [hdistance]
      exact mul_le_mul_of_nonneg_left (hb _ t ht') (pow_nonneg (by norm_num) _)
    calc
      _ ≤ 9 * C * F k t + 2 * C * (w (k + j + 3) * E (k + j + 3) t) :=
        weighted_neighbor_sum_range_le_nine (fun i => hn i t ht') hw
          (dyadic_nat_dist_adjacent_bounds j) hC (hr0 t ht) (fun n => hr n t ht) (k + j)
      _ ≤ 9 * C * F k t + 2 * C * ((1 / 2 : ℝ) ^ (k + 3) * M) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left htail (by positivity))
      _ = _ := by ring
  have hFg (k) (t : ℝ) (ht : t ∈ Icc a b) : F k t ≤
      gronwallBound (M * (1 / 2 : ℝ) ^ j) (9 * C)
        (2 * C * M * (1 / 2 : ℝ) ^ (k + 3)) (t - a) :=
    le_gronwallBound_of_interior_deriv_le (hFc k)
      (fun s hs => (hFd k s hs).differentiableAt) (hF0 k).le (hFr k) t ht
  intro t ht
  have hle (k : ℕ) : E j t ≤ gronwallBound (M * (1 / 2 : ℝ) ^ j) (9 * C)
      (2 * C * M * (1 / 2 : ℝ) ^ (k + 3)) (t - a) := by
    have hs : w j * E j t ≤ F k t := by
      apply Finset.single_le_sum (s := Finset.range (k + j + 3)) (f := fun i => w i * E i t)
      · exact fun i _ => mul_nonneg (hw i) (hn i t ht)
      · exact Finset.mem_range.mpr (by omega)
    have hj : w j = 1 := by simp [w]
    have hs' : E j t ≤ F k t := by simpa only [hj, one_mul] using hs
    exact hs'.trans (hFg k t ht)
  have hp : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have heps : Tendsto (fun k : ℕ => 2 * C * M * (1 / 2 : ℝ) ^ (k + 3))
      atTop (𝓝 0) := by
    simpa only [pow_add, mul_zero, zero_mul] using
      (hp.mul_const ((1 / 2 : ℝ) ^ 3)).const_mul (2 * C * M)
  have hg : Tendsto (fun k : ℕ => gronwallBound (M * (1 / 2 : ℝ) ^ j) (9 * C)
      (2 * C * M * (1 / 2 : ℝ) ^ (k + 3)) (t - a))
      atTop (𝓝 (M * (1 / 2 : ℝ) ^ j * Real.exp (9 * C * (t - a)))) := by
    simpa only [Function.comp_def, gronwallBound_ε0] using
      ((gronwallBound_continuous_ε (M * (1 / 2 : ℝ) ^ j) (9 * C) (t - a)).tendsto 0).comp heps
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hg hle
