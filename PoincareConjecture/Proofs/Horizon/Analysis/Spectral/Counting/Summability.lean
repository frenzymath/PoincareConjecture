/-
Provenance and modification notice (recorded 2026-09-29).
Notices for the adapted portions:
Copyright 2026 The DifferentialGeometry contributors
Source: https://github.com/qinz1yang/differential-geometry
DifferentialGeometry/Analysis/Spectral/Intrinsic/Garding/EigenvalueTailSummableFromCounting.lean
Comparison revision: 1b535dd102b94cc42b107cca27059687888f08b3.
Modifications: The dyadic summability proof is adapted to an arbitrary index type and finite-subset
counting.
License: Apache-2.0; see LICENSES/Apache-2.0.txt and NOTICE.
See MODIFICATIONS.md for the reviewed file mapping and scope of this notice.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

noncomputable section

namespace Poincare.Analysis.Spectral.Counting

open scoped BigOperators

theorem summable_neg_rpow_of_counting {ι : Type*} (w : ι → ℝ)
    (hw : ∀ i, 1 ≤ w i) (q : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hcount : ∀ (R : ℝ), 1 ≤ R → ∀ s : Finset ι,
      (∀ i ∈ s, w i ≤ R) → (s.card : ℝ) ≤ A * R ^ q) :
    Summable (fun i => (w i) ^ (-((q : ℝ) + 2))) := by
  classical
  set p : ℝ := (q : ℝ) + 2 with hp_def
  have hp_nn : (0 : ℝ) ≤ p := by rw [hp_def]; positivity
  set f : ι → ℝ := fun i => (w i) ^ (-p) with hf_def
  set shell : ι → ℕ := fun i => Nat.log 2 ⌊w i⌋₊ with hshell_def
  have hwpos : ∀ i, 0 < w i := fun i => lt_of_lt_of_le one_pos (hw i)
  have hwnn : ∀ i, 0 ≤ w i := fun i => (hwpos i).le
  have hfloor1 : ∀ i, 1 ≤ ⌊w i⌋₊ := fun i => (Nat.one_le_floor_iff (w i)).mpr (hw i)
  have h_lower : ∀ i, (2 : ℝ) ^ (shell i) ≤ w i := by
    intro i
    have h1 : 2 ^ (shell i) ≤ ⌊w i⌋₊ :=
      Nat.pow_log_le_self 2 (Nat.one_le_iff_ne_zero.mp (hfloor1 i))
    calc (2 : ℝ) ^ (shell i) = ((2 ^ (shell i) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊w i⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ w i := Nat.floor_le (hwnn i)
  have h_upper : ∀ i, w i < 2 ^ (shell i + 1) := by
    intro i
    have h0 : ⌊w i⌋₊ < 2 ^ (shell i + 1) :=
      Nat.lt_pow_succ_log_self one_lt_two ⌊w i⌋₊
    have h1 : ⌊w i⌋₊ + 1 ≤ 2 ^ (shell i + 1) := Nat.succ_le_of_lt h0
    have h2 : w i < (⌊w i⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (w i)
    have h3 : (⌊w i⌋₊ : ℝ) + 1 ≤ (2 : ℝ) ^ (shell i + 1) := by
      exact_mod_cast h1
    linarith
  have hf_nn : ∀ i, 0 ≤ f i := fun i => Real.rpow_nonneg (hwnn i) _
  have hf_le : ∀ i, f i ≤ (2 : ℝ) ^ (-(shell i : ℝ) * p) := by
    intro i
    rw [hf_def]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (shell i) := by positivity
    have hstep : (w i) ^ (-p) ≤ ((2 : ℝ) ^ (shell i)) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos h2pos (h_lower i) (neg_nonpos.mpr hp_nn)
    refine hstep.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast (2 : ℝ) (shell i),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  set g : ℕ → ℝ := fun m => A * 2 ^ q * (2 : ℝ) ^ (-(2 : ℝ) * m) with hg_def
  have hsummand_eq : (fun m : ℕ => (2 : ℝ) ^ (-(2 : ℝ) * m)) =
      fun m : ℕ => ((1 : ℝ) / 4) ^ m := by
    funext m
    rw [show (-(2 : ℝ) * (m : ℝ)) = ((m : ℝ) * (-(2 : ℝ))) by ring,
      Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg h2m_pos.le, Real.rpow_natCast]
    rw [← pow_mul, mul_comm m 2, pow_mul, ← inv_pow]
    norm_num
  have hbase_summable : Summable (fun m : ℕ => (2 : ℝ) ^ (-(2 : ℝ) * m)) := by
    rw [hsummand_eq]
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hg_summable : Summable g := hbase_summable.mul_left (A * 2 ^ q)
  have hg_nn : ∀ m, 0 ≤ g m := fun m => by rw [hg_def]; positivity
  refine summable_of_sum_le (c := ∑' m, g m) hf_nn (fun u => ?_)
  have hpartition :
      ∑ m ∈ u.image shell, ∑ i ∈ u with shell i = m, f i = ∑ i ∈ u, f i :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem shell hi) f
  rw [← hpartition]
  have hfiber : ∀ m ∈ u.image shell,
      ∑ i ∈ u with shell i = m, f i ≤ g m := by
    intro m _hm
    have hbound_each : ∀ i ∈ u.filter (fun i => shell i = m),
        f i ≤ (2 : ℝ) ^ (-(m : ℝ) * p) := by
      intro i hi
      have hsi : shell i = m := (Finset.mem_filter.mp hi).2
      simpa only [hsi] using hf_le i
    have hcard_le : ((u.filter (fun i => shell i = m)).card : ℝ) ≤
        A * (2 : ℝ) ^ ((m + 1) * q) := by
      rw [pow_mul]
      apply hcount _ (one_le_pow₀ (by norm_num))
      intro i hi
      have hsi : shell i = m := (Finset.mem_filter.mp hi).2
      simpa only [hsi] using (h_upper i).le
    calc ∑ i ∈ u with shell i = m, f i
        ≤ ∑ _i ∈ u.filter (fun i => shell i = m), (2 : ℝ) ^ (-(m : ℝ) * p) :=
          Finset.sum_le_sum hbound_each
      _ = ((u.filter (fun i => shell i = m)).card : ℝ) *
          (2 : ℝ) ^ (-(m : ℝ) * p) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A * 2 ^ ((m + 1) * q)) * (2 : ℝ) ^ (-(m : ℝ) * p) :=
          mul_le_mul_of_nonneg_right hcard_le (Real.rpow_nonneg (by norm_num) _)
      _ = g m := by
          simp only [hg_def, hp_def]
          have h2pos : (0 : ℝ) < 2 := by norm_num
          have h2q : (2 : ℝ) ^ ((m + 1) * q) =
              (2 : ℝ) ^ (((m : ℝ) * q + q) : ℝ) := by
            rw [← Real.rpow_natCast (2 : ℝ) ((m + 1) * q)]
            congr 1
            push_cast
            ring
          have h2qcast : (2 : ℝ) ^ q = (2 : ℝ) ^ ((q : ℝ)) :=
            (Real.rpow_natCast 2 q).symm
          have hexpL : ((m : ℝ) * q + q) + (-(m : ℝ) * (q + 2)) =
              (q : ℝ) + (-2 * (m : ℝ)) := by ring
          rw [h2q, h2qcast, mul_assoc A, mul_assoc A,
            ← Real.rpow_add h2pos, ← Real.rpow_add h2pos, hexpL]
  refine (Finset.sum_le_sum hfiber).trans ?_
  exact hg_summable.sum_le_tsum _ (fun m _ => hg_nn m)

theorem summable_weighted_exp_of_counting {ι : Type*} (lam : ι → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (C : ℝ) (hC : 0 ≤ C) (p : ℝ)
    (hcount : ∀ (L : ℝ), 0 ≤ L → ∀ s : Finset ι,
      (∀ i ∈ s, lam i ≤ L) → (s.card : ℝ) ≤ C * (1 + L) ^ p)
    {t : ℝ} (ht : 0 < t) (m : ℕ) :
    Summable (fun i => (1 + lam i) ^ m * Real.exp (-t * lam i)) := by
  let q : ℕ := ⌈p⌉₊
  have hw : ∀ i, 1 ≤ 1 + lam i := fun i => by linarith [hlam i]
  have htail := summable_neg_rpow_of_counting (fun i => 1 + lam i) hw q C hC
    (by
      intro R hR s hs
      have hb := hcount (R - 1) (by linarith) s (fun i hi => by linarith [hs i hi])
      have hRq : R ^ p ≤ R ^ q := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hR (Nat.le_ceil p)
      have hRone : 1 + (R - 1) = R := by ring
      rw [hRone] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left hRq hC))
  have hsum : Summable (fun i => ((1 + lam i) ^ (q + 2))⁻¹) := by
    convert htail using 1
    funext i
    rw [show (q : ℝ) + 2 = ((q + 2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg (by linarith [hlam i]), Real.rpow_natCast]
  let k : ℕ := m + q + 2
  let B : ℝ := Real.exp t * ((k.factorial : ℝ) / t ^ k)
  refine (hsum.mul_left B).of_nonneg_of_le
    (fun i => mul_nonneg (pow_nonneg (by linarith [hlam i]) _) (Real.exp_pos _).le)
    (fun i => ?_)
  have hx : 0 < 1 + lam i := by linarith [hlam i]
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have he := Real.pow_div_factorial_le_exp ((1 + lam i) * t)
    (mul_nonneg hx.le ht.le) k
  rw [div_le_iff₀ hfac] at he
  have he' := mul_le_mul_of_nonneg_right he
    (Real.exp_pos (-((1 + lam i) * t))).le
  rw [mul_assoc, mul_comm (k.factorial : ℝ), ← mul_assoc,
    ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at he'
  have hb : (1 + lam i) ^ k * Real.exp (-((1 + lam i) * t)) ≤
      (k.factorial : ℝ) / t ^ k := by
    apply (le_div_iff₀ (pow_pos ht k)).mpr
    calc
      (1 + lam i) ^ k * Real.exp (-((1 + lam i) * t)) * t ^ k =
          ((1 + lam i) * t) ^ k * Real.exp (-((1 + lam i) * t)) := by
            rw [mul_pow]; ring
      _ ≤ (k.factorial : ℝ) := he'
  have hexp : Real.exp (-t * lam i) =
      Real.exp t * Real.exp (-((1 + lam i) * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change (1 + lam i) ^ m * Real.exp (-t * lam i) ≤ B / (1 + lam i) ^ (q + 2)
  apply (le_div_iff₀ (pow_pos hx (q + 2))).mpr
  calc
    (1 + lam i) ^ m * Real.exp (-t * lam i) * (1 + lam i) ^ (q + 2) =
        Real.exp t * ((1 + lam i) ^ k * Real.exp (-((1 + lam i) * t))) := by
          rw [hexp, show k = m + (q + 2) by simp [k, Nat.add_assoc], pow_add]
          ring
    _ ≤ B := mul_le_mul_of_nonneg_left hb (Real.exp_pos t).le

end Poincare.Analysis.Spectral.Counting
