import PoincareConjecture.Proofs.M35.RadialGauge.ScalarRapidProducts
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Group.Bounded










set_option autoImplicit false

open Set
open scoped ContDiff BigOperators

namespace PoincareConjecture.M35.RadialGauge



theorem positive_reciprocal_exterior_jets_bounded {A : Type*} {f : A → ℝ → ℝ}
    {c : ℝ} (hc : 0 < c)
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) (Ioi 0))
    (hpos : ∀ a r, 0 < r → 0 < f a r)
    (hfloor : ∀ a r, 1 ≤ r → c ≤ f a r)
    (hb : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ a r, 1 ≤ r →
      |iteratedDeriv j (f a) r| ≤ B) :
    ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ a r, 1 ≤ r →
      |iteratedDeriv j (fun s => 1 / f a s) r| ≤ B := by
  classical
  choose B hB0 hB using hb
  have hinv : ContDiffOn ℝ ∞ (fun r : ℝ => 1 / r) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun _ hr => ne_of_gt hr)
  have hj (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Icc c (B 0),
      ‖iteratedFDerivWithin ℝ i (fun r : ℝ => 1 / r) (Ioi 0) y‖ ≤ C := by
    have hd := hinv.continuousOn_iteratedFDerivWithin
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl i) isOpen_Ioi.uniqueDiffOn
    obtain ⟨C, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hd.mono (fun _ hy => hc.trans_le hy.1))
    exact ⟨max C 0, le_max_right _ _, fun y hy => (hCb y hy).trans (le_max_left _ _)⟩
  choose J hJ0 hJ using hj
  intro k
  let C := ∑ i ∈ Finset.range (k + 1), J i
  let D := 1 + ∑ i ∈ Finset.range (k + 1), B i
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => hJ0 i)
  have hD : 1 ≤ D := by
    have h := Finset.sum_nonneg (s := Finset.range (k + 1)) (fun i _ => hB0 i)
    dsimp only [D]
    linarith
  refine ⟨(k.factorial : ℝ) * C * D ^ k, by positivity, ?_⟩
  intro a r hr
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hfval : f a r ∈ Icc c (B 0) := by
    refine ⟨hfloor a r hr, ?_⟩
    exact (le_abs_self _).trans (by simpa only [iteratedDeriv_zero] using hB 0 a r hr)
  have ho (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDerivWithin ℝ i (fun r : ℝ => 1 / r) (Ioi 0) (f a r)‖ ≤ C := by
    exact (hJ i (f a r) hfval).trans (Finset.single_le_sum (fun j _ => hJ0 j)
      (show i ∈ Finset.range (k + 1) by
        simpa only [Finset.mem_range] using Nat.lt_succ_of_le hi))
  have hi (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
      ‖iteratedFDerivWithin ℝ i (f a) (Ioi 0) r‖ ≤ D ^ i := by
    rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi hrp,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    have hBi : B i ≤ D := by
      have h := Finset.single_le_sum (f := B) (fun j _ => hB0 j)
        (show i ∈ Finset.range (k + 1) by
          simpa only [Finset.mem_range] using Nat.lt_succ_of_le hik)
      dsimp only [D]
      linarith
    exact ((hB i a r hr).trans hBi).trans (le_self_pow₀ hD (by omega))
  have hcomp := norm_iteratedFDerivWithin_comp_le hinv (hf a)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
    isOpen_Ioi.uniqueDiffOn isOpen_Ioi.uniqueDiffOn (hpos a) hrp ho hi
  rw [iteratedFDerivWithin_of_isOpen k isOpen_Ioi hrp,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hcomp
  exact hcomp

end PoincareConjecture.M35.RadialGauge
