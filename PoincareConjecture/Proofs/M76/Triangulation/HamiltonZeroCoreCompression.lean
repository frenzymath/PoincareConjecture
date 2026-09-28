import PoincareConjecture.Proofs.M76.Mathlib.SmallLipschitzHomeomorph
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Normed.Group.Constructions












set_option autoImplicit false

open Set
open scoped NNReal

namespace PoincareConjecture.M76

variable {ι : Type*} [Fintype ι]

private noncomputable def coreMargin (x : ι → ℝ) : ℝ := max 0 (2 - ‖x‖)

private noncomputable def clippedCore (x : ι → ℝ) : ι → ℝ :=
  fun i => max (-coreMargin x) (min (x i) (coreMargin x))

private theorem clippedCore_lipschitz : LipschitzWith 1 (clippedCore (ι := ι)) := by
  have hm : LipschitzWith 1 (coreMargin (ι := ι)) := by
    have h : LipschitzWith 1 (fun x : ι → ℝ => 2 - ‖x‖) := by
      simpa using (LipschitzWith.const (2 : ℝ)).sub
        (lipschitzWith_one_norm : LipschitzWith 1 (norm : (ι → ℝ) → ℝ))
    exact h.const_max 0
  have hc (i : ι) : LipschitzWith 1 (fun x : ι → ℝ => x i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul, Pi.sub_apply] using
      norm_le_pi_norm (x - y) i
  have hi (i : ι) : LipschitzWith 1 (fun x : ι → ℝ => clippedCore x i) := by
    simpa only [clippedCore, Pi.neg_apply, max_self] using hm.neg.max ((hc i).min hm)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_one, one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))).mpr
  intro i
  simpa only [Pi.sub_apply, NNReal.coe_one, one_mul] using (hi i).norm_sub_le x y

private theorem clippedCore_eq (x : ι → ℝ) (hx : ‖x‖ ≤ 1) : clippedCore x = x := by
  have hmargin : ‖x‖ ≤ coreMargin x := by
    exact (show ‖x‖ ≤ 2 - ‖x‖ by linarith).trans (le_max_right _ _)
  funext i
  have hi : |x i| ≤ coreMargin x :=
    (show |x i| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i).trans hmargin
  rw [clippedCore, min_eq_left (le_trans (le_abs_self _) hi),
    max_eq_right (le_trans (neg_le_neg hi) (neg_abs_le _))]

private theorem clippedCore_eq_zero (x : ι → ℝ) (hx : 2 ≤ ‖x‖) : clippedCore x = 0 := by
  have hm : coreMargin x = 0 := max_eq_left (sub_nonpos.mpr hx)
  funext i
  simp only [clippedCore, hm, neg_zero, Pi.zero_apply]
  exact max_eq_left (min_le_right _ _)

private theorem exists_supported_core_halving :
    ∃ H : (ι → ℝ) ≃ₜ (ι → ℝ),
      (∀ x, ‖x‖ ≤ 1 → H x = (1 / 2 : ℝ) • x) ∧
      ∀ x, 2 ≤ ‖x‖ → H x = x := by
  let u : (ι → ℝ) → (ι → ℝ) := fun x => (-1 / 2 : ℝ) • clippedCore x
  have hu : LipschitzWith (1 / 2) u := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖(-1 / 2 : ℝ) • clippedCore x - (-1 / 2 : ℝ) • clippedCore y‖ ≤
      ((1 / 2 : ℝ≥0) : ℝ) * ‖x - y‖
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    norm_num
    have hclip := (clippedCore_lipschitz (ι := ι)).norm_sub_le x y
    simpa only [Pi.sub_apply, NNReal.coe_one, one_mul] using hclip
  obtain ⟨H, hH⟩ := hu.exists_homeomorph_add (by norm_num)
  refine ⟨H, ?_, ?_⟩
  · intro x hx
    rw [hH]
    change x + (-1 / 2 : ℝ) • clippedCore x = (1 / 2 : ℝ) • x
    rw [clippedCore_eq x hx]
    calc
      x + (-1 / 2 : ℝ) • x = (1 + (-1 / 2) : ℝ) • x := by rw [add_smul, one_smul]
      _ = (1 / 2 : ℝ) • x := by norm_num
  · intro x hx
    rw [hH]
    change x + (-1 / 2 : ℝ) • clippedCore x = x
    rw [clippedCore_eq_zero x hx, smul_zero, add_zero]




theorem exists_supported_unit_cube_compression (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ (r : ℝ) (H : (ι → ℝ) ≃ₜ (ι → ℝ)),
      0 < r ∧ r ≤ 1 ∧ r < epsilon ∧
      (∀ x, ‖x‖ ≤ 1 → H x = r • x) ∧
      ∀ x, 2 ≤ ‖x‖ → H x = x := by
  obtain ⟨H, hHcore, hHout⟩ := exists_supported_core_halving (ι := ι)
  let S : ℕ → ((ι → ℝ) ≃ₜ (ι → ℝ)) :=
    Nat.rec (Homeomorph.refl _) (fun _ e => e.trans H)
  have hS (n : ℕ) :
      (∀ x, ‖x‖ ≤ 1 → S n x = (1 / 2 : ℝ) ^ n • x) ∧
      ∀ x, 2 ≤ ‖x‖ → S n x = x := by
    induction n with
    | zero => exact ⟨fun _ _ => by simp [S], fun _ _ => rfl⟩
    | succ n ih =>
      constructor
      · intro x hx
        change H (S n x) = (1 / 2 : ℝ) ^ (n + 1) • x
        rw [ih.1 x hx, hHcore]
        · rw [smul_smul, pow_succ']
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by norm_num) _)]
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n,
            pow_le_one₀ (n := n) (by norm_num : (0 : ℝ) ≤ 1 / 2)
              (by norm_num : (1 / 2 : ℝ) ≤ 1),
            norm_nonneg x]
      · intro x hx
        change H (S n x) = x
        rw [ih.2 x hx, hHout x hx]
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hepsilon (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨(1 / 2 : ℝ) ^ n, S n, pow_pos (by norm_num) _,
    pow_le_one₀ (by norm_num) (by norm_num), hn, (hS n).1, (hS n).2⟩

end PoincareConjecture.M76
