import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture.M30

theorem le_two_mul_of_deriv_le_sq_above {f f' : ℝ → ℝ} {a b C M q : ℝ}
    (hC : 0 < C) (hM : 0 < M) (hq : q ≤ M)
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ s ∈ Ico a b, HasDerivWithinAt f (f' s) (Ici s) s)
    (hinitial : f a ≤ M)
    (hrate : ∀ s ∈ Ico a b, q ≤ f s → f' s ≤ C * f s ^ 2)
    (htime : 8 * C * M * (b - a) ≤ 1) :
    ∀ s ∈ Icc a b, f s ≤ 2 * M := by
  let B : ℝ → ℝ := fun s => M + 8 * C * M ^ 2 * (s - a)
  have hBbounds (s : ℝ) (hs : s ∈ Icc a b) : M ≤ B s ∧ B s ≤ 2 * M := by
    have hlo : 0 ≤ 8 * C * M ^ 2 * (s - a) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hs.1)
    have htime' : 8 * C * M * (s - a) ≤ 1 :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 a) (by positivity)).trans htime
    have hhi := mul_le_mul_of_nonneg_right htime' hM.le
    dsimp [B]
    constructor <;> nlinarith
  have hBd (s : ℝ) : HasDerivAt B (8 * C * M ^ 2) s := by
    simpa only [B, id_eq, mul_one] using
      (((hasDerivAt_id s).sub_const a).const_mul (8 * C * M ^ 2)).const_add M
  have hle : ∀ s ∈ Icc a b, f s ≤ B s := by
    apply image_le_of_deriv_right_lt_deriv_boundary hcont hderiv
    · simpa only [B, sub_self, mul_zero, add_zero] using hinitial
    · exact hBd
    · intro s hs heq
      obtain ⟨hlo, hhi⟩ := hBbounds s ⟨hs.1, hs.2.le⟩
      have hflo : M ≤ f s := by rwa [heq]
      have hfhi : f s ≤ 2 * M := by rwa [heq]
      have hsquare : f s ^ 2 ≤ 4 * M ^ 2 := by nlinarith
      have hbound := (hrate s hs (hq.trans hflo)).trans
        (mul_le_mul_of_nonneg_left hsquare hC.le)
      have hpositive : 0 < C * M ^ 2 := mul_pos hC (sq_pos_of_pos hM)
      nlinarith
  intro s hs
  exact (hle s hs).trans (hBbounds s hs).2

theorem le_two_mul_of_abs_deriv_le_sq_above_backward
    {f f' : ℝ → ℝ} {a b C M q : ℝ}
    (hC : 0 < C) (hM : 0 < M) (hq : q ≤ M)
    (hderiv : ∀ s ∈ Icc a b, HasDerivWithinAt f (f' s) (Icc a b) s)
    (hterminal : f b ≤ M)
    (hrate : ∀ s ∈ Icc a b, q ≤ f s → |f' s| ≤ C * f s ^ 2)
    (htime : 8 * C * M * (b - a) ≤ 1) :
    ∀ s ∈ Icc a b, f s ≤ 2 * M := by
  have hmap : MapsTo (fun s : ℝ => -s) (Icc (-b) (-a)) (Icc a b) := by
    intro s hs
    exact ⟨le_neg.mp hs.2, neg_le.mp hs.1⟩
  have hd (s : ℝ) (hs : s ∈ Icc (-b) (-a)) :
      HasDerivWithinAt (fun t => f (-t)) (-f' (-s)) (Icc (-b) (-a)) s := by
    convert! (hderiv (-s) (hmap hs)).comp s
      (hasDerivWithinAt_id s (Icc (-b) (-a))).neg hmap using 1
    simp
  have hcont : ContinuousOn (fun s => f (-s)) (Icc (-b) (-a)) :=
    fun s hs => (hd s hs).continuousWithinAt
  have hbound := le_two_mul_of_deriv_le_sq_above hC hM hq hcont
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs))
    (by simpa using hterminal)
    (fun s hs hq' => (neg_le_abs (f' (-s))).trans
      (hrate (-s) (hmap (Ico_subset_Icc_self hs)) hq'))
    (by simpa only [neg_sub_neg] using htime)
  intro s hs
  simpa using hbound (-s) ⟨neg_le_neg hs.2, neg_le_neg hs.1⟩

theorem scalar_le_double_on_normalized_backward_interval
    {f f' : ℝ → ℝ} {C D Q tau : ℝ}
    (hC : 0 < C) (hD : 4 ≤ D) (hQ : 0 < Q)
    (hderiv : ∀ s ∈ Icc (-(tau / Q)) 0,
      HasDerivWithinAt f (f' s) (Icc (-(tau / Q)) 0) s)
    (hterminal : f 0 ≤ D * Q)
    (hrate : ∀ s ∈ Icc (-(tau / Q)) 0,
      4 * Q ≤ f s → |f' s| ≤ C * f s ^ 2)
    (htime : 8 * C * D * tau ≤ 1) :
    ∀ s ∈ Icc (-(tau / Q)) 0, f s ≤ 2 * D * Q := by
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have htime' : 8 * C * (D * Q) * (0 - -(tau / Q)) ≤ 1 := by
    calc
      8 * C * (D * Q) * (0 - -(tau / Q)) = 8 * C * D * tau := by
        rw [zero_sub, neg_neg]
        field_simp
      _ ≤ 1 := htime
  intro s hs
  simpa only [mul_assoc] using le_two_mul_of_abs_deriv_le_sq_above_backward
    hC (mul_pos hDpos hQ) (mul_le_mul_of_nonneg_right hD hQ.le)
    hderiv hterminal hrate htime' s hs

end PoincareConjecture.M30
