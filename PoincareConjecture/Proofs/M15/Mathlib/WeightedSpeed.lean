import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt











set_option autoImplicit false

open Filter Set
open scoped Topology

namespace Real



theorem le_exp_sq_mul_of_deriv_le {v v' : ℝ → ℝ} {a b S : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hv : ContinuousOn v (Icc 0 S))
    (hv' : ∀ s ∈ Ioo 0 S, HasDerivAt v (v' s) s)
    (hbound : ∀ s ∈ Ioo 0 S, v' s ≤ 2 * a * s * v s + 2 * b * s ^ 2) :
    ∀ s ∈ Icc 0 S,
      v s ≤ exp (a * s ^ 2) * (v 0 + (2 / 3 : ℝ) * b * s ^ 3) := by
  let f := fun s => exp (-a * s ^ 2) * v s - (2 / 3 : ℝ) * b * s ^ 3
  let f' := fun s => exp (-a * s ^ 2) * (v' s - 2 * a * s * v s) -
    2 * b * s ^ 2
  have hf : ContinuousOn f (Icc 0 S) := by
    dsimp [f]
    fun_prop
  have hf' (s : ℝ) (hs : s ∈ Ioo 0 S) : HasDerivAt f (f' s) s := by
    convert (((((hasDerivAt_id s).pow 2).const_mul (-a)).exp.mul (hv' s hs)).sub
      (((hasDerivAt_id s).pow 3).const_mul ((2 / 3 : ℝ) * b))) using 1 <;>
      first | rfl | (dsimp [f, f']; ring)
  have hf'_nonpos (s : ℝ) (hs : s ∈ Ioo 0 S) : f' s ≤ 0 := by
    have he : exp (-a * s ^ 2) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [sq_nonneg s])
    have h₁ := mul_le_mul_of_nonneg_left (hbound s hs) (exp_pos (-a * s ^ 2)).le
    have h₂ := mul_le_mul_of_nonneg_right he
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb) (sq_nonneg s))
    dsimp [f']
    nlinarith
  have hanti : AntitoneOn f (Icc 0 S) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 S) hf
    · intro s hs
      exact (hf' s (by simpa only [interior_Icc] using hs)).hasDerivWithinAt
    · intro s hs
      exact hf'_nonpos s (by simpa only [interior_Icc] using hs)
  intro s hs
  have h := hanti ⟨le_rfl, hS⟩ hs hs.1
  dsimp [f] at h
  norm_num at h
  have hstep : exp (-a * s ^ 2) * v s ≤ v 0 + (2 / 3 : ℝ) * b * s ^ 3 := by
    simpa only [neg_mul] using h
  have hcancel : exp (a * s ^ 2) * exp (-a * s ^ 2) = 1 := by
    rw [← exp_add]
    simp
  have hmul := mul_le_mul_of_nonneg_left hstep (exp_pos (a * s ^ 2)).le
  rw [← mul_assoc, hcancel, one_mul] at hmul
  exact hmul



theorem sqrt_le_exp_sq_mul_of_deriv_le {q q' : ℝ → ℝ} {a b S : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hq : ContinuousOn q (Icc 0 S)) (hq_nonneg : ∀ s ∈ Icc 0 S, 0 ≤ q s)
    (hq' : ∀ s ∈ Ioo 0 S, HasDerivAt q (q' s) s)
    (hbound : ∀ s ∈ Ioo 0 S,
      q' s ≤ 4 * a * s * q s + 4 * b * s ^ 2 * sqrt (q s)) :
    ∀ s ∈ Icc 0 S,
      sqrt (q s) ≤ exp (a * s ^ 2) * (sqrt (q 0) + (2 / 3 : ℝ) * b * s ^ 3) := by
  intro s hs
  have hregularized (η : ℝ) (hη : 0 < η) :
      sqrt (q s) ≤ exp (a * s ^ 2) *
        (sqrt (q 0 + η ^ 2) + (2 / 3 : ℝ) * b * s ^ 3) := by
    have hpositive (t : ℝ) (ht : t ∈ Icc 0 S) : 0 < q t + η ^ 2 :=
      add_pos_of_nonneg_of_pos (hq_nonneg t ht) (sq_pos_of_pos hη)
    have hv' (t : ℝ) (ht : t ∈ Ioo 0 S) :
        HasDerivAt (fun t => sqrt (q t + η ^ 2))
          (q' t / (2 * sqrt (q t + η ^ 2))) t :=
      ((hq' t ht).add_const (η ^ 2)).sqrt (ne_of_gt (hpositive t (Ioo_subset_Icc_self ht)))
    have hvbound (t : ℝ) (ht : t ∈ Ioo 0 S) :
        q' t / (2 * sqrt (q t + η ^ 2)) ≤
          2 * a * t * sqrt (q t + η ^ 2) + 2 * b * t ^ 2 := by
      apply (div_le_iff₀ (mul_pos (by norm_num) (sqrt_pos.mpr
        (hpositive t (Ioo_subset_Icc_self ht))))).2
      have hqv : q t ≤ sqrt (q t + η ^ 2) ^ 2 := by
        rw [sq_sqrt (hpositive t (Ioo_subset_Icc_self ht)).le]
        nlinarith [sq_nonneg η]
      have hroot : sqrt (q t) ≤ sqrt (q t + η ^ 2) :=
        sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg η))
      have h₁ := mul_le_mul_of_nonneg_left hqv
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ha) ht.1.le)
      have h₂ := mul_le_mul_of_nonneg_left hroot
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hb) (sq_nonneg t))
      nlinarith [hbound t ht]
    exact (sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg η))).trans
      (le_exp_sq_mul_of_deriv_le ha hb hS (hq.add continuousOn_const).sqrt
        hv' hvbound s hs)
  have hlim : Tendsto
      (fun η : ℝ => exp (a * s ^ 2) *
        (sqrt (q 0 + η ^ 2) + (2 / 3 : ℝ) * b * s ^ 3))
      (𝓝[>] (0 : ℝ))
      (𝓝 (exp (a * s ^ 2) * (sqrt (q 0) + (2 / 3 : ℝ) * b * s ^ 3))) := by
    have hc : ContinuousAt
        (fun η : ℝ => exp (a * s ^ 2) *
          (sqrt (q 0 + η ^ 2) + (2 / 3 : ℝ) * b * s ^ 3)) 0 := by
      fun_prop
    have ht : Tendsto
        (fun η : ℝ => exp (a * s ^ 2) *
          (sqrt (q 0 + η ^ 2) + (2 / 3 : ℝ) * b * s ^ 3)) (𝓝 (0 : ℝ))
        (𝓝 (exp (a * s ^ 2) * (sqrt (q 0) + (2 / 3 : ℝ) * b * s ^ 3))) := by
      simpa using hc.tendsto
    exact ht.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact hregularized η hη

end Real
