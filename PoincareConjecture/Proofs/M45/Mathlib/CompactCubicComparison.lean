import PoincareConjecture.Proofs.M05.Analysis.Parabolic.CompactMaximum
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false

open Set

namespace Poincare.Parabolic

theorem norm_le_reciprocal_of_sq_deriv_le_cube_at_max
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {N D : A → ℝ → ℝ} {C b : ℝ}
    (hC : 0 < C) (hb : 0 ≤ b) (hbC : C * b < 2)
    (hN : ContinuousOn (Function.uncurry N) (univ ×ˢ Icc 0 b))
    (hnonneg : ∀ q t, t ∈ Icc 0 b → 0 ≤ N q t)
    (hderiv : ∀ q t, t ∈ Ioc 0 b →
      HasDerivWithinAt (fun s => N q s ^ 2) (D q t) (Icc 0 b) t)
    (hmax : ∀ q t, t ∈ Ioc 0 b →
      (∀ p, N p t ≤ N q t) → D q t ≤ C * N q t ^ 3)
    (hinit : ∀ q, N q 0 ≤ 1) :
    ∀ q t, t ∈ Icc 0 b → N q t ≤ (1 - C * t / 2)⁻¹ := by
  let p : ℝ → ℝ := fun t => (1 - C * t / 2)⁻¹
  have hden (t : ℝ) (ht : t ∈ Icc 0 b) : 0 < 1 - C * t / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hC.le]
  have hppos (t : ℝ) (ht : t ∈ Icc 0 b) : 0 < p t := inv_pos.mpr (hden t ht)
  have hpc : ContinuousOn (fun q : A × ℝ => p q.2) (univ ×ˢ Icc 0 b) :=
    ((continuous_const.sub ((continuous_const.mul continuous_snd).div_const 2)).continuousOn).inv₀
      (fun q hq => (hden q.2 hq.2).ne')
  have hpd (t : ℝ) (ht : t ∈ Icc 0 b) :
      HasDerivAt (fun s => p s ^ 2) (C * p t ^ 3) t := by
    have hd : HasDerivAt p ((C / 2) / (1 - C * t / 2) ^ 2) t := by
      simpa only [p, id_eq, mul_one, neg_div, neg_neg] using!
        ((((hasDerivAt_id t).const_mul C).div_const 2).const_sub 1).inv (hden t ht).ne'
    convert! hd.pow 2 using 1
    dsimp [p]
    field_simp [(hden t ht).ne']
  obtain ⟨K, hK⟩ :=
    ((isCompact_univ : IsCompact (univ : Set A)).prod isCompact_Icc).bddAbove_image hN
  have hKpos : 0 < max K 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hbound (q : A) (t : ℝ) (ht : t ∈ Icc 0 b) : N q t ≤ max K 1 :=
    (hK (mem_image_of_mem (Function.uncurry N)
      (show (q, t) ∈ univ ×ˢ Icc 0 b from ⟨mem_univ q, ht⟩))).trans (le_max_left _ _)
  have hF := nonpos_of_deriv_le_mul_at_max
    (F := fun q t => N q t ^ 2 - p t ^ 2)
    (F' := fun q t => D q t - C * p t ^ 3)
    (a := 0) (b := b) (K := 3 * C * max K 1)
    (by simpa only [Function.uncurry, Pi.sub_apply, Pi.pow_apply] using!
      (hN.pow 2).sub (hpc.pow 2))
    (fun q t ht => (hderiv q t ht).sub (hpd t ⟨ht.1.le, ht.2⟩).hasDerivWithinAt)
    (fun q t ht hpos hspace => by
      have ht' : t ∈ Icc 0 b := ⟨ht.1.le, ht.2⟩
      have hNq := hnonneg q t ht'
      have hp := (hppos t ht').le
      have hpN : p t ≤ N q t := by nlinarith
      have hNmax (z : A) : N z t ≤ N q t := by
        have hz := hspace z
        nlinarith [hnonneg z t ht']
      have hD := hmax q t ht hNmax
      have hNK := hbound q t ht'
      have hpK := hpN.trans hNK
      have hquad : N q t ^ 2 + N q t * p t + p t ^ 2 ≤
          3 * max K 1 * (N q t + p t) := by
        nlinarith [mul_le_mul_of_nonneg_right hNK hNq,
          mul_le_mul_of_nonneg_right hNK hp, mul_le_mul_of_nonneg_right hpK hp,
          mul_nonneg hKpos.le hNq, mul_nonneg hKpos.le hp]
      have hpoly : N q t ^ 3 - p t ^ 3 ≤
          3 * max K 1 * (N q t ^ 2 - p t ^ 2) := by
        calc
          _ = (N q t - p t) * (N q t ^ 2 + N q t * p t + p t ^ 2) := by ring
          _ ≤ (N q t - p t) * (3 * max K 1 * (N q t + p t)) :=
            mul_le_mul_of_nonneg_left hquad (sub_nonneg.mpr hpN)
          _ = _ := by ring
      nlinarith [mul_le_mul_of_nonneg_left hpoly hC.le])
    (fun q => by
      have hq := pow_le_pow_left₀ (hnonneg q 0 ⟨le_rfl, hb⟩) (hinit q) 2
      simpa only [p, mul_zero, zero_div, sub_zero, inv_one, one_pow, sub_nonpos] using hq)
  intro q t ht
  have h := hF q t ht
  change N q t ≤ p t
  nlinarith [hnonneg q t ht, hppos t ht]

theorem norm_le_two_of_sq_deriv_le_cube_at_max_sharp
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {N D : A → ℝ → ℝ} {C b : ℝ}
    (hC : 0 < C) (hb : 0 ≤ b) (hbC : C * b ≤ 1)
    (hN : ContinuousOn (Function.uncurry N) (univ ×ˢ Icc 0 b))
    (hnonneg : ∀ q t, t ∈ Icc 0 b → 0 ≤ N q t)
    (hderiv : ∀ q t, t ∈ Ioc 0 b →
      HasDerivWithinAt (fun s => N q s ^ 2) (D q t) (Icc 0 b) t)
    (hmax : ∀ q t, t ∈ Ioc 0 b →
      (∀ p, N p t ≤ N q t) → D q t ≤ C * N q t ^ 3)
    (hinit : ∀ q, N q 0 ≤ 1) :
    ∀ q t, t ∈ Icc 0 b → N q t ≤ 2 := by
  intro q t ht
  have h := norm_le_reciprocal_of_sq_deriv_le_cube_at_max hC hb
    (lt_of_le_of_lt hbC (by norm_num)) hN hnonneg hderiv hmax hinit q t ht
  have hden : 1 / 2 ≤ 1 - C * t / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hC.le]
  apply h.trans
  rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < 1 - C * t / 2)]
  linarith

end Poincare.Parabolic
