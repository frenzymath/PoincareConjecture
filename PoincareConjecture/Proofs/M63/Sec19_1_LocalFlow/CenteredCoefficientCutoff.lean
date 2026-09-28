import PoincareConjecture.Proofs.M03.Existence.DeTurckTraceCutoffNative









set_option autoImplicit false

namespace PoincareConjecture.M63

open SpectralHeatNative QuasilinearDeTurckNative

variable {iota E : Type*} [Countable iota]
  [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem norm_centeredCoefficientCutoff_sub_le (lambda : iota → NNReal)
    {r : ℝ} (hr : 0 < r) (M : E →L[ℝ] State iota →L[ℝ] State iota)
    (a : State iota → E) (b : State iota → State iota)
    {eps A B : ℝ} (_heps : 0 ≤ eps) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha0 : ‖a 0‖ ≤ eps)
    (ha : ∀ z z', ‖z‖ ≤ r → ‖z'‖ ≤ r → ‖a z - a z'‖ ≤ A * ‖z - z'‖)
    (hb : ∀ z z', ‖z‖ ≤ r → ‖z'‖ ≤ r → ‖b z - b z'‖ ≤ B * ‖z - z'‖)
    (P x y : State iota) :
    let C := fun z => shiftedBaseMultiplier lambda (traceCutoff lambda r z)
    ‖(M (a (C x)) (P + x) + b (C x)) - (M (a (C y)) (P + y) + b (C y))‖ ≤
      ‖M‖ * eps * ‖x - y‖ + 2 * ‖M‖ * A *
        (max ‖shiftedBaseMultiplier lambda x‖ ‖shiftedBaseMultiplier lambda y‖ * ‖x - y‖ +
          ‖shiftedBaseMultiplier lambda (x - y)‖ * ‖P + y‖) +
      2 * B * ‖shiftedBaseMultiplier lambda (x - y)‖ := by
  let C := fun z => shiftedBaseMultiplier lambda (traceCutoff lambda r z)
  have hCr (z) : ‖C z‖ ≤ r := norm_trace_traceCutoff_le lambda hr z
  have hCo (z) : ‖C z‖ ≤ ‖shiftedBaseMultiplier lambda z‖ :=
    norm_trace_traceCutoff_le_original lambda hr z
  have hCd : ‖C x - C y‖ ≤ 2 * ‖shiftedBaseMultiplier lambda (x - y)‖ := by
    simpa only [map_sub] using norm_trace_traceCutoff_sub_le lambda hr x y
  have hac : ‖a (C x)‖ ≤ eps + A * ‖shiftedBaseMultiplier lambda x‖ := by
    have h := ha (C x) 0 (hCr x) (by simpa using hr.le)
    simp only [sub_zero] at h
    calc
      _ ≤ ‖a (C x) - a 0‖ + ‖a 0‖ := norm_le_norm_sub_add _ _
      _ ≤ A * ‖C x‖ + eps := add_le_add h ha0
      _ ≤ eps + A * ‖shiftedBaseMultiplier lambda x‖ := by
        linarith [mul_le_mul_of_nonneg_left (hCo x) hA]
  have had : ‖a (C x) - a (C y)‖ ≤ 2 * A * ‖shiftedBaseMultiplier lambda (x - y)‖ := by
    calc
      _ ≤ A * ‖C x - C y‖ := ha _ _ (hCr x) (hCr y)
      _ ≤ A * (2 * ‖shiftedBaseMultiplier lambda (x - y)‖) :=
        mul_le_mul_of_nonneg_left hCd hA
      _ = _ := by ring
  have hbd : ‖b (C x) - b (C y)‖ ≤ 2 * B * ‖shiftedBaseMultiplier lambda (x - y)‖ := by
    calc
      _ ≤ B * ‖C x - C y‖ := hb _ _ (hCr x) (hCr y)
      _ ≤ B * (2 * ‖shiftedBaseMultiplier lambda (x - y)‖) :=
        mul_le_mul_of_nonneg_left hCd hB
      _ = _ := by ring
  have heq : (M (a (C x)) (P + x) + b (C x)) -
      (M (a (C y)) (P + y) + b (C y)) =
      M (a (C x)) (x - y) + M (a (C x) - a (C y)) (P + y) +
        (b (C x) - b (C y)) := by
    simp only [map_sub, map_add, sub_apply]
    abel
  have hm : ‖shiftedBaseMultiplier lambda x‖ ≤
      2 * max ‖shiftedBaseMultiplier lambda x‖ ‖shiftedBaseMultiplier lambda y‖ := by
    have h := le_max_left ‖shiftedBaseMultiplier lambda x‖ ‖shiftedBaseMultiplier lambda y‖
    linarith [norm_nonneg (shiftedBaseMultiplier lambda x)]
  have hm' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (mul_nonneg (norm_nonneg M) hA)) (norm_nonneg (x - y))
  change ‖(M (a (C x)) (P + x) + b (C x)) - (M (a (C y)) (P + y) + b (C y))‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖M (a (C x)) (x - y)‖ + ‖M (a (C x) - a (C y)) (P + y)‖ +
        ‖b (C x) - b (C y)‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖M‖ * ‖a (C x)‖ * ‖x - y‖ +
        ‖M‖ * ‖a (C x) - a (C y)‖ * ‖P + y‖ +
        2 * B * ‖shiftedBaseMultiplier lambda (x - y)‖ :=
      add_le_add (add_le_add (M.le_opNorm₂ _ _) (M.le_opNorm₂ _ _)) hbd
    _ ≤ ‖M‖ * (eps + A * ‖shiftedBaseMultiplier lambda x‖) * ‖x - y‖ +
        ‖M‖ * (2 * A * ‖shiftedBaseMultiplier lambda (x - y)‖) * ‖P + y‖ +
        2 * B * ‖shiftedBaseMultiplier lambda (x - y)‖ :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hac (norm_nonneg M))
          (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left had (norm_nonneg M))
          (norm_nonneg _))) le_rfl
    _ ≤ _ := by nlinarith only [hm']

end PoincareConjecture.M63
