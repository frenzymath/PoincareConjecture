import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsCapTensorNormAlgebra

/-!
# Finite tensor action and trace bounds

Every coefficient is retained. Acting on one tensor index costs the
operator norm, while contracting two equal indices costs sqrt(3).
These are the Hilbert--Schmidt bounds in the scalar-error remainder.
Source: Morgan--Tian, Definition 9.72, pp. 230-231.
-/

set_option autoImplicit false

open scoped BigOperators

namespace PoincareMT.M47

variable {ι : Type*} [Fintype ι]

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem cap_array_vector_norm_sq (f : ι → E₃) :
    ‖(WithLp.toLp 2 (fun p : ι × Fin 3 => f p.1 p.2) :
      EuclideanSpace ℝ (ι × Fin 3))‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  rw [cap_array_norm_sq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  exact (cap_array_norm_sq (fun j => f i j)).symm

/-- Applying a real operator to one index of an arbitrary finite
tensor costs its operator norm once. -/
theorem cap_array_operator_action_norm_le (L : E₃ →L[ℝ] E₃) (f : ι → E₃) :
    ‖(WithLp.toLp 2 (fun p : ι × Fin 3 => L (f p.1) p.2) :
      EuclideanSpace ℝ (ι × Fin 3))‖ ≤
      ‖L‖ * ‖(WithLp.toLp 2 (fun p : ι × Fin 3 => f p.1 p.2) :
        EuclideanSpace ℝ (ι × Fin 3))‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, cap_array_vector_norm_sq (fun i => L (f i)),
    cap_array_vector_norm_sq f, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg L) (norm_nonneg (f i)))).mpr (L.le_opNorm (f i))
  simpa only [mul_pow] using h

/-- Cauchy--Schwarz for the full finite coefficient pairing. -/
theorem cap_array_pairing_abs_le (f g : ι → ℝ) :
    |∑ i, f i * g i| ≤
      ‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖ *
        ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖ := by
  simpa only [PiLp.inner_apply, Real.inner_apply] using
    abs_real_inner_le_norm (WithLp.toLp 2 f : EuclideanSpace ℝ ι)
      (WithLp.toLp 2 g : EuclideanSpace ℝ ι)

/-- Tracing two three-dimensional covariant indices costs sqrt(3),
independently of the other finite indices. -/
theorem cap_array_trace_norm_le (T : ι → Fin 3 → Fin 3 → ℝ) :
    ‖(WithLp.toLp 2 (fun a => ∑ i, T a i i) : EuclideanSpace ℝ ι)‖ ≤
      Real.sqrt 3 * ‖(WithLp.toLp 2 (fun p : ι × (Fin 3 × Fin 3) => T p.1 p.2.1 p.2.2) :
        EuclideanSpace ℝ (ι × (Fin 3 × Fin 3)))‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
    cap_array_norm_sq, cap_array_norm_sq]
  simp only [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin 3 => (1 : ℝ)) (fun i => T a i i)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, mul_one] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 3))
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (fun j _ => sq_nonneg (T a i j)) (Finset.mem_univ i)

end PoincareMT.M47
