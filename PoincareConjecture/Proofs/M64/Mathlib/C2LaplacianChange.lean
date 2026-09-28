import PoincareConjecture.Proofs.M60.Mathlib.SecondDerivativeChain

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Filter
open scoped Topology ContDiff

namespace PoincareConjecture

variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem m64C2_laplacian_comp {f : P → E} {H : E → F} {x : P}
    (hf : ContDiffAt ℝ 2 f x) (hH : ContDiffAt ℝ 2 H (f x)) (b : Fin 2 → P) :
    (∑ i, fderiv ℝ (fderiv ℝ (H ∘ f)) x (b i) (b i)) =
      (∑ i, fderiv ℝ (fderiv ℝ H) (f x) (fderiv ℝ f x (b i))
        (fderiv ℝ f x (b i))) +
      fderiv ℝ H (f x) (∑ i, fderiv ℝ (fderiv ℝ f) x (b i) (b i)) := by
  simp_rw [M60.second_fderiv_comp hH hf]
  rw [Finset.sum_add_distrib, map_sum]

theorem m64C1_reconstruction_column_bound {f : P → E} {u : P → F} {A : F → E}
    {x : P} (hu : DifferentiableAt ℝ u x) (hA : DifferentiableAt ℝ A (u x))
    (heq : f =ᶠ[𝓝 x] A ∘ u) {L : ℝ} (hL : ‖fderiv ℝ A (u x)‖ ≤ L) (v : P) :
    ‖fderiv ℝ f x v‖ ≤ L * ‖fderiv ℝ u x v‖ := by
  rw [heq.fderiv_eq, fderiv_comp x hA hu, ContinuousLinearMap.comp_apply]
  exact ((fderiv ℝ A (u x)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

theorem m64C2_coordinate_laplacian_growth {f : P → E} {H : E → F} {x : P}
    (hf : ContDiffAt ℝ 2 f x) (hH : ContDiffAt ℝ 2 H (f x)) (b : Fin 2 → P)
    {C D1 D2 L : ℝ} (hC : 0 ≤ C) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hL : 0 ≤ L)
    (hfirst : ‖fderiv ℝ H (f x)‖ ≤ D1)
    (hsecond : ‖fderiv ℝ (fderiv ℝ H) (f x)‖ ≤ D2)
    (hgrowth : ‖∑ i, fderiv ℝ (fderiv ℝ f) x (b i) (b i)‖ ≤
      C * ∑ i, ‖fderiv ℝ f x (b i)‖ ^ 2)
    (hback : ∀ i, ‖fderiv ℝ f x (b i)‖ ≤ L * ‖fderiv ℝ (H ∘ f) x (b i)‖) :
    ‖∑ i, fderiv ℝ (fderiv ℝ (H ∘ f)) x (b i) (b i)‖ ≤
      ((D2 + D1 * C) * L ^ 2) * ∑ i, ‖fderiv ℝ (H ∘ f) x (b i)‖ ^ 2 := by
  have hquad (i : Fin 2) :
      ‖fderiv ℝ (fderiv ℝ H) (f x) (fderiv ℝ f x (b i)) (fderiv ℝ f x (b i))‖ ≤
        D2 * ‖fderiv ℝ f x (b i)‖ ^ 2 := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ H) (f x)‖ *
          ‖fderiv ℝ f x (b i)‖ * ‖fderiv ℝ f x (b i)‖ :=
        (fderiv ℝ (fderiv ℝ H) (f x)).le_opNorm₂ _ _
      _ ≤ D2 * ‖fderiv ℝ f x (b i)‖ * ‖fderiv ℝ f x (b i)‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsecond (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have henergy : (∑ i, ‖fderiv ℝ f x (b i)‖ ^ 2) ≤
      L ^ 2 * ∑ i, ‖fderiv ℝ (H ∘ f) x (b i)‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mpr (hback i)
  rw [m64C2_laplacian_comp hf hH b]
  calc
    _ ≤ (∑ i, ‖fderiv ℝ (fderiv ℝ H) (f x)
          (fderiv ℝ f x (b i)) (fderiv ℝ f x (b i))‖) +
        ‖fderiv ℝ H (f x) (∑ i, fderiv ℝ (fderiv ℝ f) x (b i) (b i))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)
    _ ≤ D2 * (∑ i, ‖fderiv ℝ f x (b i)‖ ^ 2) +
        D1 * (C * ∑ i, ‖fderiv ℝ f x (b i)‖ ^ 2) := by
      apply add_le_add
      · simpa only [Finset.mul_sum] using Finset.sum_le_sum (fun i _ => hquad i)
      · exact ((fderiv ℝ H (f x)).le_opNorm _).trans
          (mul_le_mul hfirst hgrowth (norm_nonneg _) hD1)
    _ = (D2 + D1 * C) * ∑ i, ‖fderiv ℝ f x (b i)‖ ^ 2 := by ring
    _ ≤ (D2 + D1 * C) * (L ^ 2 * ∑ i, ‖fderiv ℝ (H ∘ f) x (b i)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left henergy (add_nonneg hD2 (mul_nonneg hD1 hC))
    _ = _ := by ring

end PoincareConjecture
