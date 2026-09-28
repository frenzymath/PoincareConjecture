import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.JetBounds

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.Proofs.M28.FiniteHessian

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem HasUniformJetBoundsAt.smul_family {n : ℕ} {f : ι → E → F} {x : ι → E}
    (h : HasUniformJetBoundsAt n f x)
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i)) (c : ι → ℝ)
    {B : ℝ} (hc : ∀ i, ‖c i‖ ≤ B) :
    HasUniformJetBoundsAt n (fun i y => c i • f i y) x := by
  obtain ⟨C, _hC0, hC⟩ := h.bound_all
  intro m hm
  refine ⟨max B 0 * C, fun i => ?_⟩
  rw [iteratedFDeriv_const_smul_apply' ((hf i).of_le (by exact_mod_cast le_top)), norm_smul]
  exact mul_le_mul ((hc i).trans (le_max_left _ _)) (hC m hm i)
    (norm_nonneg _) (le_max_right _ _)

theorem HasUniformJetBoundsAt.exists_scalar_error_tail
    {n : ℕ} {f : ι → E → F} {x : ι → E} (h : HasUniformJetBoundsAt n f x)
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    {c : ℕ → ℝ} {a : ℝ} (hc : Tendsto c atTop (𝓝 a)) (index : ι → ℕ) :
    ∀ rho : ℝ, 0 < rho → ∃ K : ℕ, ∀ i, K ≤ index i → ∀ m ≤ n,
      ‖iteratedFDeriv ℝ m (fun y => (c (index i) - a) • f i y) (x i)‖ ≤ rho := by
  obtain ⟨B, _hB0, hB⟩ := h.bound_all
  have hmax : 0 < max B 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  intro rho hrho
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hc (rho / max B 1) (div_pos hrho hmax)
  refine ⟨K, ?_⟩
  intro i hi m hm
  have hsmall : |c (index i) - a| < rho / max B 1 := by
    simpa only [Real.dist_eq] using hK (index i) hi
  rw [iteratedFDeriv_const_smul_apply' ((hf i).of_le (by exact_mod_cast le_top)),
    norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ (rho / max B 1) * max B 1 :=
      mul_le_mul hsmall.le ((hB m hm i).trans (le_max_left _ _))
        (norm_nonneg _) (div_pos hrho hmax).le
    _ = rho := div_mul_cancel₀ rho hmax.ne'

end PoincareConjecture.Proofs.M28.FiniteHessian
