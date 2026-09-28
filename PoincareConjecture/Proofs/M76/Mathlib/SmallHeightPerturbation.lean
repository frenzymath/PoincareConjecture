import PoincareConjecture.Proofs.M76.Mathlib.UniformConvexPLLipschitz










set_option autoImplicit false

open Set Geometry
open scoped NNReal




theorem LipschitzOnWith.strictMonoOn_id_add_mul {f : ℝ → ℝ} {s : Set ℝ}
    {L : ℝ≥0} (hf : LipschitzOnWith L f s) {ε : ℝ} (hε : |ε| * (L : ℝ) < 1) :
    StrictMonoOn (fun t => t + ε * f t) s := by
  intro u hu v hv huv
  have hd : |f v - f u| ≤ (L : ℝ) * (v - u) := by
    have h := hf.dist_le_mul v hv u hu
    simpa only [Real.dist_eq, abs_of_pos (sub_pos.mpr huv)] using h
  have he : |ε * (f v - f u)| ≤ (|ε| * (L : ℝ)) * (v - u) := by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hd (abs_nonneg ε)
  have hlower := (abs_le.mp he).1
  have hstrict := mul_lt_mul_of_pos_right hε (sub_pos.mpr huv)
  nlinarith

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem FinitePiecewiseAffineOn.exists_strictMonoOn_vertical_perturbation
    {g : E × ℝ → ℝ} {B : Set E} {α β : ℝ}
    (hg : FinitePiecewiseAffineOn g (B ×ˢ Icc α β)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ x ∈ B,
      StrictMonoOn (fun t => t + ε * g (x, t)) (Icc α β) := by
  obtain ⟨L, hL⟩ := hg.exists_uniform_vertical_lipschitzOnWith
  let δ : ℝ := 1 / ((L : ℝ) + 1)
  have hden : 0 < (L : ℝ) + 1 := by positivity
  refine ⟨δ, one_div_pos.mpr hden, fun ε hε x hx => (hL x hx).strictMonoOn_id_add_mul ?_⟩
  have hsmall : |ε| * ((L : ℝ) + 1) < 1 := (lt_div_iff₀ hden).mp hε
  nlinarith [abs_nonneg ε]

end Geometry
