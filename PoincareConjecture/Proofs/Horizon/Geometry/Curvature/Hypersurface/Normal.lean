import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional









set_option autoImplicit false
open scoped InnerProductSpace

namespace Poincare.Geometry.Curvature.Hypersurface

theorem normal_eq_inner_smul_of_codim_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : Submodule ℝ E)
    (hdim : Module.finrank ℝ T + 1 = Module.finrank ℝ E)
    (N : E) (hN : ⟪N, N⟫_ℝ = 1) (hNT : N ∈ Tᗮ)
    (w : E) (hw : w ∈ Tᗮ) : w = ⟪w, N⟫_ℝ • N := by
  have hN0 : N ≠ 0 := by
    intro hz
    simp [hz] at hN
  have hd : Module.finrank ℝ Tᗮ = 1 :=
    Submodule.finrank_add_finrank_orthogonal' hdim
  have hspan : Tᗮ = ℝ ∙ N :=
    eq_span_singleton_of_mem_of_finrank_eq_one hd hNT hN0
  rw [hspan, Submodule.mem_span_singleton] at hw
  obtain ⟨a, rfl⟩ := hw
  simp only [real_inner_smul_left, hN, mul_one]

theorem inner_normals_eq_mul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : Submodule ℝ E)
    (hdim : Module.finrank ℝ T + 1 = Module.finrank ℝ E)
    (N : E) (hN : ⟪N, N⟫_ℝ = 1) (hNT : N ∈ Tᗮ)
    (v w : E) (hw : w ∈ Tᗮ) :
    ⟪v, w⟫_ℝ = ⟪v, N⟫_ℝ * ⟪w, N⟫_ℝ := by
  conv_lhs => rw [normal_eq_inner_smul_of_codim_one T hdim N hN hNT w hw]
  simp [real_inner_smul_right, mul_comm]

end Poincare.Geometry.Curvature.Hypersurface
