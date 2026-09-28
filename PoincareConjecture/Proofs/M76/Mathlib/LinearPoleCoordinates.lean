import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

namespace ContinuousLinearEquiv

theorem exists_apply_eq_one {ι : Type*} [Finite ι]
    {v : ι → ℝ} (hv : v ≠ 0) :
    ∃ e : (ι → ℝ) ≃L[ℝ] (ι → ℝ), e v = fun _ => 1 := by
  let := Fintype.ofFinite ι
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  change v i ≠ 0 at hi
  let w : ι → ℝ := fun j => 1 - v j
  let f : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    LinearMap.id + ((v i)⁻¹ • LinearMap.proj i).smulRight w
  let g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    LinearMap.id - (LinearMap.proj i).smulRight w
  have hf (y : ι → ℝ) (j : ι) : f y j = y j + (v i)⁻¹ * y i * (1 - v j) := rfl
  have hg (z : ι → ℝ) (j : ι) : g z j = z j - z i * (1 - v j) := rfl
  let e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
    { f with
      invFun := g
      left_inv := by
        intro y
        funext j
        change g (f y) j = y j
        simp only [hg, hf]
        field_simp [hi]
        ring
      right_inv := by
        intro z
        funext j
        change f (g z) j = z j
        simp only [hf, hg]
        field_simp [hi]
        ring }
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  funext j
  change f v j = 1
  rw [hf, inv_mul_cancel₀ hi, one_mul]
  ring

end ContinuousLinearEquiv
