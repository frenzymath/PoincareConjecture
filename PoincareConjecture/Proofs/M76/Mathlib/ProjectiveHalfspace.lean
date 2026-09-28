import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring










set_option autoImplicit false

open Set
open scoped BigOperators

namespace LinearMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]



noncomputable def fractionalRadial (L : E →ₗ[ℝ] ℝ) (x : E) : E :=
  (1 + L x)⁻¹ • x



theorem fractionalRadial_neg_denom (L : E →ₗ[ℝ] ℝ) {x : E}
    (hx : 1 + L x ≠ 0) :
    1 + (-L) (L.fractionalRadial x) = (1 + L x)⁻¹ := by
  simp only [fractionalRadial, LinearMap.neg_apply, map_smul, smul_eq_mul]
  field_simp [hx]
  ring



theorem fractionalRadial_neg_apply (L : E →ₗ[ℝ] ℝ) {x : E}
    (hx : 1 + L x ≠ 0) : (-L).fractionalRadial (L.fractionalRadial x) = x := by
  change (1 + (-L) (L.fractionalRadial x))⁻¹ • L.fractionalRadial x = x
  rw [L.fractionalRadial_neg_denom hx]
  simp only [inv_inv, fractionalRadial, smul_smul, mul_inv_cancel₀ hx, one_smul]



theorem fractionalRadial_injOn (L : E →ₗ[ℝ] ℝ) :
    InjOn L.fractionalRadial {x | 1 + L x ≠ 0} := by
  intro x hx y hy he
  calc
    x = (-L).fractionalRadial (L.fractionalRadial x) :=
      (L.fractionalRadial_neg_apply hx).symm
    _ = (-L).fractionalRadial (L.fractionalRadial y) := congrArg _ he
    _ = y := L.fractionalRadial_neg_apply hy




theorem fractionalRadial_affineIndependent (L : E →ₗ[ℝ] ℝ)
    {ι : Type*} {p : ι → E} (hp : AffineIndependent ℝ p)
    (hd : ∀ i, 1 + L (p i) ≠ 0) :
    AffineIndependent ℝ (L.fractionalRadial ∘ p) := by
  classical
  apply affineIndependent_iff.mpr
  intro s w hw hwv
  have hv : ∑ i ∈ s, (w i / (1 + L (p i))) • p i = 0 := by
    simpa only [Function.comp_apply, fractionalRadial, smul_smul, div_eq_mul_inv] using hwv
  have hL : ∑ i ∈ s, (w i / (1 + L (p i))) * L (p i) = 0 := by
    simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using congrArg L hv
  have hsum : ∑ i ∈ s, w i / (1 + L (p i)) = 0 := by
    have he : (∑ i ∈ s, w i / (1 + L (p i))) +
        (∑ i ∈ s, w i / (1 + L (p i)) * L (p i)) = ∑ i ∈ s, w i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hd i]
    simpa only [hL, hw, add_zero] using he
  intro i hi
  have he := hp.eq_zero_of_sum_eq_zero hsum hv i hi
  exact (div_eq_zero_iff.mp he).resolve_right (hd i)

end LinearMap
