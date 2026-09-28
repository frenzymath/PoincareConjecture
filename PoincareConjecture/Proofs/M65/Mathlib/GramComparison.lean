import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

set_option autoImplicit false

namespace ContinuousLinearMap

theorem gramDet_two_le_of_quadratic_bound {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (g h : E →L[ℝ] E →L[ℝ] ℝ)
    (gsymm : ∀ u v, g u v = g v u) (hsymm : ∀ u v, h u v = h v u)
    (gpos : ∀ u, u ≠ 0 → 0 < g u u) (hnonneg : ∀ u, 0 ≤ h u u)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ u, h u u ≤ C * g u u) (u v : E) :
    h u u * h v v - (h u v) ^ 2 ≤ C ^ 2 * (g u u * g v v - (g u v) ^ 2) := by
  by_cases hu : u = 0
  · simp [hu]
  have hgu := gpos u hu
  let k := g u v / g u u
  let w := v - k • u
  have shear (B : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x) :
      B u u * B v v - (B u v) ^ 2 = B u u * B w w - (B u w) ^ 2 := by
    simp only [w, map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, hsymm v u]
    ring
  have horth : g u w = 0 := by
    simp only [w, map_sub, map_smul, smul_eq_mul, k]
    rw [div_mul_cancel₀ _ hgu.ne', sub_self]
  have hgram : g u u * g w w = g u u * g v v - (g u v) ^ 2 := by
    simpa only [horth, zero_pow two_ne_zero, sub_zero] using (shear g gsymm).symm
  calc
    _ = h u u * h w w - (h u w) ^ 2 := shear h hsymm
    _ ≤ h u u * h w w := sub_le_self _ (sq_nonneg _)
    _ ≤ (C * g u u) * (C * g w w) :=
      mul_le_mul (hbound u) (hbound w) (hnonneg w) (mul_nonneg hC hgu.le)
    _ = C ^ 2 * (g u u * g w w) := by ring
    _ = _ := by rw [hgram]

end ContinuousLinearMap
