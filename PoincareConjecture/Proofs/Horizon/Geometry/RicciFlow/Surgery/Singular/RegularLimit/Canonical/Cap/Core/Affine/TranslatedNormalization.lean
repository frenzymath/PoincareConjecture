import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Affine.Translation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.ModelComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RoundCylinderTranslation

theorem close_scaled_pullback_of_full_domain {ε δ c bound : ℝ}
    (hε : 0 < ε) (hεδ : 2 * ε ≤ δ) (s : ℝ)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderTensorSmoothOn ε B)
    (hjet : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
      roundCylinderJetErrorSquared 0 B ⌊(2 * ε)⁻¹⌋₊ z ≤ bound)
    (hsub : MapsTo (fun t : ℝ => t + s)
      (Ioo (-δ⁻¹) δ⁻¹) (Ioo (-ε⁻¹) ε⁻¹))
    (hbudget : 2 * c ^ 2 * bound + 6 * (c - 1) ^ 2 < δ ^ 2) :
    RoundCylinderClose δ 0 (fun z v w => c * pullback s B z v w) := by
  have hsmooth := smoothOn_pullback s hB hsub
  refine ⟨?_, 2 * c ^ 2 * bound + 6 * (c - 1) ^ 2, hbudget, ?_⟩
  · intro q i j
    exact contDiffOn_const.mul (hsmooth q i j)
  · intro z hz
    have hδ : 0 < δ := lt_of_lt_of_le (by positivity : 0 < 2 * ε) hεδ
    have horder : ⌊δ⁻¹⌋₊ ≤ ⌊(2 * ε)⁻¹⌋₊ :=
      Nat.floor_mono ((inv_le_inv₀ hδ (by positivity)).2 hεδ)
    have hold : roundCylinderJetErrorSquared 0 (pullback s B) ⌊δ⁻¹⌋₊ z ≤ bound := by
      rw [jetErrorSquared_pullback]
      exact (DeepHorn.evolvingCylinderJetErrorSquared_mono (by norm_num)
        B (space s z) horder).trans (hjet _ (hsub hz))
    have hscale := SingularRegularLimit.cylinder_scaled_jetError_le_explicit
      (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) < 1) hsmooth c ⌊δ⁻¹⌋₊ z hz
    simp only [sub_zero, mul_one, div_one] at hscale
    have hmul := mul_le_mul_of_nonneg_left hold (show 0 ≤ 2 * c ^ 2 by positivity)
    exact hscale.trans (by nlinarith)

theorem close_scaled_pullback_of_linear_error {ε δ c A : ℝ}
    (hε : 0 < ε) (hεδ : 2 * ε ≤ δ) (hc : 0 ≤ c) (hcmax : c ≤ 2)
    (hA : 0 ≤ A) (hcerror : |c - 1| ≤ A * ε) (s : ℝ)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderTensorSmoothOn ε B)
    (hjet : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
      roundCylinderJetErrorSquared 0 B ⌊(2 * ε)⁻¹⌋₊ z ≤ 4 * ε ^ 2)
    (hsub : MapsTo (fun t : ℝ => t + s)
      (Ioo (-δ⁻¹) δ⁻¹) (Ioo (-ε⁻¹) ε⁻¹))
    (hbudget : (32 + 6 * A ^ 2) * ε ^ 2 < δ ^ 2) :
    RoundCylinderClose δ 0 (fun z v w => c * pullback s B z v w) := by
  apply close_scaled_pullback_of_full_domain hε hεδ s hB hjet hsub
  have hc2 : c ^ 2 ≤ 4 := by nlinarith
  have herr : (c - 1) ^ 2 ≤ A ^ 2 * ε ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (c - 1)) (mul_nonneg hA hε.le)).2 hcerror
    simpa only [sq_abs, mul_pow] using hh
  have hh := mul_le_mul_of_nonneg_right hc2 (sq_nonneg ε)
  nlinarith

end PoincareConjecture.RoundCylinderTranslation
