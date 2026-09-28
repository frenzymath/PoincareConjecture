import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.CollarPolarDerivatives
import PoincareConjecture.Proofs.M58.Cor18_28_PolarDensity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

open Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



theorem m60Contraction_spatial_bound (g : RiemannianMetric 3 M)
    (C : ℝ × (M × M) → M) (x : ℝ × (M × M)) (B : ℝ)
    (hp : ∀ v : TangentSpace (𝓡 3) x.2.1,
      g.tangentNorm (C x)
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C x (0, v, 0)) ≤
          B * g.tangentNorm x.2.1 v)
    (hq : ∀ v : TangentSpace (𝓡 3) x.2.2,
      g.tangentNorm (C x)
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C x (0, 0, v)) ≤
          B * g.tangentNorm x.2.2 v)
    (v : TangentSpace (𝓡 3) x.2.1) (w : TangentSpace (𝓡 3) x.2.2) :
    g.tangentNorm (C x)
      (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C x (0, v, w)) ≤
        B * (g.tangentNorm x.2.1 v + g.tangentNorm x.2.2 w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let D := mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C x
  have hsplit : ((0, v, w) : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) x) =
      (0, v, 0) + (0, 0, w) := by
    change ((0 : ℝ), v, w) = (0 + 0, v + 0, 0 + w)
    simp
  change ‖D (0, v, w)‖ ≤ B * (‖v‖ + ‖w‖)
  erw [hsplit, map_add]
  apply (norm_add_le _ _).trans
  rw [mul_add]
  exact add_le_add (hp v) (hq w)




theorem m60LoopCollar_polar_density_le (g : RiemannianMetric 3 M)
    (C : ℝ × (M × M) → M) (γ₀ γ₁ : C1FreeLoopSpace (M := M))
    {r : ℝ} (hr : 0 < r) (t : ℝ) {A B H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hF : MDifferentiableAt (𝓡 2) (𝓡 3) (m60LoopCollar C γ₀ γ₁) (r • angularPoint t))
    (hC : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
      (1 - diskTimeProfile r, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t))
    (htime : g.tangentNorm (C (1 - diskTimeProfile r, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t))
      (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
        (1 - diskTimeProfile r, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t) (1, 0, 0)) ≤ A)
    (hfirst : ∀ v : TangentSpace (𝓡 3) (periodicFreeLoop γ₁ t),
      g.tangentNorm (C (1 - diskTimeProfile r, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t))
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
          (1 - diskTimeProfile r, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t) (0, v, 0)) ≤
            B * g.tangentNorm (periodicFreeLoop γ₁ t) v)
    (hlast : ∀ v : TangentSpace (𝓡 3) (periodicFreeLoop γ₀ t),
      g.tangentNorm (C (1 - diskTimeProfile r, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t))
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
          (1 - diskTimeProfile r, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t) (0, 0, v)) ≤
            B * g.tangentNorm (periodicFreeLoop γ₀ t) v)
    (hprofile : |deriv diskTimeProfile r| ≤ H) :
    r * m60AreaDensity g (m60LoopCollar C γ₀ γ₁) (r • angularPoint t) ≤
      H * A * B * (g.tangentNorm (periodicFreeLoop γ₁ t) (curveVelocity (periodicFreeLoop γ₁) t) +
        g.tangentNorm (periodicFreeLoop γ₀ t) (curveVelocity (periodicFreeLoop γ₀) t)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let D := mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
    (1 - diskTimeProfile r, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t)
  have h := mul_parametrizedAreaDensity_le_polar g (m60LoopCollar C γ₀ γ₁)
    (r • angularPoint t) hr.le t
  erw [m60LoopCollar_mfderiv_radial C γ₀ γ₁ hr t hF hC,
    m60LoopCollar_mfderiv_angular C γ₀ γ₁ hr t hF hC,
    m60LoopCollar_polar C γ₀ γ₁ hr t] at h
  change r * m60AreaDensity g (m60LoopCollar C γ₀ γ₁) (r • angularPoint t) ≤
    ‖-deriv diskTimeProfile r • D (1, 0, 0)‖ *
      ‖D (0, curveVelocity (periodicFreeLoop γ₁) t, curveVelocity (periodicFreeLoop γ₀) t)‖ at h
  rw [norm_smul, Real.norm_eq_abs, abs_neg] at h
  have hang := m60Contraction_spatial_bound g C _ B hfirst hlast
    (curveVelocity (periodicFreeLoop γ₁) t) (curveVelocity (periodicFreeLoop γ₀) t)
  calc
    _ ≤ (H * A) * (B * (g.tangentNorm (periodicFreeLoop γ₁ t)
        (curveVelocity (periodicFreeLoop γ₁) t) + g.tangentNorm (periodicFreeLoop γ₀ t)
        (curveVelocity (periodicFreeLoop γ₀) t))) := h.trans
      (mul_le_mul (mul_le_mul hprofile htime (norm_nonneg _) hH) hang
        (norm_nonneg _) (mul_nonneg hH hA))
    _ = _ := by ring

end PoincareConjecture
