import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.CollarDensity
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AnnularPolarBound
import PoincareConjecture.Proofs.M58.Cor18_28_AreaBound

set_option autoImplicit false

open Set MeasureTheory Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

open Proofs.M58

theorem m60LoopCollar_area_le
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (C : ℝ × (M × M) → M)
    (γ₀ γ₁ : C1FreeLoopSpace (M := M))
    (hC : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C (s, γ₁ z, γ₀ z))
    {A B H : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (htime : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      g.tangentNorm (C (s, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t))
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
          (s, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t) (1, 0, 0)) ≤ A)
    (hfirst : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ v : TangentSpace (𝓡 3) (periodicFreeLoop γ₁ t),
      g.tangentNorm (C (s, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t))
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
          (s, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t) (0, v, 0)) ≤
            B * g.tangentNorm (periodicFreeLoop γ₁ t) v)
    (hlast : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ v : TangentSpace (𝓡 3) (periodicFreeLoop γ₀ t),
      g.tangentNorm (C (s, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t))
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
          (s, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t) (0, 0, v)) ≤
            B * g.tangentNorm (periodicFreeLoop γ₀ t) v)
    (hprofile : ∀ r ∈ Icc (0 : ℝ) 1, |deriv diskTimeProfile r| ≤ H) :
    (∫ z in (closedBall (0 : LoopPlane) (1 / 2 : ℝ))ᶜ ∩ loopDiskSet,
      m60AreaDensity g (m60LoopCollar C γ₀ γ₁) z) ≤
        H * A * B * (freeLoopLength g γ₁ + freeLoopLength g γ₀) := by
  let ell := fun t =>
    g.tangentNorm (periodicFreeLoop γ₁ t) (curveVelocity (periodicFreeLoop γ₁) t) +
    g.tangentNorm (periodicFreeLoop γ₀ t) (curveVelocity (periodicFreeLoop γ₀) t)
  have hi (γ : C1FreeLoopSpace (M := M)) : IntegrableOn (fun t =>
      g.tangentNorm (periodicFreeLoop γ t) (curveVelocity (periodicFreeLoop γ) t))
      (Ioo (-Real.pi) Real.pi) volume :=
    ((continuous_freeLoopSpeed g γ).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioo_subset_Icc_self
  have hell : (∫ t in Ioo (-Real.pi) Real.pi, ell t) =
      freeLoopLength g γ₁ + freeLoopLength g γ₀ := by
    rw [show ell = (fun t => g.tangentNorm (periodicFreeLoop γ₁ t)
      (curveVelocity (periodicFreeLoop γ₁) t) + g.tangentNorm (periodicFreeLoop γ₀ t)
      (curveVelocity (periodicFreeLoop γ₀) t)) from rfl,
      integral_add (hi γ₁) (hi γ₀), integral_polar_freeLoopSpeed, integral_polar_freeLoopSpeed]
  rw [← hell]
  apply m60AreaIntegral_annulus_le_polar g _ (mul_nonneg (mul_nonneg hH hA) hB) ell
    ((continuous_freeLoopSpeed g γ₁).add (continuous_freeLoopSpeed g γ₀))
    (fun _ => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  intro r hr t _
  have hr0 : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hχ : 1 - diskTimeProfile r ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨h0, h1⟩ := diskTimeProfile_mem_Icc r
    exact ⟨sub_nonneg.mpr h1, by linarith⟩
  have hz : r • angularPoint t ≠ 0 := norm_pos_iff.mp (by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, norm_angularPoint, mul_one]
    exact hr0)
  let q : LoopCircle := ⟨angularPoint t, norm_angularPoint t⟩
  have hq (γ : C1FreeLoopSpace (M := M)) : periodicFreeLoop γ t = γ q := γ.boundary q
  have hc := hC _ hχ q
  rw [← hq γ₁, ← hq γ₀] at hc
  exact m60LoopCollar_polar_density_le g C γ₀ γ₁ hr0 t hA hH
    ((m60LoopCollar_contMDiffAt C γ₀ γ₁ hC hz).mdifferentiableAt one_ne_zero)
    (hc.mdifferentiableAt one_ne_zero) (htime _ hχ t) (hfirst _ hχ t) (hlast _ hχ t)
    (hprofile r ⟨hr0.le, hr.2⟩)

end PoincareConjecture
