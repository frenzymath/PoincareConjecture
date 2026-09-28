import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Curve.Velocity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Energy.Length


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Bundle
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem continuousOn_speed_of_contMDiffOn (g : RiemannianMetric n M)
    {γ : ℝ → M} {I : Set ℝ} (hI : IsOpen I)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I) :
    ContinuousOn (fun u => g.tangentNorm (γ u)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1)) I := by
  intro u hu
  have hγu := (hγ u hu).contMDiffAt (hI.mem_nhds hu)
  have hv := (Poincare.Manifold.contMDiffOn_velocity_lift hI hγ u hu).contMDiffAt
    (hI.mem_nhds hu)
  have h := ((g.contMDiff (γ u)).comp u hγu).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := fun _ : M => ℝ) hv hv
  have hh := (contMDiffAt_totalSpace.mp h).2
  exact Real.continuous_sqrt.continuousAt.comp_continuousWithinAt
    hh.continuousAt.continuousWithinAt


theorem toReal_edist_le_integral_speed (g : RiemannianMetric n M)
    {γ : ℝ → M} {I : Set ℝ} {a b : ℝ}
    (hab : a ≤ b) (hI : IsOpen I) (hsub : Icc a b ⊆ I)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I) :
    (g.edist (γ a) (γ b)).toReal ≤ ∫ u in a..b,
      g.tangentNorm (γ u) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1) := by
  have h := g.edist_le_ofReal_integral_speed hab ((hγ.mono hsub).of_le (by simp))
    ((g.continuousOn_speed_of_contMDiffOn hI hγ).mono hsub)
  have hnonneg : 0 ≤ ∫ u in a..b,
      g.tangentNorm (γ u) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1) :=
    intervalIntegral.integral_nonneg hab (fun _ _ => Real.sqrt_nonneg _)
  simpa only [ENNReal.toReal_ofReal hnonneg] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h

end PoincareConjecture.RiemannianMetric
