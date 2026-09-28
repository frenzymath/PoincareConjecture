import PoincareConjecture.Proofs.M36.MetricCombination
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal
open MeasureTheory

namespace PoincareConjecture.M36

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def metricPathSpeed (g : RiemannianMetric n M) (gamma : ℝ → M)
    (t : ℝ) : ℝ :=
  g.tangentNorm (gamma t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma t 1)

theorem metricPathSpeed_nonneg (g : RiemannianMetric n M) (gamma : ℝ → M) (t : ℝ) :
    0 ≤ metricPathSpeed g gamma t := Real.sqrt_nonneg _

theorem metricPathSpeed_continuous (g : RiemannianMetric n M) {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma) :
    Continuous (metricPathSpeed g gamma) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  have hunit : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞ (fun t : ℝ =>
      (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hv : Continuous (fun t : ℝ =>
      (⟨gamma t, mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma t 1⟩ : TangentBundle (𝓡 n) M)) :=
    (hgamma.continuous_tangentMap le_rfl).comp hunit.continuous
  exact (hv.inner_bundle hv).sqrt

theorem pathELength_eq_integral_speed (g : RiemannianMetric n M) {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma) {a b : ℝ} (hab : a ≤ b) :
    g.pathELength gamma a b = ENNReal.ofReal (∫ t in a..b, metricPathSpeed g gamma t) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.pathELength (𝓡 n) gamma a b = _
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  calc
    _ = ∫⁻ t in Set.Icc a b, ENNReal.ofReal (metricPathSpeed g gamma t) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t _
      dsimp only
      erw [← ofReal_norm, norm_eq_sqrt_real_inner]
      rfl
    _ = ENNReal.ofReal (∫ t in Set.Icc a b, metricPathSpeed g gamma t) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal
        (metricPathSpeed_continuous g hgamma).integrableOn_Icc
        (Filter.Eventually.of_forall (metricPathSpeed_nonneg g gamma))
    _ = _ := by
      rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

end PoincareConjecture.M36
